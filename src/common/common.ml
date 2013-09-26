open Printf

(** Common Types and Functions *)

(*
 * Type Definitions
 *)

type reg = EAX | EBX | ECX | EDX | ESI | EDI | EBP | ESP

type op = ADD | SUB | MUL | DIV | XOR | OR | AND

type gadget =
    | LoadConst of reg * int                (** reg, stack offset *)
    | CopyReg of reg * reg                  (** dst reg = src reg *)
    | BinOp of reg * reg * op * reg         (** dst reg = src1 OP src2 *)
    | ReadMem of reg * reg * int32          (** dst = [addr_reg + offset] *)
    | WriteMem of reg * int32 * reg         (** [addr_reg + offset] = src *)
    | ReadMemOp of reg * op * reg * int32   (** dst OP= [addr_reg + offset] *)
    | WriteMemOp of reg * int32 * op * reg  (** [addr_reg + offset] OP= src_reg *)
    | Lahf
    | OpEsp of op * reg * int               (** esp = esp op reg, where op=+/-, sf = stack_fix *)

(* (offset_start, offset_end) *)
type fmeta = FileMeta of int * int

(* (gadget, file meta, modified registers, stack_fix) *)
type gmeta = GMeta of gadget * fmeta * reg list * int

(* (filename, (data section start, data section end), gadget list)
    type used for marshaling candidates for verification *)
type gcontainer = GContainer of string * (int * int) * gmeta list

type candidate = Cand of (int * int) * Ast.stmt list


(*
 * Definitions
 *)
let rEGS = [EAX; EBX; ECX; EDX; ESI; EDI; EBP; ESP;]

let rEGS_NO_ESP = [EAX; EBX; ECX; EDX; ESI; EDI; EBP;]

let gLOBAL_MEM = "mem:?u32"
let sTACK_BASE = 0x0A1D5000
let tOO_BIG = 0x1000
let eFLAGS = "EFLAGS:u32"
let eFLAGS_MASK = 0xd5


(*
 * Dump functions
 *)
let dump_reg r =
    match r with
    | EAX -> "eax"
    | EBX -> "ebx"
    | ECX -> "ecx"
    | EDX -> "edx"
    | ESI -> "esi"
    | EDI -> "edi"
    | EBP -> "ebp"
    | ESP -> "esp"

let dump_regs regs =
    let l = List.map (fun r->dump_reg r) regs in
    let f acc s = acc^";"^s in
    let s = List.fold_left f "" l in
    sprintf "[%s]" s

let dump_op op =
    match op with
    | ADD -> "+"
    | SUB -> "-"
    | MUL -> "*"
    | DIV -> "/"
    | XOR -> "^"
    | AND -> "&"
    | OR  -> "|"

let dump_filemeta fm =
    let FileMeta(off_s, off_e) = fm in
    let s = sprintf "(s: 0x%x, e: 0x%x)" off_s off_e in
    s

let dump_gadget g =
    match g with
    | LoadConst(r, off) ->
        sprintf "LoadConst(%s, 0x%x)" (dump_reg r) off

    | CopyReg(r1, r2) ->
        sprintf "CopyReg(%s, %s)" (dump_reg r1) (dump_reg r2)

    | BinOp(r_dst,r1,op,r2) ->
        sprintf "BinOp(%s, %s, %s, %s)" (dump_reg r_dst) (dump_reg r1) (dump_op op) (dump_reg r2)

    | ReadMem(r_dst, r_addr, off) ->
        sprintf "ReadMem(%s = [%s+0x%lx])" (dump_reg r_dst) (dump_reg r_addr) off

    | WriteMem(r_addr, off, r_src) ->
        sprintf "WriteMem([%s+0x%lx] = %s)" (dump_reg r_addr) off (dump_reg r_src)

    | ReadMemOp(r_dst, op, r_addr, off) ->
        sprintf "ReadMemOp(%s %s= [%s+0x%lx])" (dump_reg r_dst) (dump_op op) (dump_reg r_addr) off

    | WriteMemOp(r_addr, off, op, r_src) ->
        sprintf "WriteMemOp([%s+0x%lx] %s= %s)" (dump_reg r_addr) off (dump_op op) (dump_reg r_src)

    | OpEsp(op, r, sf) ->
        sprintf "OpEsp(%s, %s, %d)" (dump_op op) (dump_reg r) sf

    | Lahf ->
        "Lahf"

let dump_gmeta gm =
    match gm with
    | GMeta(gadget, fm, modified_regs, stack_fix) ->
        let gs = dump_gadget gadget in
        let fs = dump_filemeta fm in
        let modified = sprintf "modified: %s" (dump_regs modified_regs) in
        let sf = sprintf "stack_fix: %d" stack_fix in
        let s = sprintf "%s, %s, %s, %s" gs fs modified sf in
        s

let dump_container c =
    let GContainer(fn, (data_s, data_e), gm_list) = c in
    let fs =
        sprintf "### fn: %s, data_s: 0x%08x, data_e: 0x%08x" fn data_s data_e in
    let l = List.map dump_gmeta gm_list in
    let l = fs::l in
    (* string concat would be O(n^2) *)
    let glue acc s = Buffer.add_string acc s; Buffer.add_string acc "\n"; acc in
    let b = List.fold_left glue (Buffer.create 32) l in
    b

let dump_int_list l =
    let f acc x =
        let s = string_of_int x in
        acc^";"^s
    in
    List.fold_left f "" l


(*
 * Auxiliary Functions
 *)
let reg_to_str reg =
    match reg with
    | EAX -> "EAX"
    | EBX -> "EBX"
    | ECX -> "ECX"
    | EDX -> "EDX"
    | ESI -> "ESI"
    | EDI -> "EDI"
    | EBP -> "EBP"
    | ESP -> "ESP"

let unwrap_ast_var v =
    match v with
    | Ast.Var(v) -> v
    | _ -> assert false

let str_to_var s =
    let av,_ = Parser.exp_from_string s in
    let v = unwrap_ast_var av in
    v

(* EAX -> var("R_EAX") *)
(* Retorna una variable de tipo Ast.var, con nombre "R_" + nombre registro. *)
let reg_var reg =
    let reg_s = reg_to_str reg in
    let reg_s = "R_"^reg_s in
    let v = str_to_var reg_s in
    v

let uniq eq l =
    let rec aux l last uni dupes =
        match l with
        | hd::tl ->
            if eq hd last = 0 then
                aux tl last uni (hd::dupes)
            else
                aux tl hd (hd::uni) dupes
        | [] -> uni, dupes
    in
    match l with
    | [] -> l,l
    | hd::[] -> l, []
    | hd::tl -> aux tl hd [hd] []

let unique eq l =
    let u, _ = uniq eq l in
    u

let nonunique eq l =
    let _, nu = uniq eq l in
    nu

let generic_unique l =
    let l = List.sort compare l in
    unique compare l

let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

let file_exc filename e =
    Format.printf "Cannot open file \"%s\": %s\n" filename (Printexc.to_string e);
    assert false

let open_file fn fopen =
    try
        let co = fopen fn in
        co
    with Sys_error _ as e ->
        file_exc fn e

let open_file_in fn = open_file fn open_in_bin

let open_file_out fn = open_file fn open_out_bin

let write_str_to_file filename str =
    let co = open_file_out filename in
    (* let co = Format.formatter_of_out_channel co in*)
    output_string co str;
    close_out co

let read_file fn =
    let ic = open_file_in fn in
    let n = in_channel_length ic in
    let s = String.create n in
    really_input ic s 0 n;
    close_in ic;
    (s)

let marshal_to_file fn thing =
    let co = open_file_out fn in
    Marshal.to_channel co thing []

let unmarshal_from_file fn =
    let ic = open_file_in fn in
    let obj = Marshal.from_channel ic in
    obj

(* this assumes that RET is the last instruction *)
let drop_last stmts =
    let stmts = List.rev (List.tl (List.rev stmts)) in
    stmts

let find_all p l =
    let f acc x = if p x then (x::acc) else acc in
    List.fold_left f [] l

let generic_dumper f_dump l =
    let f _ x = Printf.printf "%s;" (f_dump x) in
    let _ = List.fold_left f () l in
    ()

let get_gadgets gmetas =
    let strip acc gm =
        let GMeta(g,_,_,_) = gm in
        g::acc
    in
    let gadgets = List.fold_left strip [] gmetas in
    gadgets

let trd (_,_,x) = x

let i32 = Int32.of_int

let fun_label id = "function_"^id

let fun_local_label fun_id id = "local_"^fun_id^"_"^id
