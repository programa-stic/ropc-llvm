open Printf

open Analysis
open Common
open RegSets
open RopCodeWriter
open RoplAst
open RoplAstRewriter
open SsaForm
open SsaFormPrinter

(** Rop Compiler Tool *)

let hARDCODED_PRINTF = 0x080484a0
let sTACK_VAR_OFF = 0
let fRAME_VAR_OFF = 4
let dATA_OFF = 8 (* start writing tables here *)

let nO_NAME_LABEL = "@@"
let gLOBAL_END_LABEL = "global_end"

(*
 * Auxiliary Functions
 *)
let add_comments f_comment new_instrs prefix instr =
    let comments =
        if f_comment instr then
            let s = dump_instr instr in
            [Comment(prefix^s)]
        else
            []
    in
    comments @ new_instrs

let is_lbl_or_comment instr =
    match instr with
    | Lbl(_) | Comment(_) -> true
    | _ -> false

let print_errors errors =
    let errors = RoplAst.dump_errors errors in
    let rec aux errors =
        match errors with
        | hd::tl ->
            let hd = "ERROR. "^hd^"\n" in
            let _ = printf "%s" hd in
            aux tl
        | [] -> ()
    in
    aux errors

(*
 * Dump Functions
 *)
let dump_possible gadgets stack_ptr frame_ptr instrs =
    let implement = make_implement stack_ptr frame_ptr in
    let p_by_arg, p_by_pos = make_possible_regs_funs gadgets implement in
    let f _ instr =
        let _ = Printf.printf "%s - " (dump_instr instr) in
        let args = arg_dumper instr in
        let per_arg _ arg =
            let _ = Printf.printf "| %s: " (dump_sreg arg) in
            let set = p_by_arg instr arg in
            let regs = RegSet.elements set in
            let _ = Common.generic_dumper (fun r -> Common.dump_reg r) regs in
            ()
        in
        let _ = List.fold_left per_arg () args in
        Printf.printf "%s" "\n"
    in
    let _ = List.fold_left f () instrs in
    ()

(* dump 'compiled' program *)
let dump_instrs cl =
    let print i =
        let s = dump_instr i in
        Printf.printf "%s\n" s in
    let _ = List.map print cl in
    ()

let dump_pairs pairs =
    let _ = print_endline "dump pairs ~~~~~~~~~~~~~" in
    let pr acc (instr,gmeta) =
        let GMeta(_,_,_,stack_fix) = gmeta in
        let (off, sep) =
            if is_lbl_or_comment instr then
                acc, " "
            else
                acc+stack_fix, "\t"
        in
        let _ = printf "0x%04x%s%s\n" acc sep (dump_instr instr) in
        off
    in
    (* First RET will add 4 *)
    let _ = List.fold_left pr 4 pairs in
    ()

(* Extract tables and create a stub that writes them to the data section.
 * All AssignTable(id,list) are changed to Assign(id,C), where C is the
 * address in .data section *)
(* AssignTable == AssignTab*)
(* Retorna: (stub, new_prog) donde: *)
(* stub: es una lista de instrucciones que inicializa la sección de datos con
los datos del programa. *)
(* new_prog: es el programa con sus funciones reescritas. *)
let handle_tables data_s prog =
    (* Reescribe los stmts de una función. *)
    (* Retorna (data_end, pairs, func) donde: *)
    (* data_end : es la dir en la pila (sección de datos) a partir de donde se pueden agregar nuevos datos. *)
    (* pairs: es la lista de (dir, dato). *)
    (* func: es la función reescrita. *)
    let per_func data_start func =
        (* let h = Hashtbl.create 8 in *)
        (* Reescribe AssignTab por Assign *)
        (* Retorna una lista (off, pairs, rew) donde *)
        (* off: es la dir en la pila (sección de datos, mejor dicho) a partir de donde se pueden agregar más datos. *)
        (* pairs: es una lista del tipo (offset, lista de enteros que representan los datos). *)
        (* rew: es una lista de stmt donde se encuentran reescritas las stmts originales. *)
        let per_stmt acc stmt =
            let (off, pairs, rew) = acc in
            match stmt with
            | AssignTab(id, l) ->
                let new_stmt = Assign(id, Const(off)) in
                let new_off = off + List.length l in
                new_off,(off,l)::pairs,new_stmt::rew

            | _ -> off,pairs,stmt::rew
        in
        let Fun(fun_id, Args(args), FunBody(stmts)) = func in
        let data_end, pairs, stmts = List.fold_left per_stmt (data_start,[],[]) stmts in
        let stmts = List.rev stmts in
        let func = Fun(fun_id, Args(args), FunBody(stmts)) in
        data_end, pairs, func
    in
    (* Función fold de la función de reescritura. *)
    let per_func_fold (data_start,l_pairs,funs) func =
        let data_end, f_pairs, new_func = per_func data_start func in
        (data_end, f_pairs::l_pairs, new_func::funs)
    in
    let dump_pairs pairs =
        let pr (off, l) =
            let s = dump_int_list l in
            printf "0x%08x,%s\n" off s
        in
        List.map pr pairs
    in
    (* Retorna una lista de instrucciones de store para los datos que hay que
    poner en la sección de datos. *)
    let make_stub pairs =
        let store addr v =
            let r = S(-1) in
            let mov = MovRegConst(r, v) in
            let wm = WriteMConst(addr, r) in
            [mov;wm]
        in
        let chop l n =
            let f (i,a,b) x = if i<n then (i+1,x::a,b) else (i+1,a,x::b) in
            let (_,a,b) = List.fold_left f (0,[],[]) l in
            List.rev a, List.rev b
        in
        let to_int l =
            let f acc x = (acc lsl 8)+x in
            List.fold_left f 0 l
        in
        let make_one off l =
            let rec aux acc off l =
                let pre,suf = chop l 3 in
                match pre with
                | hd::tl ->
                    let v = to_int (List.rev pre) in
                    let s = store off v in
                    aux (s::acc) (off+3) suf
                | [] -> List.flatten (List.rev acc)
            in
            let s = aux [] off l in
            s
        in
        let f acc (off,l) =
            let s = make_one off l in
            s::acc
        in
        let ss = List.fold_left f [] pairs in
        List.flatten (List.rev ss)
    in
    let data_start = data_s+dATA_OFF in
    let Prog(func_list) = prog in
    let (_,l_pairs,funs) = List.fold_left per_func_fold (data_start,[],[]) func_list in
    let funs = List.rev funs in
    let pairs = List.rev (List.flatten l_pairs) in
    let _ = dump_pairs pairs in
    (* Programa con sus funciones reescritas. *)
    let new_prog = Prog(funs) in
    (* Genera los stmts necesarios para guardar los datos del programa en la sección de datos. *)
    let stub = make_stub pairs in
    stub, new_prog

(* concretize symbolic constants *)
(* IN: (instr,gm) pairs
 * OUT: (instr,gm) pairs without MovRegSymb *)
(* Reescribe MovRegSymb por MovRegConst*)
let fix_symblic pairs =
    let get_size gm =
        let GMeta(_,_,_,stack_fix) = gm in
        stack_fix
    in
    let check_lbl label instr = match instr with Lbl(lab) -> label=lab | _ -> false in
    let distance_to_generic f_match pairs =
        let rec aux dist pairs =
            match pairs with
            | (instr,gm)::tl ->
                if f_match instr then
                    (*
                    let _ = Printf.printf "found label %s in: %s\n" label
                    (dump_instr instr) in
                    *)
                    Some(dist)
                else
                    begin
                    (* Ignore gmetas for labels and comments -_-' *)
                    if is_lbl_or_comment instr then
                        aux dist tl
                    else
                        let size = get_size gm in
                        aux (size+dist) tl
                    end
            | [] -> None
        in
        let dist = aux 0 pairs in
        dist
    in
    let distance_to_lbl lbl pairs =
        let f_match = check_lbl lbl in
        let dist = distance_to_generic f_match pairs in
        dist
    in
    let try_both_ways id pre suf =
        let before = distance_to_lbl id pre in
        let after = distance_to_lbl id suf in
        match before,after with
        | Some(_),Some(_) -> failwith ("Found duplicate: "^id)
        | None, None -> failwith ("Can't find label:"^id)
        | Some(n),None -> -n
        | None,Some(n) -> n
    in
    let distance_to_unnamed dir pre suf =
        let sign,chunk =
            match dir with
            | Forward -> 1,suf
            | Backward -> -1,pre
        in
        let dist = distance_to_lbl nO_NAME_LABEL chunk in
        match dist with
        | Some(n) -> sign*n
        | None -> failwith "Unnamed not found"
    in
    let get_distance symb pre suf =
        match symb with
        | Named(id) -> try_both_ways id pre suf
        | Unnamed(dir) -> distance_to_unnamed dir pre suf
    in
    let rec aux pre suf =
        match suf with
        | (MovRegSymb(reg, FromTo(start, fin)),gm)::tl->
            let dstart = get_distance start pre suf in
            let dfin = get_distance fin pre suf in
            let dist = dfin-dstart in
            let _ = printf "FromTo: (%s,%s)->(%d,%d)->%d\n" (dump_symb start) (dump_symb fin) dstart dfin dist in
            let fix = MovRegConst(reg, dist) in
            aux ((fix,gm)::pre) tl
        | hd::tl -> aux (hd::pre) tl
        | [] -> List.rev pre
    in
    aux [] pairs

(* AdvanceStack -> RawHex.
 * to_binary would try to fill the gap before the return address,
 * but we use that space for arguments. *)
(* Reescribe instr AdvanceStack -> RawHex *)
let fix_ext_call_stuff pairs =
    let get_addr gm =
        let GMeta(_, fm, _, _) = gm in
        let FileMeta(off_s, _) = fm in
        off_s
    in
    let set_stack_fix gm sf =
        let GMeta(g,fm,mod_reg,_) = gm in
        GMeta(g,fm,mod_reg,sf)
    in
    let f acc (instr,gmeta) =
        let new_instr =
            match instr with
            | AdvanceStack(n) -> RawHex(get_addr gmeta)
            | _ -> instr
        in
        if new_instr <> instr then
            let cmt = Comment(dump_instr instr) in
            let fake_gm = set_stack_fix gmeta 4 in
            let p1 = (new_instr, fake_gm) in
            let p2 = (cmt, gmeta) in
            p1::p2::acc
        else (instr,gmeta)::acc
    in
    let pairs = List.fold_left f [] pairs in
    List.rev pairs

let write_const_const src_reg addr_reg addr value =
    let m1 = MovRegConst(src_reg, value) in
    let m2 = MovRegConst(addr_reg, addr) in
    let wm1 = WriteM(addr_reg, src_reg) in
    [m1; m2; wm1]

(* Retorna (pre, suf, st_ptr, sf_ptr) donde: *)
(* pre = es el prologo que inicializa la pila *)
(* sub = es una etiqueta que determina el final de la pila. *)
(* st_ptr = puntero al stack. *)
(* sf_ptr = puntero al stack frame. *)
let global_prefix_suffix data_s data_e =
    let stack_top = data_e in
    let stack_frame = stack_top in
    let st_ptr = data_s+sTACK_VAR_OFF in (* global var holding stack_top *)
    let sf_ptr = data_s+fRAME_VAR_OFF in (* -- stack_frame *)
    let addr_reg, src_reg = S(-1), S(-2) in (* HACK *)
    (* Escribe en el tope real de la pila (es decir, dir más baja posible) donde
    está el tope de la pila y donde está el stack frame. *)
    let write_st = write_const_const src_reg addr_reg st_ptr stack_top in
    let write_sf = write_const_const src_reg addr_reg sf_ptr stack_frame in
    let reg = S(-3) in
    let mov = MovRegSymb(reg, FromTo(Named(fun_label "main"), Named(gLOBAL_END_LABEL))) in
    let push = PushReg(reg) in
    let lbl = Lbl(gLOBAL_END_LABEL) in
    let pre = write_st @ write_sf @ [mov; push] in
    let suf = [lbl] in
    pre, suf, st_ptr, sf_ptr

(* Remueve instrucciones superfluas, en este caso Lbl y Comment. *)
let filter_trash pairs =
    let p (i,_) =
        match i with
        | Lbl(_) | Comment(_) -> false
        | _ -> true
    in
    List.filter p pairs

(* FIXME: main has to be at the beginning *)
let compile prog container =
    (* Retorna una lista s_pairs : (instr, gmeta) *)
    let process_func assign_regs instr_lll =
        (* Procesa un stmt. *)
        let per_stmt acc instrs =
            (* list of instructions, set of regs to preserve *)
            let impl =
                try
                    assign_regs instrs SRegSet.empty
                with Not_found ->
                    let _ = dump_instrs instrs in
                    assert false
                in
            impl::acc
        in
        (* Procesa una lista de stmts. *)
        let per_func acc stmts =
            let impl = List.fold_left per_stmt [] stmts in
            let impl = List.rev impl in
            impl::acc
        in
        let impl_lll = List.fold_left per_func [] instr_lll in
        List.rev impl_lll
    in
    (* ??? *)
    let verify_impl impl =
        let p instr = instr_type instr = T0 in
        let ok = List.for_all p impl in
        if not ok then assert false
        else ()
    in

    (* Load data *)
    let GContainer(fn, (data_s, data_e), gmetas) = container in

    (* Retorna (pre, suf, st_ptr, sf_ptr) donde: *)
    let prefix, suffix, stack_ptr, frame_ptr = global_prefix_suffix data_s data_e in

    (* Swap AssignTable with Assign (const).
     * stub stores all tables in .data section *)
    let stub, prog = handle_tables data_s prog in

    (* assign_regs : instrs -> top_preserved -> s_pairs *)
    let assign_regs = make_assign_regs gmetas stack_ptr frame_ptr in

    (* instr list list list.
     * 1st level: list of functions
     * 2nd level: list of (rewritten) stmts
     * 3rd level: instructions *)
    (* instrs_ll : lista de sentencias SSA *)
    let instrs_ll = rewrite_prog prog stack_ptr frame_ptr in
    let instrs_ll = [stub] :: [prefix] :: instrs_ll @ [[suffix]] in

    (* Debugging... *)
    (*
    let _ =
        let print_l instrs_l =
            Printf.printf "            [+] Debugging (instrs_l) :\n";
            List.iter (fun ins -> Printf.printf "                  %s\n" (dump_instr ins))  instrs_l;
            Printf.printf "             =========================\n";
        in
        let print_ll instrs_ll =
            Printf.printf "      [+] Debugging (instrs_ll) :\n";
            List.iter print_l instrs_ll;
            Printf.printf "      ==========================\n";
        in
        Printf.printf "[+] Debugging:\n";
        List.iter print_ll instrs_ll;
        Printf.printf "===============\n";
    in
    *)
    let impl_lll = process_func assign_regs instrs_ll in
    let impl_ll = List.flatten impl_lll in

    (* pairs = (instr, gm); gm = gadget metadata *)
    let pairs = List.flatten impl_ll in

    (* Reescribe instr AdvanceStack a RawHex*)
    let pairs = fix_ext_call_stuff pairs in

    let instrs = List.map fst pairs in

    let _ = dump_pairs pairs in
    let _ = verify_impl instrs in

    (* ??? *)
    let pairs = fix_symblic pairs in

    (* Remueve instrucciones superfluas, en este caso Lbl y Comment. *)
    let pairs = filter_trash pairs in

    (* Retorna un string con la dir de los gadgets (el código rop). *)
    let bin_str = to_binary pairs in
    instrs, pairs, bin_str

let parse_ropl_src src_fn =
    let cin = open_in src_fn in
    let lexbuf = Lexing.from_channel cin in
    let p = RoplParser.input RoplLexer.token lexbuf in
    let errors = RoplAst.verify_prog p in
    (RoplAst.unwrap_prog p, errors)

let parse_llvm_src fn =
    let cin = open_in fn in
    let lexbuf = Lexing.from_channel cin in
    let p = LlvmParser.input LlvmLexer.token lexbuf in
    let p = LlvmAstTranslator.translate_prog p in
    (p, [])

let main () =
    let argc = Array.length Sys.argv in

    if argc > 3 then
        let src_type = Sys.argv.(1) in
        let src_fn = Sys.argv.(2) in
        let vg_fn = Sys.argv.(3) in
        let out_fn =
            if src_type = "ropl" then
                "compiled-ropl.bin"
            else
                "compiled-llvm.bin"
        in

        let (p, errors) =
            if src_type = "ropl" then
                parse_ropl_src src_fn
            else
                parse_llvm_src src_fn
        in

        if errors <> [] then
            print_errors errors
        else
            (* Print program *)
            let s = RoplAst.dump_prog p in
            let _ = printf "DUMPED:\n%s\n####\n" s in

            (* Load program *)
            (* let p = RoplAst.unwrap_prog p in *)
            let p = RoplAst.move_main_to_front p in
            let p = RoplAst.flatten_prog p in

            (* Load gadgets *)
            let container = Common.unmarshal_from_file vg_fn in

            (* Compile program *)
            let cl, pairs, bin_str = compile p container in

            (* Print compiled code to file *)
            let _ = write_str_to_file out_fn bin_str in
            ()
    else
        (* Print usage message *)
        let err = Printf.sprintf "Usage:\n%s <src type> <src fn> <vg fn>\n" Sys.argv.(0) in
        print_string err

let _ = main()
