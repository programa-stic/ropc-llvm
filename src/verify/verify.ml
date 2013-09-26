open Printf

open Common

(** Gadget Semantic Veritication Tool *)

(* Al solver le pasan una sentencia del estilo: *)
(* Declaración de variables libres *)
(* Aseveraciones. ASSERT(F); donde: F must be a well-formed expression
    (given previous definitions and declarations) of type BOOLEAN *)
(* QUERY(F); donde STP can be queried to determine whether or not a formula F
    is logically implied by the formulas in the current logical context. *)
(* COUNTEREXAMPLES: Si el resultado de la query dió Invalid, counterexample
retorna una asignación que invalida el query(F) *)
(* Ejemplo concreto: *)
(*
% free variables:
R_EBP_0 : BITVECTOR(32);
R_EDI_3 : BITVECTOR(32);
% end free variables.

ASSERT(
0bin1 = (
    LET initial_EDI_11151_0 = R_EDI_3 IN (
        LET initial_EBP_11152_1 = R_EBP_0 IN (
            LET final_EBP_11279_2 = R_EBP_0 IN
                IF ( NOT(final_EBP_11279_2=(initial_EBP_11152_1&initial_EDI_11151_0)) ) THEN
                    0bin1
                ELSE
                    0bin0
                ENDIF
            )
        )
    )
);
QUERY(FALSE);
COUNTEREXAMPLE;
*)
(*
    Counterexample:
        R_EBP_0 -> 0x1
        R_EDI_3 -> 0
*)

let pREFIX_INITIAL = "initial_"
let pREFIX_FINAL = "final_"
let lITTLE_ENDIAN = Ast.exp_false

let sOLVER = (Smtexec.STP.si)

(*
let counter = ref 0;;

let get_formula_fn fn =
    counter := !counter + 1;
    fn^(string_of_int !counter)^".formula.txt"
*)
let get_formula_fn fn = fn^".formula.txt"

(* l1-l2 *)
let diff l1 l2 =
    (* set difference for lists *)
    let rec aux acc regs =
        match regs with
        | reg::tl ->
            begin
                try
                    let _ = List.find (fun r -> reg=r) l2 in
                    aux acc tl
                with Not_found ->
                    aux (reg::acc) tl
            end
        | [] -> acc
    in
    aux [] l1

let dump_prog prog =
    let pp = new Pp.pp_oc stdout in
    begin
    pp#ast_program prog;
    pp#close;
    end

let compute_wp cfg post =
  let (gcl, post) = Utils_common.to_ssagcl cfg post in
  (Wp.wp gcl post, [])

(* taken from bap/utils/topredicate.ml *)
let prep prog post =
    let cfg = Cfg_ast.of_prog prog in
    let cfg = Prune_unreachable.prune_unreachable_ast cfg in
    let (wp, foralls) = compute_wp cfg post in
    (wp, foralls)

(* Genera el archivo de fórmulas que luego el solver va a procesar. Se
    genera usando las sentencias a verificar y la poscondición a cumplir. *)
(* De las sentencias (prog) se obtiene el cfg (control flow graph) y con este
    se computa la Weakest Precondition. *)
(* La Weakest Precondition se calcula a partir del GCL (Guarded Command
    Language) mediante el CFG. *)
(* prog - stmt list
    post - Ast.exp postcondition
    oc - output channel *)
let emit_formula prog post oc =
    let (wp, foralls) = prep prog post in
    let m2a = new Memory2array.memory2array_visitor () in
    let wp = Ast_visitor.exp_accept m2a wp in
    let foralls = List.map (Ast_visitor.rvar_accept m2a) foralls in
    let pp = ((sOLVER#printer) :> Formulap.fppf) in
    let p = pp oc in
    begin
    p#assert_ast_exp_with_foralls foralls wp;
    p#counterexample;
    p#close;
    end

(* sr_pairs = (save_var, reg_var) list
    eg.: initial_eax = R_EAX -> (initial_eax, R_EAX) *)
let emit_save_regs sr_pairs =
    let rec aux acc regs =
        match regs with
        | (save_var, reg_var)::tl ->
            let i = Ast.Move(save_var, Ast.Var(reg_var), []) in
            aux (i::acc) tl
        | [] -> acc
    in
    aux [] sr_pairs

let prefixed_var prefix s =
    let s = prefix^s in
    let av, _ = Parser.exp_from_string s in
    let v = Common.unwrap_ast_var av in
    v

let prefixed_var_reg reg prefix =
    let s = Common.reg_to_str reg in
    let typ = ":u32" in
    let s = s^typ in
    prefixed_var prefix s

let initial_var_reg reg = prefixed_var_reg reg pREFIX_INITIAL
let final_var_reg reg =  prefixed_var_reg reg pREFIX_FINAL

let get_reg_var reg = prefixed_var_reg reg ""

let initial_mem () = prefixed_var pREFIX_INITIAL Common.gLOBAL_MEM
let final_mem () = prefixed_var pREFIX_FINAL Common.gLOBAL_MEM

let x_mem_pair f_mem =
    let mem_v = prefixed_var "" Common.gLOBAL_MEM in
    let mem = f_mem () in
    (mem, mem_v)

let initial_mem_pair () = x_mem_pair initial_mem
let final_mem_pair () = x_mem_pair final_mem

let x_pair reg f =
    let rv = Common.reg_var reg in
    let iv = f reg in
    (iv,rv)

let initial_pair reg = x_pair reg initial_var_reg
let final_pair reg = x_pair reg final_var_reg

let initial_eflags () = prefixed_var pREFIX_INITIAL Common.eFLAGS

let op_to_type_op op =
    match op with
    | Common.ADD -> Type.PLUS
    | Common.SUB -> Type.MINUS
    | Common.MUL -> Type.TIMES
    | Common.DIV -> Type.DIVIDE
    | Common.XOR -> Type.XOR
    | Common.OR  -> Type.OR
    | Common.AND -> Type.AND

let exp_addr_off addr_v off32 =
    let ast_off = Int_utils.ast_i32_from_i32 off32 in
    let addr_exp = Ast.BinOp(Type.PLUS, Ast.Var(addr_v), ast_off) in
    addr_exp

let exp_load_reg_off mem_v addr_v off32 =
    let addr_exp = exp_addr_off addr_v off32 in
    let exp = Ast.Load(Ast.Var(mem_v), addr_exp, lITTLE_ENDIAN, Ast.reg_32) in
    exp

let exp_store_reg_off_val mem_v addr_v off32 exp_value =
    let addr_exp = exp_addr_off addr_v off32 in
    let exp = Ast.Store(Ast.Var(mem_v), addr_exp, exp_value, lITTLE_ENDIAN, Ast.reg_32) in
    exp

(*
 * PSC Functions
 *)
let psc_copy_reg dst src =
    (* genera el string de la variable src para ser procesada por el solver. *)
    let (init_src, src_var) = initial_pair src in
    (* genera el string de la variable dst para ser procesada por el solver. *)
    let (final_dst, dst_var) = final_pair dst in
    (* genera el prefijo (que es salvar el valor inicial de la var que se va a
    modificar). *)
    let prefix = emit_save_regs [(init_src, src_var)] in
    (* genera el sufijo (que es salvar el valor inicial de la var que se va a
    modificar). *)
    let suffix = emit_save_regs [(final_dst, dst_var)] in
    (* cond = (final_dst != init_src) *)
    let cond = Ast.BinOp(Type.NEQ, Ast.Var(final_dst), Ast.Var(init_src)) in
    (prefix, suffix, cond)

let psc_binop dst src1 op src2 =
    let (init_src1, src1_v) = initial_pair src1 in
    let (init_src2, src2_v) = initial_pair src2 in
    let (final_dst, dst_v) = final_pair dst in
    let prefix = emit_save_regs [(init_src1, src1_v);(init_src2, src2_v)] in
    let suffix = emit_save_regs [(final_dst, dst_v)] in
    let type_op = op_to_type_op op in
    let exp = Ast.BinOp(type_op, Ast.Var(init_src1), Ast.Var(init_src2)) in
    (* cond = ( final_dst != ( init_src1 op init_src2 ) ) *)
    let cond = Ast.BinOp(Type.NEQ, Ast.Var(final_dst), exp) in
    (prefix, suffix, cond)

let psc_load_const reg off =
    let (init_mem, mem_v) = initial_mem_pair () in
    let (init_esp, esp_v) = initial_pair ESP in
    let (final_reg, reg_v) = final_pair reg in
    let prefix = emit_save_regs [(init_mem, mem_v);(init_esp, esp_v)] in
    let suffix = emit_save_regs [(final_reg, reg_v)] in
    let ast_off = Int_utils.ast_i32 off in
    let exp_esp = Ast.BinOp(Type.PLUS, Ast.Var(init_esp), ast_off) in
    let exp = Ast.Load(Ast.Var(init_mem), exp_esp, lITTLE_ENDIAN, Ast.reg_32) in
    let cond = Ast.BinOp(Type.NEQ, Ast.Var(final_reg), exp) in
    (prefix, suffix, cond)

let common_psc_read_mem dst_reg addr_reg off f_op =
    let (init_mem, mem_v) = initial_mem_pair () in
    let (init_dst, dst_v) = final_pair dst_reg in
    let (final_dst, _) = final_pair dst_reg in
    let (init_addr, addr_v) = initial_pair addr_reg in
    let prefix = emit_save_regs [(init_mem, mem_v);(init_addr, addr_v);(init_dst, dst_v)] in
    let suffix = emit_save_regs [(final_dst, dst_v)] in
    let exp = exp_load_reg_off init_mem init_addr off in
    let exp = f_op init_dst exp in
    let cond = Ast.BinOp(Type.NEQ, Ast.Var(final_dst), exp) in
    (prefix, suffix, cond)

let psc_read_mem dst_reg addr_reg off =
    let f init_dst mem_exp = mem_exp in
    common_psc_read_mem dst_reg addr_reg off f

let common_psc_write_mem addr_reg off src_reg f_op =
    let (init_mem, mem_v) = initial_mem_pair () in
    let (final_mem, _) = final_mem_pair () in
    let (init_src, src_v) = initial_pair src_reg in
    let (init_addr, addr_v) = initial_pair addr_reg in
    let prefix = emit_save_regs [(init_mem, mem_v);(init_addr, addr_v);(init_src, src_v)] in
    let suffix = emit_save_regs [(final_mem, mem_v)] in
    let init_src = Ast.Var(init_src) in
    let init_load = exp_load_reg_off init_mem init_addr off in
    let store_exp = f_op init_load init_src in
    let init_store = exp_store_reg_off_val init_mem init_addr off store_exp in
    let cond = Ast.BinOp(Type.NEQ, Ast.Var(final_mem), init_store) in
    (prefix, suffix, cond)

let psc_write_mem addr_reg off src_reg =
    let f init_load init_src = init_src in
    common_psc_write_mem addr_reg off src_reg f

let psc_read_mem_op dst_reg op addr_reg off =
    let f init_dst mem_exp =
        let t_op = op_to_type_op op in
        let exp = Ast.BinOp(t_op, Ast.Var(init_dst), mem_exp) in
        exp
    in
    common_psc_read_mem dst_reg addr_reg off f

let psc_write_mem_op addr_reg off op src_reg =
    let f init_load init_src =
        let t_op = op_to_type_op op in
        let exp = Ast.BinOp(t_op, init_load, init_src) in
        exp
    in
    common_psc_write_mem addr_reg off src_reg f

let psc_lahf () =
    let mask_eflags exp =
        let exp = Ast.BinOp(Type.AND, exp, Int_utils.ast_i32 0xD5) in
        (* 2nd bit of EFLAGS is always set *)
        let exp = Ast.BinOp(Type.OR, exp, Int_utils.ast_i32 0x2) in
        exp
    in
    let eflags_v = Common.str_to_var Common.eFLAGS in
    let init_eflags = initial_eflags () in
    let (final_eax, eax_v) = final_pair EAX in
    let prefix = emit_save_regs [(init_eflags, eflags_v)] in
    let suffix = emit_save_regs [(final_eax, eax_v)] in
    let exp_ah = Ast.BinOp(Type.RSHIFT, Ast.Var(final_eax), Int_utils.ast_i32 8) in
    let exp_ah = mask_eflags exp_ah in
    let exp_efl = mask_eflags (Ast.Var(init_eflags)) in
    let cond = Ast.BinOp(Type.NEQ, exp_ah, exp_efl) in
    (prefix, suffix, cond)

let psc_op_esp op reg stack_fix =
    let (prefix, suffix, cond) = psc_binop ESP ESP op reg in
    let t,v,exp =
        match cond with
        | Ast.BinOp(t,v,exp) -> t,v,exp
        | _ -> assert false
    in
    let new_exp = Ast.BinOp(Type.PLUS, exp, Int_utils.ast_i32 stack_fix) in
    let cond = Ast.BinOp(t,v,new_exp) in
    (prefix, suffix, cond)

(* prefix, suffix, condition *)
let psc_gadget g =
    match g with
    | CopyReg(dst, src) -> psc_copy_reg dst src
    | BinOp(dst, src1, op, src2) -> psc_binop dst src1 op src2
    | LoadConst(reg, off) -> psc_load_const reg off
    | ReadMem(dst_reg, addr_reg, off) -> psc_read_mem dst_reg addr_reg off
    | WriteMem(addr_reg, off, src_reg) -> psc_write_mem addr_reg off src_reg
    | ReadMemOp(dst_reg, op, addr_reg, off) -> psc_read_mem_op dst_reg op addr_reg off
    | WriteMemOp(addr_reg, off, op, src_reg) -> psc_write_mem_op addr_reg off op src_reg
    | Lahf -> psc_lahf ()
    | OpEsp(op, r, sf) -> psc_op_esp op r sf

(* final_esp = initial_esp + fix *)
let psc_stack_fix fix =
    let (init_esp, esp_v) = initial_pair ESP in
    let (final_esp, _) = final_pair ESP in
    let prefix = emit_save_regs [(init_esp, esp_v)] in
    let suffix = emit_save_regs [(final_esp, esp_v)] in
    let ast_fix = Int_utils.ast_i32 fix in
    let exp_esp = Ast.BinOp(Type.PLUS, Ast.Var(init_esp), ast_fix) in
    let cond = Ast.BinOp(Type.NEQ, Ast.Var(final_esp), exp_esp) in
    (prefix, suffix, cond)

(* ask about PRESERVED regs, to get MODIFIED regs *)
let psc_preserved_regs regs =
    let f (l_init,l_final) reg =
        let (init_reg, reg_v) = initial_pair reg in
        let (final_reg, _) = final_pair reg in
        let l_init = (init_reg, reg_v)::l_init in
        let l_final = (final_reg, reg_v)::l_final in
        (l_init, l_final)
    in
    let (l_init, l_final) = List.fold_left f ([],[]) regs in
    let prefix = emit_save_regs l_init in
    let suffix = emit_save_regs l_final in
    (* ~(init_reg = final_reg AND ...) == init_reg <> final_reg OR ... *)
    let cond_maker acc (init_reg, final_reg) =
        let reg_neq = Ast.BinOp(Type.NEQ, Ast.Var(init_reg), Ast.Var(final_reg)) in
        let cond = Ast.BinOp(Type.OR, reg_neq, acc) in
        cond
    in
    let init_final = List.map2 (fun (ir,_) (fr,_) -> (ir,fr)) l_init l_final in
    let cond = List.fold_left cond_maker (Ast.exp_false) init_final in
    (prefix, suffix, cond)

(* Agrega prefijos y sufijos a la lista de sentencias para que pueda ser
    procesada por el solver. *)
let wrap_with_ps f_psc stmts =
    let (prefix, suffix, cond) = f_psc () in
    let stmts = prefix @ stmts @ suffix in
    stmts, cond

(*
let fake () =
    let exp, _ = Parser.exp_from_string "R_EAX:u32 + R_EBX:u32+1:u32" in
    let v, _ = Parser.exp_from_string "R_EAX" in
    let v = Gdefs.unwrap_ast_var v in
    let i = Ast.Move(v, exp, []) in
    [i]
*)

(* Retorna función verficadora de gadgets. *)
let make_verify fn formula_fn =
    let prog = Asmir.open_program fn in
    let get_stmts off_s off_e =
        let (i,j) = Int_utils.cast_range off_s off_e in
        let stmts = Asmir.asmprogram_to_bap_range prog i j in
        let stmts = Common.drop_last stmts in
        stmts
    in
    let solve_formula formula_fn =
          let r = sOLVER#solve_formula_file ~printmodel:true formula_fn in
          let _ = Printf.fprintf stderr "Solve result: %s\n" (Smtexec.result_to_string r) in
          r
    in
    let is_valid r =
        match r with
        | Smtexec.Valid -> true
        | Smtexec.Invalid -> false
        | Smtexec.SmtError -> false (*; Printf.printf "DEBUG: Solve result: SmtError\n" *)
        | Smtexec.Timeout -> false (*; Printf.printf "DEBUG: Solve result: Timeout\n" *)
        (*| _ -> false *) (* assert false *) (* SmtError, Timeout *)
    in
    let ask_solver stmts cond =
        (* let oc = open_out formula_fn in *)
        let oc = open_out (get_formula_fn "a.out") in
        let _ = emit_formula stmts cond oc in
        let _ = close_out oc in
        let res = solve_formula formula_fn in
        is_valid res
    in
    let generic_verify f_psc stmts =
        (* ps_stmts : sentencias en formato solver *)
        let ps_stmts, cond = wrap_with_ps f_psc stmts in
        let _ = dump_prog ps_stmts in
        ask_solver ps_stmts cond
    in
    (* verify gadget-specific properties *)
    (* gadget : gadget *)
    (* stmts : Ast.Program *)
    let verify_gadget_stmts gadget stmts =
        (* genera el prefijo, sufijo y la condición para verificar le gadget. *)
        let f_psc () = psc_gadget gadget in
        (* Realiza la verificación. *)
        generic_verify f_psc stmts
    in
    (* verify that final_esp = initial_esp + fix *)
    let verify_stack_fix stmts stack_fix =
        let f_psc () = psc_stack_fix stack_fix in
        generic_verify f_psc stmts
    in
    let verify_preserved_regs stmts preserved =
        let f_psc () = psc_preserved_regs preserved in
        (* check if all of these are preserved. if not, check them one by one *)
        let valid = generic_verify f_psc stmts in
        valid
    in
    let update_mod_regs stmts mod_regs preserved =
        (* at least one reg in 'preserved' is modified.. *)
        let is_modified reg =
            let f_psc () = psc_preserved_regs [reg] in
            not (generic_verify f_psc stmts)
        in
        let modified = List.filter is_modified preserved in
        modified @ mod_regs
    in
    (* returns bool,mod_regs, where bool is true iff semantics and stack_fix are ok.
        mod_regs can be larger than original *)
    let verify_gmeta gmeta =
        let _ = Printf.printf "Verifying Gadget: %s\n\n" (dump_gmeta gmeta) in
        (* Carga un gmeta y lo descompone en sus partes. *)
        let GMeta(gadget, fm, mod_regs, stack_fix) = gmeta in
        let FileMeta(off_s, off_e) = fm in
        (* Carga los stmts que corresponden al gadget que se está procesando. *)
        let stmts = get_stmts off_s off_e in
        let verify () =
            (* Verifica las sentencias del gadget. *)
            let sem_ok =
            match gadget with
                | BinOp(_,_,DIV,_) -> true  (* FIX: There are problems verifying division. So, for now, we skip it. *)
                | _                -> verify_gadget_stmts gadget stmts
            in
            (* stack_fix for OpEsp is checked differently *)
            match gadget with
            | OpEsp(_,_,_) -> sem_ok
            | _ -> sem_ok && verify_stack_fix stmts stack_fix
        in
        let update_mod_regs () =
            let preserved = diff Common.rEGS_NO_ESP mod_regs in
            let all_ok = verify_preserved_regs stmts preserved in
            if all_ok then mod_regs
            else update_mod_regs stmts mod_regs preserved
        in
        let semantics_ok = verify () in
        let mod_regs =
            (* recalculate only if semantics are ok. invoking the solver is costly *)
            if semantics_ok then update_mod_regs ()
            else mod_regs
        in
        semantics_ok, mod_regs
    in
    verify_gmeta

(* GContainer = filename * (data section start, data section end) * gadget list
    type used for marshaling candidates for verification *)
(* fmeta = (offset_start, offset_end) *)
(* gmeta = gadget, file meta, modified registers, stack_fix *)
let verify_and_update_container container =
    let GContainer(fn, data, gmetas) = container in

    let formula_fn = get_formula_fn fn in

    (* verifica cada uno de los gadgets. *)
    let verify_gmeta = make_verify fn formula_fn in
    let f gmeta =
        let (semantics_ok, mod_regs) = verify_gmeta gmeta in
        (semantics_ok, gmeta, mod_regs)
    in
    let gmetas = List.map f gmetas in

    (* kill those with bad semantics *)
    let gmetas = List.filter (fun (ok,_,_) -> ok) gmetas in
    let gmetas = List.map (fun (_,gm,mr) -> (gm,mr)) gmetas in

    (* update mod_regs *)
    let upd (gm, mr) =
        let GMeta(gadget, fm, mod_regs, stack_fix) = gm in
        GMeta(gadget, fm, mr, stack_fix)
    in
    let gmetas = List.map upd gmetas in

    let new_container = GContainer(fn, data, gmetas) in
    new_container

let main () =
    let argc = Array.length Sys.argv in

    if argc > 2 then
        let fn = Sys.argv.(1) in
        let ofn = Sys.argv.(2) in

        (* Load gadget file *)
        let container = Common.unmarshal_from_file fn in

        (* Update gadgets *)
        let upd_container = verify_and_update_container container in
        Common.marshal_to_file ofn upd_container
    else
        (* Print usage message *)
        let err = Printf.sprintf "Usage:\n%s <candidates file> <output file>\n" Sys.argv.(0) in
        output_string stdout err

let _ = main ()
