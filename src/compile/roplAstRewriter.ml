open Printf

open Common
open RegSets
open RoplAst
open SsaForm

(* Reescribe RoplAst en una forma SSA *)

let hARDCODED_PRINTF = 0x080484a0
let nO_NAME_LABEL = "@@"
let gLOBAL_END_LABEL = "global_end"

(* every invocation of f_next_reg returns new symbolic reg *)
(* Pasa a una representacion SSA *)
let make_rewrite_exp f_next_reg read_local ref_local =
    let rec rewrite_exp exp oreg =
        match exp with
        | BinOp(exp1, op, exp2) ->
            let reg1 = f_next_reg () in
            let iexp1 = rewrite_exp exp1 reg1 in
            let reg2 = f_next_reg () in
            let iexp2 = rewrite_exp exp2 reg2 in
            let o = BinO(oreg, reg1, op, reg2) in
            iexp1 @ iexp2 @ [o]
        | UnOp(op, exp) ->
            begin
            match op with
            | Sub -> rewrite_exp (BinOp(Const(0),op,exp)) oreg
            | Not -> rewrite_exp (BinOp(Const(-1),Xor,exp)) oreg
            | _ -> assert false
            end
        | Var(id) ->
            let rl = read_local id oreg in
            [rl]
        | Ref(id) ->
            let rl = ref_local id oreg in
            [rl]
        | ReadMem(id) ->
            let addr_reg = f_next_reg () in
            let rl = read_local id addr_reg in
            let rm = ReadM(oreg, addr_reg) in
            [rl;rm]
        | Const(x) ->
            let mov = MovRegConst(oreg, x) in
            [mov]
    in
    rewrite_exp

(* Reescribe una sentencia en función de instrucciones más sencillas. *)
(* Pasa a una representacion SSA *)
let rewrite_stmt stack_ptr frame_ptr locals fun_id stmt =
    let f_next_reg = make_reg_generator () in
    let rw_local id reg f_ctor =
        let id2off id = try Hashtbl.find locals id with Not_found -> assert false in
        let off = id2off id in
        f_ctor off reg
    in
    let write_local id reg =
        rw_local id reg (fun off reg -> WriteLocal(off, reg))
    in
    let read_local id reg =
        rw_local id reg (fun off reg -> ReadLocal(off, reg))
    in
    let ref_local id reg =
        rw_local id reg (fun off reg -> LocalAddr(off, reg))
    in
    let deref_local id reg =
        let f off reg =
            let addr_reg = f_next_reg () in
            let rl = ReadLocal(off, addr_reg) in
            let wm = WriteM(addr_reg, reg) in
            [rl;wm]
        in
        rw_local id reg f
    in
    let rewrite_exp = make_rewrite_exp f_next_reg read_local ref_local in
    let push_arg arg =
        (* just check if args are simple *)
        let _ = match arg with
            | Var(_) | ReadMem(_) | Ref(_) | Const(_) -> true
            | _ -> assert false
        in
        let reg = f_next_reg () in
        let iarg = rewrite_exp arg reg in
        let push = PushReg(reg) in
        iarg @ [push]
    in
    let push_args args =
        let rec aux acc args =
            match args with
            | arg::tl ->
                let pa = push_arg arg in
                aux (pa::acc) tl
            | [] -> acc
        in
        let pushes = aux [] args in
        (* let pushes = List.rev pushes in *)
        List.concat pushes
    in
    let set_eax_on_cond cond =
        (* ah = SF ZF xx AF xx PF xx CF *)
        (* returns mask and the value required to take the jump *)
        let flag_mask_const flag =
            let mask,v =
                match flag with
                | E -> (1 lsl 6), 1 lsl 6   (* jz, ZF = 1 *)
                | A -> (1 lor (1 lsl 6)), 0 (* ja, CF = ZF = 0 *)
                | B -> 1, 1                 (* jb, CF = 1 *)
                | _ -> assert false
            in
            (* flags are saved to AH, so shift *)
            let mask,v = mask lsl 8, v lsl 8 in
            mask, v
        in
        let neg, flags =
            match cond with
            | Cond(flags) -> false, flags
            | NCond(flags) -> true, flags
        in
        (* FIXME: just one flag atm *)
        let flag = match flags with hd::[] -> hd | _ -> assert false in
        if flag=MP then
            let mov = MovRegConst(C(EAX), 1) in
            [mov]
        else
            let mask, v = flag_mask_const flag in
            let reg = f_next_reg () in
            let mov1 = MovRegConst(reg, mask) in
            let and_ah = BinO(C(EAX), C(EAX), And, reg) in
            let reg = f_next_reg () in
            let mov2 = MovRegConst(reg, v) in
            let sub = BinO(C(EAX), C(EAX), Sub, reg) in
            let lahf = SaveFlags in
            let reg = f_next_reg () in
            (* ZF position in EAX: 6th bit of AH *)
            let mov3 = MovRegConst(reg, 1 lsl (6+8)) in
            let shr = BinO(C(EAX), C(EAX), Div, reg) in
            let reg = f_next_reg () in
            let mov4 = MovRegConst(reg, 1) in
            (* eax=1 iff cond *)
            let last = [BinO(C(EAX), C(EAX), And, reg)] in
            let last = last @
                if neg then [BinO(C(EAX), C(EAX), Xor, reg)]
                else []
            in
            [mov1;and_ah;mov2;sub;lahf;mov3;shr;mov4]@last
    in
    let rewrite stmt =
        match stmt with
        | Assign(id, exp) ->
            let reg = f_next_reg () in
            let iexp = rewrite_exp exp reg in
            let wl = write_local id reg in
            iexp @ [wl]
        | DerefAssign(id, exp) ->
            let reg = f_next_reg () in
            let iexp = rewrite_exp exp reg in
            let wl = deref_local id reg in
            iexp @ wl
        | WriteMem(id, exp) ->
            let exp_reg = f_next_reg () in
            let iexp = rewrite_exp exp exp_reg in
            let addr_reg = f_next_reg () in
            let rl = read_local id addr_reg in
            let wm = WriteM(addr_reg, exp_reg) in
            iexp @ [rl;wm]
        | Cmp(exp1, exp2) ->
            let reg1, reg2 = f_next_reg (), f_next_reg () in
            let iexp1 = rewrite_exp exp1 reg1 in
            let iexp2 = rewrite_exp exp2 reg2 in
            let reg = f_next_reg () in
            let sub = BinO(reg, reg1, Sub, reg2) in
            let lahf = SaveFlags in
            iexp1 @ iexp2 @ [sub; lahf]
        | Call(id, ExpArgs(exp_args)) ->
            let pushes = push_args exp_args in
            let reg = f_next_reg () in
            let mov = MovRegSymb(reg, FromTo(Named(fun_label id), Unnamed(Forward))) in
            let p = PushReg(reg) in
            let reg = f_next_reg () in
            let mov2 = MovRegSymb(reg, FromTo(Unnamed(Forward), Named(fun_label id))) in
            let add = OpStack(Add, reg) in (* jmp *)
            let lbl = Lbl(nO_NAME_LABEL) in
            pushes @ [mov;p;mov2;add;lbl]
        | ExtCall(id, ExpArgs(exp_args)) ->
            let rec range i j = if i >= j then [] else i :: (range (i+1) j) in
            let make_filler n =
                let m x = let x = x land 0xFF in (x lsl 24) lor (x lsl 16) lor (x lsl 8) lor x in
                let f acc x = RawHex(m x)::acc in
                let nums = range 0 n in
                let filler = List.fold_left f [] nums in
                let filler = List.rev filler in
                filler
            in
            let store_args imp_addr args =
                let addr_reg = f_next_reg () in
                let v_reg = f_next_reg () in
                let off_reg = f_next_reg () in
                let fix_reg = f_next_reg () in

                let per_arg acc arg =
                    let iarg = rewrite_exp arg v_reg in
                    let wm = WriteM(addr_reg, v_reg) in
                    let set = MovRegConst(off_reg, 4) in
                    let add = BinO(addr_reg, addr_reg, Add, off_reg) in
                    acc @ (iarg@[wm;set;add]) (* O(n^2) *)
                in
                let tmp_reg = f_next_reg () in
                let lbl = Lbl(nO_NAME_LABEL) in
                let save_esp = MovRegReg(tmp_reg, C(ESP)) in
                let mov = MovRegSymb(fix_reg, FromTo(Unnamed(Backward), Unnamed(Forward))) in
                let fix1 = BinO(addr_reg, tmp_reg, Add, fix_reg) in
                (* Restore import address *)
                let reg = f_next_reg () in
                let set_imp = MovRegConst(reg, imp_addr) in
                let wm = WriteM(addr_reg, reg) in
                let reg = f_next_reg () in
                let set8 = MovRegConst(reg, 8) in
                let fix2 = BinO(addr_reg, addr_reg, Add, reg) in
                let stores = List.fold_left per_arg [] args in
                [save_esp;lbl;mov;fix1;set_imp;wm;set8;fix2] @ stores
            in
            let jmp_over_locals locals_filler =
                let n = List.length locals_filler in
                let reg = f_next_reg () in
                let mov = MovRegConst(reg, n*4) in
                let ops = OpStack(Add, reg) in
                [mov;ops]
            in
            let imp_addr = hARDCODED_PRINTF in
            let cmt_s = sprintf "jmp %s" id in
            (* At least 128 bytes for locals *)
            let n_args = List.length exp_args in
            let locals_filler = make_filler (256/4) in
            let jmp_skip_locals = jmp_over_locals locals_filler in
            (* FIXME: hardcoded printf *)
            let jmp_imp = RawHex(imp_addr) in
            (* FIXME: we don't need equality in AdvStack, just >= *)
            let adv = AdvanceStack(n_args*4+4) in
            let lbl = Lbl(nO_NAME_LABEL) in
            let args_filler = make_filler n_args in
            let write_args = store_args imp_addr exp_args in
            write_args @ jmp_skip_locals @ locals_filler @
                [Comment(cmt_s);lbl;jmp_imp;adv] @ (args_filler)
        | Branch(cond, id) ->
            (* eax=1 iff cond, 0 otherwise *)
            let setz = set_eax_on_cond cond in
            let reg = f_next_reg () in
            let start = Unnamed(Forward) in
            let fin = Named(fun_local_label fun_id id) in
            let mov = MovRegSymb(reg, FromTo(start, fin)) in
            let mul = BinO(C(EAX), C(EAX), Mul, reg) in
            let add = OpStack(Add, C(EAX)) in (* jmp *)
            let lbl = Lbl(nO_NAME_LABEL) in
            setz @ [mov; mul; add; lbl;]
        | Label(id) -> [Lbl(fun_local_label fun_id id)]

        | Enter(n) ->
                let reg = f_next_reg () in
                let rm1 = ReadMConst(reg, frame_ptr) in
                let push = PushReg(reg) in
                let reg = f_next_reg () in
                let rm2 = ReadMConst(reg, stack_ptr) in
                let wm1 = WriteMConst(frame_ptr, reg) in
                let reg1 = f_next_reg () in
                let rm3 = ReadMConst(reg1, stack_ptr) in
                let reg2 = f_next_reg () in
                let mov = MovRegConst(reg2, n) in
                let reg3 = f_next_reg () in
                let sub = BinO(reg3, reg1, Sub, reg2) in
                let wm2 = WriteMConst(stack_ptr, reg3) in
                [rm1;push;rm2;wm1;rm3;mov;sub;wm2]
        | Leave ->
                let reg = f_next_reg () in
                let rm = ReadMConst(reg, frame_ptr) in
                let wm1 = WriteMConst(stack_ptr, reg) in
                let reg = f_next_reg () in
                let pop = PopReg(reg) in
                let wm2 = WriteMConst(frame_ptr, reg) in
                [rm;wm1;pop;wm2]
        | Ret(id) ->
                let reg1 = f_next_reg () in
                let reg2 = f_next_reg () in
                let reg3 = f_next_reg () in
                let p2 = PopReg(reg1) in
                let mov = MovRegSymb(reg2, FromTo(Unnamed(Forward), Named(fun_label id))) in
                let sub = BinO(reg3, reg2, Add, reg1) in
                let add = OpStack(Add, reg3) in (* jmp *)
                let lbl = Lbl(nO_NAME_LABEL) in
                [p2;mov;sub;add;lbl;]
        (* AssignTab is replaced with Assign(id,C) earlier *)
        | AssignTab(_,_) -> assert false
    in
    let new_instrs = rewrite stmt in
    let comments =
        match stmt with
        | Label(_) -> []
        | _ ->
            let s = RoplAst.dump_stmt stmt in
            [Comment(s)]
    in
    comments @ new_instrs

(* Reescribe el programa ropl en funcion de instrucciones más sencillas. *)
let rewrite_prog prog stack_ptr frame_ptr =
    (* Crea un hash table con (var, posicion en la pila) para los parametros
    de entrada y las variables locales. *)
    let assign_vars func =
        let collect_locals stmts =
            let rec aux acc stmts =
                match stmts with
                (* all locals are initialized before use *)
                | (Assign(id,_))::tl -> aux (id::acc) tl
                | hd::tl -> aux acc tl
                | [] -> acc
            in
            let ids = aux [] stmts in
            let ids = Common.generic_unique ids in
            ids
        in
        let Fun(id, Args(args), FunBody(stmts)) = func in
        let h = Hashtbl.create 32 in
        let f (h,n) arg =
            let _ = Hashtbl.add h arg n in
            (h,n+4)
        in
        (* v1,frame,ret,arg1,...,argN *)
        let (h,_) = List.fold_left f (h,12) args in
        let g (h,n) id =
            let _ = Hashtbl.add h id n in
            (h,n-4)
        in
        let ids = collect_locals stmts in
        let (h,_) = List.fold_left g (h,0) ids in
        h
    in
    (* Reescribe una funcion ropl en funcion de instrucciones más sencillas. *)
    let rewrite_func func =
        (* Agrega enter y leave a lista de sentencias reservando la cantidad
        de bytes correspondientes a todas las variables locales + los
        parámetros de entrada. *)
        let add_stack_stuff fun_id locals stmts =
            let locals_count = Hashtbl.length locals in
            (* every local is a dword *)
            let pre = [Enter(locals_count*4)] in
            let suf = [Leave;Ret(fun_id)] in
            let stmts = pre@stmts@suf in
            stmts
        in
        let rewrite_stmt = rewrite_stmt stack_ptr frame_ptr in
        let Fun(fun_id, Args(args), FunBody(stmts)) = func in
        let locals = assign_vars func in
        let stmts = add_stack_stuff fun_id locals stmts in
        let instrs = List.map (fun stmt -> rewrite_stmt locals fun_id stmt) stmts in
        let head = RoplAst.dump_func_head func in
        let fun_lbl = fun_label fun_id in
        let pre = [Comment(head); Lbl(fun_lbl);] in
        let instrs = [pre]@instrs in
        instrs
    in
    let Prog(func_list) = prog in
    let rew = List.map rewrite_func func_list in
    (* let rew = List.concat (rew) in *)
    rew
