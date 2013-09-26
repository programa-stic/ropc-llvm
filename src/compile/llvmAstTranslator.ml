(*
 * NOTAS:
 *  * Branch: La condición del branch es el resultado de un icmp. Por lo
 *  tanto, para poder traducirlo, hay que obtener la cond del icmp asociado
 *  al branch en cuestión y con eso hacer la traducción. Entonces, hay que
 *  hacer un pasada previa a la traducción para resolver eso (etapa de
 *  preprocesamiento). Habría que generar un nuevo LlvmAst.Branch, por
 *  ejemplo, LlvmAst.BranchExplicit que posea la condición y, luego, pasar
 *  de este a RoplAst.Branch.
 *
 * TODO:
 *  * Call: Hay que resolver de alguna manera las qué funciones son
 *  externas y cuáles no.
 *)

exception TranslationException;;

(* Auxiliary functions *)
(* ------------------------------------------------------------------------- *)
let is_pointer var =
    let last_char = var.[(String.length var) - 1] in
        last_char == '*'

let remove_pointer var =
    String.sub var 0 (String.length var - 1)

let is_intrinsic func =
    String.compare func "@llvm.memcpy.p0i8.p0i8.i64" == 0

let get_intrinsic_name func =
    let split = Str.split (Str.regexp "\\.") func in
        List.nth split 1

let create_hashtable size init =
    let tbl = Hashtbl.create size in
        List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
        tbl

let build_func_table func_list =
    let mapper f =
        match f with
        | LlvmAst.Fun(id, args, body) -> id
    in
        let func_info = List.map mapper func_list in
            func_info

let is_array_type ty =
    Str.string_match (Str.regexp "\\[\\(.*\\) x \\(.*\\)\\]") ty 0

let is_primitive_type ty =
    Str.string_match (Str.regexp "i\\(.*\\)") ty 0

let unpack_array_type ty =
    let _ = Str.string_match (Str.regexp "\\[\\(.*\\) x \\(.*\\)\\]") ty 0 in
        (int_of_string((Str.matched_group 1 ty)), (Str.matched_group 2 ty))

let sizeof_array_type_elem elem_ty =
    match elem_ty with
    | "i8"  -> 1
    | "i16" -> 2
    | "i32" -> 4
    | "i64" -> 8
    | _     -> failwith ("Unsupported size : " ^ elem_ty)

let generate_tab_list n =
    let rec f n =
        if n == 0 then [] else 0 :: (f (n-1))
    in
        f n

let unpack_exp_args exp_args =
    match exp_args with
    | LlvmAst.ExpArgs(typed_exp) -> typed_exp

(*
 *  array_type_to_size_list: Transforma, array en una lista de sus
 *  respectivos tamaños por coordenada. Por ejemplo,
 *      [10 x [20 x [3 x i32]]] -> [10; 20; 3; 4]
 *)
let array_type_to_size_list ty =
    let rec f typ acc =
        if is_array_type typ then
            let elem_count, elem_ty = unpack_array_type typ in
            f elem_ty acc @ [elem_count]
        else
            let elem_size = sizeof_array_type_elem typ in
            acc @ [elem_size]
    in
    f ty []

let rec typed_exp_list_to_exp_list typed_exp_list =
    match typed_exp_list with
    | []                                -> []
    | LlvmAst.TypedExp(ty, exp) :: tail -> exp :: typed_exp_list_to_exp_list tail

let translate_intrinsic_args intrinsic args =
    match intrinsic with
    | "memcpy" ->
        let dst, src, len =
            List.nth args 0, List.nth args 1, List.nth args 2
        in
            [dst; src; len]

    | _ -> failwith ("Unsupported intrinsic : " ^ intrinsic)

let is_extern_function id func_table =
    List.exists (fun name -> String.compare id name == 0) func_table

(* Filter functions *)
(* ------------------------------------------------------------------------- *)
let filter_exp exp =
    match exp with
    | LlvmAst.Alloca(_, _) -> true
    | LlvmAst.BitCast(_, _, _) -> true
    | LlvmAst.GetElementPtr(_, _, _) -> true
    | _ -> true

(*
 * TODO:
 *  * LlvmAst.Ret : Ver cómo retornar valores.
 *)
let filter_stmt stmt =
    match stmt with
    | LlvmAst.Assign(id, exp) -> filter_exp exp
    | LlvmAst.Ret(_) -> false
    | LlvmAst.RetVoid -> false
    | _ -> true

(* Preprocessor Functions *)
(* ------------------------------------------------------------------------- *)
(*
 * TODO:
 *  * Mejorar, no asumir que icmp y br están juntas.
 *)
let preprocess_branch stmt1 stmt2 =
    match stmt2 with
    | LlvmAst.BranchE(exp, iftrue, iffalse) ->
        begin
            match stmt1 with
            | LlvmAst.Assign(id, LlvmAst.ICmp(cond, exp1, exp2)) ->
                LlvmAst.BranchC(cond, iftrue, iffalse)

            | _ -> raise (Invalid_argument "assign_cmp")
        end
    | _ -> stmt2

let process_call_arg typed_exp =
    match typed_exp with
    | LlvmAst.TypedExp(ty, exp) ->
        match exp with
        | LlvmAst.GetElementPtr(ty', id', typed_exps') ->
            let tmp_var_lbl = "@tmp_var_lbl" in
            let tmp_var     = LlvmAst.Var(tmp_var_lbl) in
            let assign_exp  = LlvmAst.Assign(tmp_var_lbl, exp) in
                [assign_exp], [LlvmAst.TypedExp(ty, tmp_var)]

        | other ->
            [], [typed_exp]

let process_call_args typed_exps =
    let rec apply_fn exps assign_exps new_typed_exps =
        match exps with
        | []        -> assign_exps, new_typed_exps
        | exp :: tl ->
            let assign_exp, new_typed_exp = process_call_arg exp in
                apply_fn tl (assign_exps @ assign_exp) (new_typed_exps @ new_typed_exp)
    in
    apply_fn typed_exps [] []

let rec preprocess_branches stmt_list =
    match stmt_list with
    | [] -> []
    | x :: [] -> [x]
    | x :: y :: [] -> x :: (preprocess_branch x y) :: []
    | x :: y :: t  ->
        match y with
        | LlvmAst.BranchE(exp, iftrue, iffalse) ->
            x :: (preprocess_branch x y) :: (preprocess_branches t)

        | other ->
            x :: (preprocess_branches (y :: t))

let preprocess_exp_get_element_ptr smt =
    match smt with
    | LlvmAst.Call(id, LlvmAst.ExpArgs(typed_exps)) ->
        let assign_exps, new_typed_exps = process_call_args typed_exps in
            assign_exps @ [ LlvmAst.Call(id, LlvmAst.ExpArgs(new_typed_exps)) ]
    | _ -> [smt]

let rec preprocess_exp_get_element_ptrs smt_list =
    match smt_list with
    | []      ->
        []

    | x :: xs ->
          (preprocess_exp_get_element_ptr x)
        @ (preprocess_exp_get_element_ptrs xs)

let preprocess_stmts stmts =
    let preprocessed_stmts = preprocess_branches stmts in
    let preprocessed_stmts = preprocess_exp_get_element_ptrs preprocessed_stmts in
        preprocessed_stmts

(* Basic Translation *)
(* ------------------------------------------------------------------------- *)
let translate_id id =
    let name = String.sub id 1 ((String.length id)-1) in
        if id.[0] == '%' then
            "var_" ^ name       (* local vars *)
        else
            name                (* global vars *)

let translate_label label =
    let name = String.sub label 1 ((String.length label)-1) in
        if label.[0] == '%' then
            "label_" ^ name     (* label *)
        else
            "label_" ^ label    (* label target *)

let translate_op op =
    match op with
    | LlvmAst.Add -> RoplAst.Add
    | LlvmAst.Sub -> RoplAst.Sub
    | LlvmAst.And -> RoplAst.And
    | LlvmAst.Mul -> RoplAst.Mul

let translate_cond id = id

let translate_func_args args =
    let LlvmAst.Args(args) = args in
        RoplAst.Args(List.map translate_id args)

(* Expression Translation *)
(* ------------------------------------------------------------------------- *)
let rec translate_exp exp =
    match exp with
    | LlvmAst.Const(v)              -> RoplAst.Const(v)
    | LlvmAst.Var(id)               -> RoplAst.Var(translate_id id)
    | LlvmAst.Bool(id)              -> RoplAst.Var(string_of_bool id)
    | LlvmAst.Load(id, align)       -> RoplAst.ReadMem(translate_id id)
    | LlvmAst.BinOp(e1, op, e2)     -> RoplAst.BinOp(translate_exp e1, translate_op op, translate_exp e2)
    | LlvmAst.BitCast(ty1, id, ty2) -> RoplAst.Var(translate_id id)
    | other                         -> raise TranslationException

let translate_typed_exp typed_exp =
    let LlvmAst.TypedExp(ty, exp) = typed_exp in
        if is_pointer ty then
            translate_exp exp
        else
            translate_exp exp

(*
 * TODO:
 *  * Rever la lista de sizes. No se está calculando bien.
 *)
let make_generator f =
    let r = ref 0 in
    let next () =
        let id = !r in
        let _ = r := !r + 1 in
        f id
    in
    next

let f_next_mul_lbl = make_generator (fun id -> "label_mul_" ^ (string_of_int id))

let f_next_mul_cnt_lbl = make_generator (fun id -> "mul_cnt_" ^ (string_of_int id))

(*
 * simulate_mul : Implementa la multiplicación mediante sumas. Se usa en el caso
 * de que no haya gadgets de multiplicación (la multiplicación impone
 * restricciones más fuertes sobre los registros ya que el resultado queda en
 * eax.)
 *)
let simulate_mul e1 e2 output_lbl =
    let iftrue_lbl       = f_next_mul_lbl () in
    let iffalse_lbl      = f_next_mul_lbl () in
    let cntr_lbl         = f_next_mul_cnt_lbl () in
    let out_init_stmt    = RoplAst.Assign(output_lbl, RoplAst.Const(0)) in
    let cnt_init_stmt    = RoplAst.Assign(cntr_lbl, RoplAst.Const(0)) in
    let iftrue_lbl_stmt  = RoplAst.Label(iftrue_lbl) in
    let add_stmt         = RoplAst.Assign(output_lbl, RoplAst.BinOp(RoplAst.Var(output_lbl), RoplAst.Add, e1)) in
    let inc_cnt_exp      = RoplAst.BinOp(RoplAst.Var(cntr_lbl), RoplAst.Add, RoplAst.Const(1)) in
    let inc_cnt_stmt     = RoplAst.Assign(cntr_lbl, inc_cnt_exp) in
    let cmp_cnt_stmt     = RoplAst.Cmp(RoplAst.Var(cntr_lbl), e2) in
    let jmp_iftrue_stmt  = RoplAst.Branch(RoplAst.Cond([RoplAst.MP]), iftrue_lbl) in
    let jmp_iffalse_stmt = RoplAst.Branch(RoplAst.Cond([RoplAst.E]), iffalse_lbl) in
    let iffalse_lbl_stmt = RoplAst.Label(iffalse_lbl) in
        [ out_init_stmt
        ; cnt_init_stmt
        ; iftrue_lbl_stmt
        ; cmp_cnt_stmt
        ; jmp_iffalse_stmt
        ; add_stmt
        ; inc_cnt_stmt
        ; jmp_iftrue_stmt
        ; iffalse_lbl_stmt
        ]

let translate_exp_get_element_ptr_offset ty typed_exp =
    let sizes           = array_type_to_size_list (remove_pointer ty) in
    let exps            = typed_exp_list_to_exp_list typed_exp in
    let offset_base_lbl = "offset" in
    let size_x_exp      = List.map2 (fun x y -> (x, y)) sizes exps in
    let rec f s_x_e acc counter =
        match s_x_e with
        | (s, e) :: tail ->
            let offset_idx_lbl   = "offset_idx_" ^ string_of_int(counter) in
            let offset_idx_stmt  = RoplAst.Assign(offset_idx_lbl, RoplAst.BinOp(RoplAst.Const(s), RoplAst.Mul, translate_exp e)) in
            (*
            (* Descomentar en caso de simular la multiplicación. *)
            let offset_idx_stmt  = simulate_mul (RoplAst.Const(s)) (translate_exp e) offset_idx_lbl in
            *)
            let offset_base_stmt = RoplAst.Assign(offset_base_lbl, RoplAst.BinOp(RoplAst.Var(offset_base_lbl), RoplAst.Add, RoplAst.Var(offset_idx_lbl))) in
            let stmts            = acc @ [ offset_idx_stmt ] @ [ offset_base_stmt ] in
            (*
            (* Descomentar en caso de simular la multiplicación. *)
            let stmts            = acc @ offset_idx_stmt @ [ offset_base_stmt ] in
            *)
                f tail stmts (counter + 1)
        | [] -> acc
    in
    let offset_stmts = f size_x_exp [] 0 in
        offset_base_lbl, offset_stmts

let translate_exp_get_element_ptr ty id exp_args assign_id =
    let trans_assign_id  = translate_id assign_id in
    let offset_lbl, offset_stmts = translate_exp_get_element_ptr_offset ty (unpack_exp_args exp_args) in
    let base             = RoplAst.Var(translate_id id) in
    let offset_init_stmt = RoplAst.Assign(offset_lbl, RoplAst.Const(0)) in
    let offset_add_stmt  = RoplAst.Assign(trans_assign_id, RoplAst.BinOp(base, RoplAst.Add, RoplAst.Var(offset_lbl))) in
    (*
        FIX: This is the correct way but this doesn't work. The problem, is most
        likely to be in the compilation problem. Something is not working when
        there are some BinOPs togheter.

          [ offset_init_stmt ]
        @ offset_stmts
        @ [ offset_add_stmt ]
    *)
    (* NOTE: This does not generate the right code, but works for limited number
             of cases.
    *)
          [ offset_init_stmt ]
        @ [ offset_add_stmt ]

let translate_exp_alloca ty align id =
    let trans_id = translate_id id in
        if is_array_type ty then
            let elem_ty = fst (unpack_array_type ty) in
                [ RoplAst.AssignTab(trans_id, generate_tab_list elem_ty) ]
        else if is_primitive_type ty then
            let pointee_var_lbl = "pointee_" ^ trans_id in
                [ RoplAst.Assign(pointee_var_lbl, RoplAst.Const(0))
                ; RoplAst.Assign(trans_id,        RoplAst.Ref(pointee_var_lbl))
                ]
        else
            failwith "Alloca : Type not supported."

let translate_exp_icmp cond e1 e2 =
    [ RoplAst.Cmp(translate_exp e1, translate_exp e2) ]

let translate_exp_call_exp id args func_table =
    let LlvmAst.ExpArgs(args) = args in
    let trans_id   = translate_id id in
    let trans_args = List.map translate_typed_exp args in
        if is_extern_function id func_table then
            [ RoplAst.Call(trans_id, RoplAst.ExpArgs(trans_args)) ]
        else
            [ RoplAst.ExtCall(trans_id, RoplAst.ExpArgs(trans_args)) ]

(* Statement Translation *)
(* ------------------------------------------------------------------------- *)
let translate_stmt_assign id exp func_table =
    match exp with
    | LlvmAst.Alloca(ty, align) ->
        translate_exp_alloca ty align id

    | LlvmAst.ICmp(cond, e1, e2) ->
        translate_exp_icmp cond e1 e2

    | LlvmAst.CallExp(call_id, args) ->
        translate_exp_call_exp call_id args func_table

    | LlvmAst.GetElementPtr(ty, gep_id, args) ->
        translate_exp_get_element_ptr ty gep_id args id

    | other ->
        [ RoplAst.Assign(translate_id id, translate_exp exp) ]

let translate_stmt_ret exp =
    [ RoplAst.Ret("id") ]

let translate_stmt_ret_void () =
    [ RoplAst.Ret("id") ]

let translate_stmt_store exp id align =
    [ RoplAst.WriteMem(translate_id id, translate_exp exp) ]

let translate_stmt_branch_u label =
    [ RoplAst.Branch(RoplAst.Cond([RoplAst.MP]), translate_label label) ]

let translate_stmt_label label =
    [ RoplAst.Label(translate_label (string_of_int label)) ]

let translate_stmt_call id args func_table =
    let LlvmAst.ExpArgs(args) = args in
        if is_intrinsic id then
            let fun_name   = get_intrinsic_name id in
            let fun_args   = translate_intrinsic_args fun_name args in
            let trans_args = List.map translate_typed_exp fun_args in
                [ RoplAst.Call("intrinsic_" ^ fun_name, RoplAst.ExpArgs(trans_args)) ]
        else
        if is_extern_function id func_table then
            [ RoplAst.Call(translate_id id, RoplAst.ExpArgs(List.map translate_typed_exp args)) ]
        else
            [ RoplAst.ExtCall(translate_id id, RoplAst.ExpArgs(List.map translate_typed_exp args)) ]

let translate_stmt_branch_c cond iftrue iffalse =
    match cond with
    | "eq" ->
        [ RoplAst.Branch(RoplAst.Cond([RoplAst.E]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.NCond([RoplAst.E]), translate_label iffalse)
        ]

    | "ne" ->
        [ RoplAst.Branch(RoplAst.Cond([RoplAst.E]),  translate_label iffalse)
        ; RoplAst.Branch(RoplAst.NCond([RoplAst.E]), translate_label iftrue)
        ]

    | "ugt" | "sgt" ->
        [ RoplAst.Branch(RoplAst.Cond([RoplAst.A]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.NCond([RoplAst.A]), translate_label iffalse)
        ]

    | "uge" | "sge" ->
        [ RoplAst.Branch(RoplAst.Cond([RoplAst.A]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.Cond([RoplAst.E]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.NCond([RoplAst.A]), translate_label iffalse)
        ]

    | "ult" | "slt" ->
        [ RoplAst.Branch(RoplAst.Cond([RoplAst.B]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.NCond([RoplAst.B]), translate_label iffalse)
        ]

    | "ule" | "sle" ->
        [ RoplAst.Branch(RoplAst.Cond([RoplAst.B]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.Cond([RoplAst.E]),  translate_label iftrue)
        ; RoplAst.Branch(RoplAst.NCond([RoplAst.B]), translate_label iffalse)
        ]

    | other ->
        raise TranslationException

(*
 * NOTA:
 *  * VoidSmt : No debería haber. Se filtraron antes de llegar acá.
 *  * BranchE : No debería haber. Se preprocesaron antes de llegar acá.
 *
 * TODO:
 *  * BranchC : Distinguir entre saltos signados y no signados.
 *)
let translate_stmt func_table stmt =
    match stmt with
    | LlvmAst.VoidStmt ->
        raise TranslationException

    | LlvmAst.Assign(id, exp) ->
        translate_stmt_assign id exp func_table

    | LlvmAst.Ret(exp) ->
        translate_stmt_ret exp

    | LlvmAst.RetVoid ->
        translate_stmt_ret_void ()

    | LlvmAst.Store(exp, id, align) ->
        translate_stmt_store exp id align

    | LlvmAst.BranchE(exp, iftrue, iffalse) ->
        raise TranslationException

    | LlvmAst.BranchU(label) ->
        translate_stmt_branch_u label

    | LlvmAst.Label(label) ->
        translate_stmt_label label

    | LlvmAst.Call(id, args) ->
        translate_stmt_call id args func_table

    | LlvmAst.BranchC(cond, iftrue, iffalse) ->
        translate_stmt_branch_c cond iftrue iffalse

(* Function Translation *)
(* ------------------------------------------------------------------------- *)
let translate_func_body func_table body =
    let LlvmAst.FunBody(stmts) = body in
    let filtered_stmts         = List.filter filter_stmt stmts in
    let preprocessed_stmts     = preprocess_stmts filtered_stmts in
    let translated_func_table  = translate_stmt func_table in
    let translated_stmts       = List.map translated_func_table preprocessed_stmts in
    let translated_func_body   = List.concat translated_stmts in
        RoplAst.FunBody(translated_func_body)

let translate_func_list func_table func_list =
    let LlvmAst.Fun(id, args, body) = func_list in
    let trans_id   = translate_id id in
    let trans_args = translate_func_args args in
    let trans_body = translate_func_body func_table body in
        RoplAst.Fun(trans_id, trans_args, trans_body)

let generate_tab_list_from_string s =
    let remove_first_char s =
        if s.[0] == '\\' then
            let chr   = int_of_string ("0x" ^ (Char.escaped s.[1]) ^ (Char.escaped s.[2])) in
            let new_s = String.sub s 3 (String.length s - 3) in
                chr, new_s
        else
            let chr   = Char.code s.[0] in
            let new_s = String.sub s 1 (String.length s - 1) in
                chr, new_s
    in
    let rec apply_fn s chars =
        if String.length s != 0 then
            let chr, new_s = remove_first_char s in
                apply_fn new_s (chars @ [ chr ])
        else
            chars
    in
    apply_fn s []

(*
 * NOTA:
 *  * Actualmente, solo se soportan variables (globales) de tipo string.
 *)
let init_globals globals =
    let process_global global =
        let LlvmAst.GlobalVarStr(id, value) = global in
        let trans_id    = translate_id id in
        let trans_value = generate_tab_list_from_string value in
            RoplAst.AssignTab(trans_id, trans_value)
    in
    List.map process_global globals

let add_global_stmts globals funs =
    let apply_fn func =
        match func with
        | RoplAst.Fun("main", args, RoplAst.FunBody(stmt_list)) ->
            RoplAst.Fun("main", args, RoplAst.FunBody(globals @ stmt_list))

        | _ -> func
    in
    List.map apply_fn funs

let translate_prog prog =
    let LlvmAst.Prog(target_info_list, globals_list, func_list, declare_func_list) = prog in
    let global_vars_stmts      = init_globals globals_list in
    let ropl_funs              = List.map (translate_func_list (build_func_table func_list)) func_list in
    let ropl_funs_with_globals = add_global_stmts global_vars_stmts ropl_funs in
        RoplAst.Prog(ropl_funs_with_globals)
