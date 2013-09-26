open LlvmAst

let id = fun x->x

let str_fold f l sep =
    let s = List.fold_left (fun acc s -> acc ^ f s ^ sep) "" l in
    if String.length s > 0 then
        String.sub s 0 (String.length s - 1)
    else
        s

let print_op op =
    match op with
    | Add -> "Add"
    | Sub -> "Sub"
    | And -> "And"
    | Mul -> "Mul"

let rec print_exp exp =
    match exp with
    | Const(x) -> Printf.sprintf "Const(%s)" (string_of_int x)
    | Var(x) -> Printf.sprintf "Var(%s)" x
    | Bool(x) -> Printf.sprintf "Bool(%B)" x
    | BinOp(e1, op, e2) -> Printf.sprintf "BinOp(%s, %s, %s)" (print_exp e1) (print_op op) (print_exp e2)
    | Alloca(e1, e2) -> Printf.sprintf "Alloca(%s, %s)" e1 (string_of_int e2)
    | Load(e1, e2) -> Printf.sprintf "Load(%s, %s)" e1 (string_of_int e2)
    | ICmp(e1, e2, e3) -> Printf.sprintf "ICmp(%s, %s, %s)" e1 (print_exp e2) (print_exp e3)
    | VoidExp -> Printf.sprintf "Void"
    | BitCast(e1, e2, e3) -> Printf.sprintf "BitCast(%s, %s, %s)" e1 e2 e3
    | GetElementPtr(ty, id, typed_exp_list) -> Printf.sprintf "GetElementPtr(%s, %s, %s)" ty id (print_exp_args typed_exp_list)
    | CallExp(name, exp_args) -> Printf.sprintf "CallExp(%s, %s)" name (print_exp_args exp_args)

and print_typed_exp typed_exp =
    match typed_exp with
    | TypedExp(ty, exp) -> Printf.sprintf "TypedExp(%s, %s)" ty (print_exp exp)

and print_exp_args args =
    match args with
    | ExpArgs(args) ->
        let s_args = str_fold print_typed_exp args "," in
        s_args

let rec print_stmt stmt =
    match stmt with
    | Assign(id, exp) -> Printf.sprintf "Assign(%s, %s)" id (print_exp exp)
    | Ret(exp) -> Printf.sprintf "ret(%s)" (print_exp exp)
    | RetVoid -> Printf.sprintf "ret void"
    | VoidStmt -> Printf.sprintf ""
    | Store(exp, id, align) -> Printf.sprintf "Store(%s, %s, %s)" (print_exp exp) id (string_of_int align)
    | BranchE(exp, id_iftrue, id_iffalse) -> Printf.sprintf "BranchE(%s, %s, %s)" (print_exp exp) id_iftrue id_iffalse
    | BranchC(cond, id_iftrue, id_iffalse) -> Printf.sprintf "BranchC(%s, %s, %s)" cond id_iftrue id_iffalse
    | BranchU(id) -> Printf.sprintf "Branch(%s)" id
    | Label(id) -> Printf.sprintf "Label(%s)" (string_of_int id)
    | Call(name, exp_args) -> Printf.sprintf "Call(%s, %s)" name (print_exp_args exp_args)

let print_args args =
    match args with
    | Args(args) ->
        let s_args = str_fold id args "," in
        s_args

let print_body body =
    match body with
    | FunBody(stmt_list) -> str_fold print_stmt stmt_list "\n"

let print_func_head f =
    match f with
    | Fun(id, args, _) ->
        let s_args = print_args args in
        let s = Printf.sprintf "# Fun: %s, args: %s" id s_args in
        s

let print_func f =
    match f with
    | Fun(id, args, body) ->
        let head = print_func_head f in
        let s_body = print_body body in
        let s = Printf.sprintf "%s\n%s\n" head s_body in
        s

let print_declare_func_head f =
    match f with
    | DeclareFun(id, args) ->
        let s_args = print_args args in
        let s = Printf.sprintf "# DeclareFun: %s, args: %s" id s_args in
        s

let print_declare_func f =
    match f with
    | DeclareFun(id, args) ->
        let head = print_declare_func_head f in
        let s = Printf.sprintf "%s\n" head in
        s

let print_globals var =
    match var with
    | GlobalVarStr(id, str) -> Printf.sprintf "GlobalVarStr(%s, %s)\n" id str

let print_target_info var =
    match var with
    | TargetInfo(id, str) -> Printf.sprintf "TargetInfo(%s, %s)\n" id str

let print_prog p =
    match p with
    | Prog(target_info_list, globals_list, func_list, declare_func_list) ->
    begin
        let s =
            Printf.sprintf "#\n" ^
            Printf.sprintf "# Target info list:\n" ^
            Printf.sprintf "#\n\n" ^
            Printf.sprintf "%s\n" (str_fold print_target_info target_info_list "\n") ^
            Printf.sprintf "#\n" ^
            Printf.sprintf "# Global var list:\n" ^
            Printf.sprintf "#\n\n" ^
            Printf.sprintf "%s\n" (str_fold print_globals globals_list "\n") ^
            Printf.sprintf "#\n" ^
            Printf.sprintf "# Funtion list:\n" ^
            Printf.sprintf "#\n\n" ^
            Printf.sprintf "%s\n" (str_fold print_func func_list "\n") ^
            Printf.sprintf "#\n" ^
            Printf.sprintf "# Declare funtion list:\n" ^
            Printf.sprintf "#\n\n" ^
            Printf.sprintf "%s\n" (str_fold print_declare_func declare_func_list "\n") in
        s
    end
