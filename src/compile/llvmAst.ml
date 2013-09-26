type ty = string

type id = string

type align = int

type cond = string

type operator =
	  Add
	| Sub
	| And
	| Mul

type exp =
	  BinOp of exp * operator * exp
	| Const of int
	| Bool of bool
	| Var of id
	| Alloca of ty * align
	| Load of id * align
	| ICmp of cond * exp * exp
	| VoidExp
	| BitCast of ty * id * ty
	| GetElementPtr of ty * id * exp_args
	| CallExp of id * exp_args
and typed_exp = TypedExp of ty * exp
and exp_args = ExpArgs of typed_exp list

type stmt =
	  Assign of id * exp
	| VoidStmt
	| Ret of exp
	| RetVoid
	| Store of exp * id * int
	| BranchE of exp * id * id
	| BranchC of cond * id * id
	| BranchU of id
	| Label of int
	| Call of id * exp_args

type args = Args of id list

type func_body = FunBody of stmt list

type func = Fun of id * args * func_body

type declare_func = DeclareFun of id * args

type metadata = Metadata of string * string

type target_info = TargetInfo of id * string

type globals = GlobalVarStr of id * string

type program = Prog of target_info list * globals list * func list * declare_func list
