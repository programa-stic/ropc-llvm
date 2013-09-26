%{

open LlvmAst

%}

/*** Declarations ***/

/* Symbols */
%token EQ
%token COMMA
%token LPAREN RPAREN
%token LCURLY RCURLY
%token LBRACKET RBRACKET

/* Bitwise Binary Operations */
%token AND

/* Binary Operations */
%token ADD
%token SUB
%token MUL

/* Terminator Instructions */
%token RET
%token BR

/* Memory Access and Addressing Operations */
%token ALLOCA
%token STORE
%token LOAD
%token GETELEMENTPTR

/* Other Instructions */
%token ICMP
%token CALL
%token FUN
%token DECLARE

/* Conversion Operations */
%token BITCAST

/* Miscellaneous */
%token EOF
%token ALIGN
%token I1
%token LABEL
%token LABEL_TARGET
%token <string> SIGN
%token <string> COND
%token <int> NUM
%token <string> ID
%token <bool> BOOL
%token <string> TYPE
%token <string> CSTR
%token <string> STR
%token TO
%token INBOUNDS
%token ELLIPSIS
%token PRIVATE
%token UNNAMED_ADDR
%token CONSTANT

/* Function Attributes */
%token NOUNWIND
%token UWTABLE

/* Parameters Attributes */
%token NOCAPTURE

/* Target Information */
%token TARGET

%start input

%type <LlvmAst.program> input


/*** Grammar rules ***/
%%
param_attr:
    |                                               { "" }
    | NOCAPTURE                                     { "nocapture" }

ty:
    | TYPE                                          { $1 }
;

ty_list:
    | ty_list COMMA ELLIPSIS                        { "..."::$1 }
    | ty_list COMMA ty                              { $3::$1 }
    | ty_list COMMA ty param_attr                   { $3::$1 }
    | ty                                            { [$1] }
    | ty param_attr                                 { [$1] }
    |                                               { [] }
;

fun_ty:
    |                                               { "" }
    | LPAREN ty_list RPAREN                         { String.concat ", " (List.rev $2) }
;

sign:
    |                                               { "" }
    | SIGN                                          { $1 }
;

exp:
    | ID                                            { Var($1) }
    | NUM                                           { Const($1) }
    | BOOL                                          { Bool($1) }

    /* Bitwise Binary Operations */
    | AND ty exp COMMA exp                          { BinOp($3, And, $5) }

    /* Binary Operations */
    | ADD sign sign ty exp COMMA exp                { BinOp($5, Add, $7) }
    | SUB sign sign ty exp COMMA exp                { BinOp($5, Sub, $7) }
    | MUL sign sign ty exp COMMA exp                { BinOp($5, Mul, $7) }

    /* Memory Access and Addressing Operations */
    | ALLOCA ty COMMA ALIGN NUM                                         { Alloca($2, $5) }
    | LOAD ty ID COMMA ALIGN NUM                                        { Load($3, $6) }
    | LOAD ty ID                                                        { Load($3, 0) }
    | GETELEMENTPTR INBOUNDS ty ID COMMA exp_args_list                  { GetElementPtr($3, $4, ExpArgs(List.rev $6)) }
    | GETELEMENTPTR INBOUNDS LPAREN ty ID COMMA exp_args_list RPAREN    { GetElementPtr($4, $5, ExpArgs(List.rev $7)) }

    /* Other Instructions */
    | ICMP COND ty exp COMMA exp                    { ICmp($2, $4, $6) }
    | CALL ty fun_ty ID exp_args                    { CallExp($4, $5) }

    /* Conversion Operations */
    | BITCAST ty ID TO ty                           { BitCast($2, $3, $5) }
;

stmt:
    /* Miscellaneous */
    | ID EQ exp                                     { Assign($1, $3) }
    | LABEL_TARGET NUM                              { Label($2) }

    /* Memory Access and Addressing Operations */
    | STORE ty exp COMMA ty ID COMMA ALIGN NUM      { Store($3, $6, $9) }
    | STORE ty exp COMMA ty ID                      { Store($3, $6, 0) }

    /* Terminator Instructions */
    | BR ty exp COMMA LABEL ID COMMA LABEL ID       { BranchE($3, $6, $9) }
    | BR LABEL ID                                   { BranchU($3) }
    | RET ty exp                                    { Ret($3) }
    | RET ty                                        { RetVoid }

    /* Other Instructions */
    | CALL ty ID exp_args                           { Call($3, $4) }
;

stmt_list:
    | stmt_list stmt                                { $2::$1 }
    | stmt                                          { [$1] }
;

args_list:
    | args_list COMMA ty ID                         { $4::$1 }
    | ty ID                                         { [$2] }
    |                                               { [] }
;

exp_args_list:
    | exp_args_list COMMA ty exp                    { TypedExp($3, $4)::$1 }
    | ty exp                                        { [TypedExp($1, $2)] }
    |                                               { [] }
;

exp_args:
    | LPAREN exp_args_list RPAREN                   { ExpArgs(List.rev $2) }
;

args:
    | LPAREN args_list RPAREN                       { Args(List.rev $2) }
;

declare_func:
    | DECLARE ty ID LPAREN ty_list RPAREN func_attrs
    {
        DeclareFun($3, Args([]))
    }
;

declare_func_list:
    | declare_func_list declare_func                { $2::$1 }
    | declare_func                                  { [$1] }
    |                                               { [] }
;

func_body:
    | LCURLY stmt_list RCURLY                       { FunBody(List.rev $2) }
;

func_attr:
    | NOUNWIND                                      { "nounwind" }
    | UWTABLE                                       { "uwtable" }

func_attrs:
    | func_attrs func_attr                          { $2::$1 }
    |                                               { [] }

func:
    | FUN ty ID args func_attrs func_body           { Fun($3, $4, $6) }
;

func_list:
    | func_list func                                { $2::$1 }
    | func                                          { [$1] }
;

var_value:
    | CSTR                                          { $1 }

linkage_type:
    | PRIVATE                                       { "private" }

global_var_attr:
    | UNNAMED_ADDR                                  { "unnamed_addr" }
    | CONSTANT                                      { "constant" }

global_var_attr_list:
    | global_var_attr_list global_var_attr          { $2::$1 }
    | global_var_attr                               { [$1] }
    |                                               { [] }

global_var:
    | ID EQ linkage_type global_var_attr_list ty var_value COMMA ALIGN NUM
    {
        GlobalVarStr($1, $6)
    }

global_var_list:
    | global_var_list global_var                    { $2::$1 }
    | global_var                                    { [$1] }
    |                                               { [] }

/* TODO: Cambiar ty por id. */
target_info:
    | TARGET ty EQ STR                              { TargetInfo($2, $4) }

target_info_list:
    | target_info_list target_info                  { $2::$1 }
    | target_info                                   { [$1] }
    |                                               { [] }

input:
    | EOF                                           { Prog([], [], [], []) }

    | target_info_list global_var_list func_list declare_func_list
    {
        Prog(List.rev $1, List.rev $2, List.rev $3, List.rev $4)
    }
;


/*** Trailer ***/
%%
