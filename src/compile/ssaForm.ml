open Common
open RoplAst

(*
 * SSA Form
 *)

type direction = Forward | Backward

(* offsets of labels can't be computed early, so use a marker to describe them.
 * offset from begining of the function/payload *)
type symb_simple =
    (* local labels are prefixed with func name, so all searches can be global *)
    | Named of id
    | Unnamed of direction (* always local *)

(* (start, end) - what's the distance from label "start" to label "end" ? *)
type symb =
    | FromTo of symb_simple * symb_simple

(* symbolic(id), concrete(reg) *)
type sreg = S of int | C of reg

type instr =
    (* T0 *)
    | AdvanceStack of int
    | RawHex of int
    | MovRegConst of sreg * int             (* sreg <- const *)
    | MovRegReg of sreg * sreg              (* dst <- src *)
    | MovRegSymb of sreg * symb
    | WriteM of sreg * sreg                 (* [addr_reg] <- src *)
    | ReadM of sreg * sreg                  (* dst <- [addr_reg] *)
    | SaveFlags
    | OpStack of operator * sreg
    | BinO of sreg * sreg * operator * sreg
    (* T1 *)
    | ReadMConst of sreg * int              (* dst <- [const] *)
    | WriteMConst of int * sreg (* [const] <- src *)
    (* dst_reg <- stack_frame+off, off is precalc. during compilation *)
    (* T2 *)
    | LocalAddr of int * sreg
    | PushReg of sreg                       (* push sreg on emu stack *)
    | PopReg of sreg                        (* pop sreg from emu stack *)
    (* T3 *)
    | ReadLocal of int * sreg               (* dst <- local_var(i) *)
    | WriteLocal of int * sreg              (* local_var(i) <- src *)
    | Lbl of id
    | Comment of string                     (* store deleted instructions as comments *)

type ityp = T0 | T1 | T2 | T3

let make_generator f =
    let r = ref 0 in
    let next () =
        let id = !r in
        let _ = r := !r + 1 in
        f id
    in
    next

let make_reg_generator () = make_generator (fun id -> S(id))
