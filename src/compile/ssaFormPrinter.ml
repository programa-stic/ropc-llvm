open Printf

open Common
open RegSets
open RoplAst
open SsaForm

(* Dump functions *)
let dump_dir = function
    | Forward -> "@f"
    | Backward -> "@b"

let dump_symb = function
    | Named(id) -> sprintf "Named(%s)" id
    | Unnamed(direction) -> sprintf "Unnamed(%s)" (dump_dir direction)

let dump_sreg = function
    | S(id) -> sprintf "r%d" (id)
    | C(r) -> (dump_reg r)

let dump_instr = function
    (* T0 *)
    | AdvanceStack(n)           -> sprintf "esp += %d" n
    | RawHex(n)                 -> sprintf "hex(0x%08x)" n
    | MovRegConst(r,c)          -> sprintf "%s = 0x%08x" (dump_sreg r) c
    | MovRegReg(r1,r2)          -> sprintf "%s = %s" (dump_sreg r1) (dump_sreg r2)
    | MovRegSymb(r,FromTo(s,f)) -> sprintf "%s = (from: %s, to: %s)" (dump_sreg r) (dump_symb s) (dump_symb f)
    | WriteM(r1,r2)             -> sprintf "[%s] = %s" (dump_sreg r1) (dump_sreg r2)
    | ReadM(r1,r2)              -> sprintf "%s = [%s]" (dump_sreg r1) (dump_sreg r2)
    | SaveFlags                 -> sprintf "SaveFlags"
    | OpStack(op, r)            -> sprintf "esp = esp %s %s" (dump_op op) (dump_sreg r)
    | BinO(ro,r1,op,r2)         -> sprintf "%s = %s %s %s" (dump_sreg ro) (dump_sreg r1) (RoplAst.dump_op op) (dump_sreg r2)
    (* T1 *)
    | ReadMConst(r,addr)        -> sprintf "%s = [0x%08x]" (dump_sreg r) addr
    | WriteMConst(addr,r)       -> sprintf "[0x%08x] = %s" addr (dump_sreg r)
    (* T2 *)
    | LocalAddr(off,r)          -> sprintf "%s = &local(%d)" (dump_sreg r) off
    | PushReg(r)                -> sprintf "push(%s)" (dump_sreg r)
    | PopReg(r)                 -> sprintf "pop(%s)" (dump_sreg r)
    (* T3 *)
    | ReadLocal(off,r)          -> sprintf "%s = *local(%d)" (dump_sreg r) off
    | WriteLocal(off,r)         -> sprintf "*local(%d) = %s" off (dump_sreg r)
    | Lbl(id)                   -> sprintf "%s:" id
    | Comment(s)                -> sprintf ";%s" s

let dump_sreg_set set =
    let sregs = SRegSet.elements set in
    let _ = Common.generic_dumper (fun r -> dump_sreg r) sregs in
    ()

let dump_reg_set set =
    let regs = RegSet.elements set in
    let _ = Common.generic_dumper (fun r -> dump_reg r) regs in
    ()

let arg_dumper instr =
    match instr with
    | AdvanceStack(_) -> []
    | RawHex(_) -> []
    | MovRegConst(a1,_) -> [a1]
    | MovRegReg(a1,a2) -> [a1;a2]
    | MovRegSymb(a1,_) -> [a1]
    | WriteM(a1,a2) -> [a1;a2]
    | ReadM(a1,a2) -> [a1;a2]
    | SaveFlags -> []
    | OpStack(_,a1) -> [a1]
    | BinO(a1,a2,_,a3) -> [a1;a2;a3]

    | ReadMConst(a1,_)
    | WriteMConst(_,a1) -> [a1]

    | LocalAddr(_,a1)
    | PushReg(a1)
    | PopReg(a1) -> [a1]

    | ReadLocal(_,a1)
    | WriteLocal(_,a1) -> [a1]
    | Lbl(_)
    | Comment(_) -> []
