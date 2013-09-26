open Printf

open Common
open SsaForm

let cRASH_ADDRESS = 0x1111

(* Escribe en io, la dir del gadget. *)
let to_binary_one io (instr,gm) =
    let get_lc_off g =
        match g with
        | LoadConst(_,off) -> off
        | _ -> assert false
    in
    let fill io n =
        let dwords = n / 4 in
        let bytes = n mod 4 in
        let rec aux i f m =
            if i < m then
                let _ = f n io in aux (i+1) f m
            else ()
        in
        let f_d n io = IO.write_i32 io n in
        let f_b n io = IO.write_byte io n in
        let _ = aux 0 f_d dwords in
        let _ = aux dwords f_b (dwords+bytes) in
        ()
    in
    let value_to_write instr off_s =
        match instr with
        | RawHex(v) -> v
        | _ -> off_s
    in
    let GMeta(g, fm, _, stack_fix) = gm in
    let FileMeta(off_s, _) = fm in
    (* ??? *)
    let v = value_to_write instr off_s in
    let _ = IO.write_i32 io v in

    let _ =
        match instr with
        | MovRegConst(r,v) ->
                let off = get_lc_off g in
                let _ = assert (stack_fix - off - 4 >= 0) in
                let _ = fill io off in
                let _ = IO.write_i32 io v in
                fill io (stack_fix - off - 8)
        | RawHex(_) -> assert (stack_fix = 4)
        | _ -> fill io (stack_fix-4)
    in
    (* return string *)
    ()

(* Escribe un io la dirs de los gadgets. *)
let to_binary pairs =
    let io = IO.output_string () in
    let consume acc (instr,gm) =
        to_binary_one io (instr,gm)
    in
    let _ = List.fold_left consume () pairs in
    (* Escribe en io la crash_address 7 veces. *)
    let _ = List.map (fun i -> IO.write_i32 io cRASH_ADDRESS) [1;2;3;4;5;6;7] in
    IO.close_out io