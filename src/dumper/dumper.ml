open Printf

open Common

(** Gadget Dumper Tool *)

let main () =
    let argc = Array.length Sys.argv in

    if argc > 1 then
        let fn = Sys.argv.(1) in
        let container = Common.unmarshal_from_file fn in
        let b = dump_container container in
        Buffer.output_buffer stdout b
    else
        (* Print usage message *)
        let err = Printf.sprintf "Usage:\n%s <bin file>\n" Sys.argv.(0) in
        print_string err

let _ = main()
