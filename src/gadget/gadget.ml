open Printf
open Sys

open Common
open GadgetClassifier
open GadgetFinder
open Int_utils

(** Gadget Finder Tool *)

(*
 * Descripción general:
 *  1. Genera una lista de las posiciones de todos los RET's.
 *
 *  2. Para cada posición RET, genera una lista de Ast.Program's
 *  (Ast.Program == Ast.stmt list). Tiene en cuenta el rango
 *  [pos RET - mAX_BYTES_BACKWARD, pos RET].
 *
 *  3. Filtra los candidatos que incluyen ciclos y los que no se pudieron
 *  desensamblar correctamente. En el punto 2 se generan listas de bytes
 *  que pueden o no ser listas de instrucciones.
 *
 *  4. Mediante ejecución simbólica, clasifica cada uno de los candidatos
 *  en cada tipo de gadget soportado.
 *)

(* Retorna una lista de (section, section start, section end) *)
let sec_start_end sections =
    let ss s = Asmir.get_section_start s in
    let se s = Asmir.get_section_end s in
    let f s = (s, safe_to_int64 (ss s), safe_to_int64 (se s)) in
    let triples = List.map f sections in
    triples

(* Filtra secciones de un programa. *)
let filter_sections prog f =
    let sections = Asmir.get_all_asections prog in
    let sections = Array.to_list sections in
    let sections = List.filter f sections in
    sections

(* Find biggest bss section in a program *)
let biggest_rw_data prog =
    let datas = filter_sections prog Asmir.is_bss in
    let sse = sec_start_end datas in
    let sse = List.map (fun (_,s,e) -> (e-s,s,e)) sse in
    let cmp (s1,_,_) (s2,_,_) = compare s1 s2 in
    let sorted = List.sort cmp sse in
    let sorted = List.map (fun (_,s,e) -> (s,e)) sorted in
    let data = List.nth sorted ((List.length sorted)-1) in
    data

(* Parsea un ejecutable y extrae todos los gadgets encontrados. *)
(* Retorna:
 *  gmetas = (gadget, file meta, modified registers, stack_fix) list
 *  data = (section start, section end)
 *)
let parse_exe fn =
    (* Abre programa *)
    let prog = Asmir.open_program fn in

    (* Busca posibles gadget descartando aquellos candidatos que no son
        gadget por no haber desensamblado correctamente o por tener saltos. *)
    let candidates = find_candidates prog in

    (* Clasifica a los gadget de acuerdo a su tipo:
        * copy_reg; binop; load_const; write_mem; read_mem; read_mem_op;
        write_mem_op; lahf; opesp; *)
    let gmetas = classify_candidates candidates in

    (* Encuentra la mayor sección bss que usará para área de datos.
        data = (section start, section end) *)
    let data = biggest_rw_data prog in
    gmetas, data

(* Crea un GContainer con fn, gmetas y data. *)
let wrap_in_container fn gmetas data =
    let cont = Common.GContainer(fn, data, gmetas) in
    cont

let parse_and_save fn ofn =
    let gmetas, data = parse_exe fn in
    let container = wrap_in_container fn gmetas data in
    Common.marshal_to_file ofn container

let main () =
    let argc = Array.length Sys.argv in

    if argc > 1 then
        let fn = Sys.argv.(1) in
        let ofn =
            if argc = 3 then
                Sys.argv.(2)
            else
                assert false
        in
        parse_and_save fn ofn
    else
        (* Print usage message *)
        let err = Printf.sprintf "Usage:\n%s <exe file> <out candidates file>\n" Sys.argv.(0) in
        print_string err

let _ = main()
