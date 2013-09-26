open Common
open Int_utils

let mAX_BYTES_BACKWARD = 10

(*
 * Gadget Discovery
 *)
(* scan for RETs *)
(* Retorna una lista enteros, que representa la posición de cada RET
encontrado. *)
let scan_section get s s_start s_end =
    let l = ref [] in
    let _ =
    for i=s_start to s_end-1 do
        let j = Int64.of_int i in
        let b = get j in
        if b = char_of_int 0xC3 then
            l := i::!l
        else
            ()
    done
    in
    !l

(* Especialización de scan_section para función de get_byte particular. *)
let make_scan get = scan_section get

(* Retorna un Ast.Program extraído del programa prog entre la posición i y j. *)
let get_range_prog prog i j =
    let (i,j) = cast_range i j in
    let l = Asmir.asmprogram_to_bap_range prog i j in
    l

(* Especialización de get_range_prog para un programa particular. *)
let make_get_range prog = get_range_prog prog

(* Retorna una lista (candidate start, candidate end) de los candidatos a
    gadgets. *)
(* positions must be sorted increasingly *)
let convert prog positions s_start =
    let get_range = make_get_range prog in
    let get_small_range prev_pos pos =
        let f i =
            let s = (pos-i) in
            let e = pos+1 in (* +1 for RET (0xc3) *)
            let stmts = get_range s e in
            Cand((s,e), stmts)
        in
        let n = min mAX_BYTES_BACKWARD (pos - prev_pos - 1) in
        let _ = if n<0 then failwith "seems like an unsorted positions list" else () in
        (* return list of ranges [[..], [..], ...] *)
        Util.mapn f n
    in
    let f (acc, prev_pos) pos =
        let l = get_small_range prev_pos pos in
        (l::acc, pos)
    in
    let _ = Printf.printf "s_start = 0x%08x\n" s_start in
    let (ranges, _) = List.fold_left f ([], s_start) positions in
    List.concat ranges

(* Especializa la función convert para un programa dado. *)
let make_convert prog = convert prog

(* Filtra secciones de un programa. *)
let filter_sections prog f =
    let sections = Asmir.get_all_asections prog in
    let sections = Array.to_list sections in
    let sections = List.filter f sections in
    sections

(* Retorna una lista de (section, section start, section end) *)
let sec_start_end sections =
    let ss s = Asmir.get_section_start s in
    let se s = Asmir.get_section_end s in
    let f s = (s, safe_to_int64 (ss s), safe_to_int64 (se s)) in
    let triples = List.map f sections in
    triples

(* Busca candidatos a gadgets en todas las secciones ejecutables de prog. *)
let candidates_all_sections prog =
    let sections = filter_sections prog Asmir.is_code in
    let get = Asmir.get_prog_contents prog in
    (* triples = (section, section_start, section_end)*)
    let triples = sec_start_end sections in
    (*let _ = test_get get in*)
    let scan = make_scan get in
    let f (s,ss,se) =
        (* Input: *)
            (* s  : section *)
            (* ss : section start *)
            (* se : section end *)
        (* Ouptut: *)
            (* (s, positions, ss) *)

        (* RETs positions in section s *)
        let positions = scan s ss se in
        let positions = List.sort compare positions in
        (s, positions, ss)
    in
    (* sec_positions = (section, positions, section_start) *)
    let sec_positions = List.map f triples in
    let convert_to_bap = make_convert prog in
    let f (s, positions, s_start) =
        let ranges = convert_to_bap positions s_start in
        (s, ranges)
    in
    let sec_ranges = List.map f sec_positions in
    let ranges = List.map (fun (x,y) -> y) sec_ranges in
    let ranges = List.concat ranges in
    ranges
(*
    (* just test *)
    if !g_start > 0 && !g_end > !g_start then
        let s,e = (!g_start, !g_end) in
        let l = get_range_prog prog s e in
        let c = Cand((s,e),l) in
        let ranges = [c] in
        ranges
    else
        ranges
*)

(* Función de filtrado de desensamblado incorrecto. *)
(* Special() is a sign of disasm error, execution will fail on these *)
let good_disasm stmts =
    let p x =
        match x with
        | Ast.Halt(_,_)
        | Ast.Special(_,_) ->
            true
        | _ -> false
    in
    let trash = List.exists p stmts in
    not trash

(* Función de filtrado de jumps. *)
(*  don't allow ANY jumps.
    incomplete, but sufficient, to avoid infinite loops *)
let no_jumps stmts =
    let p x =
        match x with
        | Ast.Jmp(_,_)
        | Ast.CJmp(_,_,_,_) ->
            true
        | _ -> false
    in
    let trash = List.exists p stmts in
    not trash

(* filter bad disasms and potential infinite loops *)
let filter_candidates candidates =
    (* get stmts *)
    let gs cand = let Cand(_,stmts) = cand in stmts in
    let fm cand = let Cand(m,_) = cand in m in
    let candidates = List.filter (fun c -> good_disasm (gs c)) candidates in
    (* RET gets split into few instructions, last of them being jmp *)
    let candidates = List.map (fun c -> Cand(fm c, Common.drop_last (gs c))) candidates in
    let candidates = List.filter (fun c -> no_jumps (gs c)) candidates in
    candidates

let find_candidates prog =
    (* Busca posibles gadget *)
    let candidates = candidates_all_sections prog in
    (* Descarta aquellos candidatos que no son gadget por no haber
    desensamblado correctamente o por tener saltos. *)
    let candidates = filter_candidates candidates in
    candidates
