open Symbeval

open Common
open GadgetSet

let hALT = Ast.Halt(Ast.exp_true, [])

(*
 * Gadget Classification
 *)
(* Performs gadget classification. *)
(* g_list : (f_init, f_finish, mem_hax, repeats) list *)
(* cand : candidate *)
let classify g_list cand =
    (* stmts : Ast.stmt list *)
    let Cand((off_s,off_e), stmts) = cand in

    (* let org_stmts = stmts in *)
    let add_halt stmts =
        stmts @ [hALT]
    in

    (* Agrega la instrucción Halt a lista de sentencias que componen un
    candidato a gadget. *)
    let stmts = add_halt stmts in

    (* cinit es el "prólogo" común a todos los gadgets. *)
    let cinit = GadgetClassifierHelper.common_init stmts in

    let f acc g_func =
        let empty_set = GadgetSet.empty in
        let (_, _, _, repeats) = g_func () in

        (* Ejecución simbólica de un candidato con el fin de averiguar qué
            tipo de gadget es. *)
        (* concrete execution *)
        let co_exec (gset,_,_) i =
            (* g_func might want to initiate regs/mem to random values with each run,
               so this is necessary. computing the tuple just once would make the registers constant *)
            let (f_init, f_finish, mem_hax, _) = g_func () in
            let init = f_init stmts in (* FIXME: should return init, stmts? *)
            let init = cinit @ init in
            (* val concretely_execute : ?s:int64 -> ?i:Ast.stmt list -> ?mem_hax:bool -> instr list -> ctx *)
            let ctx = Symbeval.concretely_execute ~i:init ~mem_hax:mem_hax (stmts) in
            (* Retorna los gadgets junto con los registros que modificaron cada
            uno durante la ejecución simbólica. Para esto se utiliza el contexto
            final de la ejecución. *)
            let gadgets, mod_regs = f_finish ctx in
            let gset_new = gadget_set_of_list gadgets in
            (* Si hay más de una repetición de ejecución simbólica, se intersecan
            los conjuntos de gadgets obtenidos para quedarse con los "válidos". *)
            let gset = if i=0 then gset_new else GadgetSet.inter gset gset_new in
            (* mod_regs are going to be verified later, so we don't have to be very precise *)
            gset, mod_regs, Some(ctx)
        in
        let range = Util.mapn (fun x->x) (repeats-1) in (* len(range) = repeats *)
        let (gset, mod_regs, ct) = List.fold_left co_exec (empty_set, [], None) range in
        let ctx =
            match ct with
            | Some(ctx) -> ctx
            | None -> assert false
        in
        let gadgets = GadgetSet.elements gset in

        (* we are not saving stmts, because marshaling them doesn't work for some reason *)
        (* verifier will not accept Halt/Special statements *)
        let wrapped = GadgetClassifierHelper.wrap_meta ctx gadgets mod_regs off_s off_e in
        wrapped::acc
    in
    let gadgets = List.fold_left f [] g_list in
    let gadgets = List.concat gadgets in
    gadgets

(* GadgetClassifierHelper.g_list es una lista de funciones que ayuda a reconocer tipos de
gadgets. *)
let make_classify = classify (GadgetClassifierHelper.g_list ());;

let classify_candidates cands =
    let classify = make_classify in
    let gmetas = List.map (fun cand -> classify cand) cands in
    let gmetas = List.concat gmetas in
    gmetas
