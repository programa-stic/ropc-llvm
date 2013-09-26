open Common
open SsaForm

module RegOrder = struct
    type t = reg
    let compare = Pervasives.compare
end

module RegSet = Set.Make( RegOrder )

module SRegOrder = struct
    type t = sreg
    let compare = Pervasives.compare
end

module SRegSet = Set.Make( SRegOrder )

let set_from_list l =
    let f set x = RegSet.add x set in
    List.fold_left f RegSet.empty l

let sreg_set_from_list l =
    let f set x = SRegSet.add x set in
    List.fold_left f SRegSet.empty l

let common_reg_set_to_sreg_set set =
    let l = RegSet.elements set in
    let l = List.map (fun r -> C(r)) l in
    let set = sreg_set_from_list l in
    set
