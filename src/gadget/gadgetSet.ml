open Common

module GadgetSet = Set.Make(
    struct
        let compare = Pervasives.compare
        type t = gadget
    end
)

let gadget_set_of_list = List.fold_left (fun acc x -> GadgetSet.add x acc) GadgetSet.empty
