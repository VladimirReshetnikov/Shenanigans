(** * rocq#22164 — half one: compiled WITH `-impredicative-set`.

    `impred_def` quantifies over all of `Set` and lands in `Set`, which needs
    the flag. *)
Definition impred_def : Set := forall X : Set, X -> X.
