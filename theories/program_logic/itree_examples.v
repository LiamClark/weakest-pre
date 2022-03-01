From stdpp Require Import base. 
From shiris.program_logic Require Import itree evaluation itreewp.

Definition prog_swap  (l k: nat): expr nat unit := 
    x ← itree.get l ;
    y ← itree.get k ;
    itree.put l y ;; itree.put k x.

Definition loop_body {A}: unit -> expr nat A :=
  itree.iter (λ x, mret $ inl ()).

Definition loop_prog {A}: expr nat A :=
    loop_body ().
