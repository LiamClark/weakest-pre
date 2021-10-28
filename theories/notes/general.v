
From stdpp Require Import base.

(* McBrides definition for his free-er general monad  *)
Inductive General (S: Type) (T: S -> Type) (X: Type) : Type :=
  | greturn : X -> General S T X
  | gask : ∀(s: S), (T s -> General S T X) -> General S T X.

Arguments greturn {S T X}.
Arguments gask {S T X}.

Fixpoint fold {S T X} {Y: Type}
    (r: X -> Y) 
    (c: (∀(s: S), (T s -> Y) -> Y))
    (m: General S T X) {struct m}: Y.
    refine (
        match m with
        | greturn x => r x       (* why are all the underscores needed here? *)
        | gask s k => c s $ λ t, fold _ _ _ _ r c (k t) 
        end
        
    
    ).
Defined.

Definition gbind {S T X Y}
    (g: General S T X)
    (k: X -> General S T Y): General S T Y :=
    fold k gask g.

(* I can see that this type checks, but I'm curious how this actually 
   represents a recursive call? We are asking for a resonse to a command s.
   Then given the response we return it into our monad still.
*)
Definition call {S T} (s: S): General S T (T s).
refine(gask s greturn ).
Defined.

Definition PiG S (T: S -> Type): Type :=
    ∀(s: S), General S T (T s).



