
From stdpp Require Import list base gmap fin_sets fin_map_dom.
From shiris.program_logic Require Import state.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
Require Import Unicode.Utf8.

(*
This is the type algebra normalized form of:
∀ S, iTree (stateE S).

Do I need partiality on the get and put signatures? or can that be handled
completely at the semantic level?
*)

CoInductive itree (E: Type -> Type) (R: Type): Type :=
| Answer (r: R) (* computation terminating with value r *)
| Think (t: itree E R) (* "silent" tau transition with child t *)
| Fork: itree E () ->  itree E R -> itree E R
| Vis: ∀{A: Type}, E A ->  (A -> itree E R) -> itree E R.

Arguments Answer {_ _}.
Arguments Think {_ _}.
Arguments Fork {_ _}.
Arguments Vis {_ _ _}.


Definition loc := nat.

Variant envE (V : Type) :Type -> Type :=
|GetE:   loc -> envE V V
|PutE:   loc -> V -> envE V ()
|AllocE: V -> envE V loc 
|FreeE:  loc -> envE V ().


Arguments GetE {_}.
Arguments PutE {_}.
Arguments AllocE {_}.
Arguments FreeE {_}.

Definition expr (V: Type) := itree (envE V). 

Definition get {V} (l: loc): expr V V := Vis (GetE l) Answer.
Definition put {V} (l: loc) (v: V): expr V () := Vis (PutE l v) Answer .
Definition alloc {V} (v: V): expr V loc := Vis (AllocE v) Answer.
Definition free {V} (l: loc): expr V () := Vis (FreeE l) Answer.


(* Apply the continuation k to the Ret nodes of the itree t *)
Instance itree_bind {E}: MBind (itree E) := λ R S k, 
    cofix go u := match u with
    | Answer r => k r
    | Think t => Think (go t)
    | Fork e k => Fork e (go k)
    | Vis e k => Vis e (λ x, go (k x))
    end.

Instance itree_mret {E}: MRet (itree E) :=
 λ _ x, Answer x.

Instance itree_fmap {E}: FMap (itree E) :=
   λ A B f ma, ma ≫= mret ∘ f.

Definition pipe {M} {m: MBind M} {A B C} 
    (f: A -> M B)
    (g: B -> M C): A -> M C := 
  λ x,  f x ≫= g.

Definition case_ {A B C}  (f: A -> C) (g: B -> C)
  : (A + B -> C) :=
    λ ab,
        match ab with
        | inl a => f a
        | inr b => g b
        end .
  
CoFixpoint iter {V A B} (f: A -> expr V (A + B)) : A -> expr V B :=
    pipe f (case_ (Think ∘ iter f) Answer). 

CoFixpoint loop {V A B C} (f: (C + A) -> expr V (C + B)): A -> expr V B :=
    λ a, iter (λ ca,
                 cb ← f ca ;
                 match cb with
                 | inl c => mret (inl (inl c))
                 | inr b => mret (inr b)
                 end
    ) (inr a).

Definition is_done {V R} (e: expr V R): option R :=
    match e with
    | Answer r => Some r
    | Think t  => None 
    | Fork e k => None 
    | Vis e k  => None 
    end.



