
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

(* Definition delay_st_pipe {ST A B C} 
    (f: A -> delay_st ST B)
    (g: B -> delay_st ST C): A -> delay_st ST C := 
  λ x,  f x ≫= g.

Definition case_ {A B C}  (f: A -> C) (g: B -> C)
  : (A + B -> C) :=
    λ ab,
        match ab with
        | inl a => f a
        | inr b => g b
        end .
  
CoFixpoint iter {ST A B} (f: A -> delay_st ST (A + B)) : A -> delay_st ST B :=
    delay_st_pipe f (case_ (Think ∘ iter f) Answer). *)


Definition heap V := gmap nat V.

Variant step_result (V A: Type): Type :=
| Step (e: expr V A)
| ForkStep (e: expr V A) (ef: expr V ()).

Arguments Step {_ _}.
Arguments ForkStep {_ _}.

Definition step_vis {V R T}
 (c: envE V T)
 : (T -> expr V R) -> state (heap V) (step_result V R) :=
    match c with
    |GetE l   => λ k, (Step ∘ k) <$> (state.get l)
    |PutE l v => λ k, (Step ∘ k) <$> (state.put l v)
    |AllocE v => λ k, (Step ∘ k) <$> (state.alloc v)
    |FreeE l  => λ k, (Step ∘ k) <$> (state.free l)
    end.

Definition step_expr {V R} (e: expr V R): state (heap V) (step_result V R) :=
    match e with
    | Answer x  => mret $ Step $ Answer x 
    | Vis stateE k => step_vis stateE k 
    | Fork e' k => mret $ ForkStep k e'
    | Think e'  =>  mret $ Step e'
    end.


Definition step_delay_st_heap {A} (e: delay_st heap A)
    : state heap (delay_st heap A).
refine (
    match e with
    | Answer x   => mret $ Answer x
    | Get n k    => _
    | Put n s' k => _
    | Think e'   => _
    end
).
- refine(_).
Admitted.

(* First a single threaded evaluator *)
Fixpoint eval_delay_st {ST A} (n: nat) (e: delay_st ST A) (s: ST) {struct n} : option A :=
    match n with
    | O => None
    | S n' => match (runState (step_delay_st e) s) with 
              | Some (e', s') => eval_delay_st n' e' s'
              | None => None
              end
    end.

Fixpoint split_and_circulate {A} (xs: list A) (f: A -> A) {struct xs}: (list A) :=
    match xs with
    | nil => nil
    | cons x xs' => xs' ++ [f x]
    end.

Definition step_delay_st_threads {ST A} 
    (threads: list (delay_st ST A)) (s: ST)
    :(ST * (list (delay_st ST A))) :=
        match threads with 
        | nil => (s, nil)
        | cons e es' => match (runState (step_delay_st e) s) with
                        | None => (s, nil)
                        | Some (e', s') => (s', es' ++ [e'])
                        end
        end.

Definition check_delay_st {ST A} (e: delay_st ST A): A + delay_st ST A :=
    match e with
    | Answer x  => inl x
    | Get n k     => inr $ e
    | Put n s' k  => inr $ e
    | Think e'  => inr $ e
    end.

(* Todo check the order of effects with list and state here
   and remove all these nested pattern matches
*)
Fixpoint eval_threaded_delay_st {ST A} 
    (n: nat) 
    (threads: list (delay_st ST A))
    (s: ST) {struct n}: option A :=

    match n with
    | O => None
    | S n' => let (s', threads') := (step_delay_st_threads threads s)
              in match threads' with
                 | nil => None
                 | cons e' _ => match check_delay_st e' with
                                | inl x => Some x
                                | inr e'' => eval_threaded_delay_st n' threads' s'
                                end
                 end
    end.





