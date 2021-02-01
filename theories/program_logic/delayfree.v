
From stdpp Require Import list base gmap fin_sets fin_map_dom.
From shiris.program_logic Require Import state.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import delayfree.
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

Definition get {V} (l: nat): expr V V := Vis (GetE l) Answer.
Definition put {V} (l: nat) (v: V): expr V () := Vis (PutE l v) Answer .
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


(* do I want to use the state monad here or expose the pairs? *)



(* Curry the value R so it can be changed by the dependent pattern match on c *)
Definition foo {V R} (c: envE V R) (σ σ': gmap loc V): R -> Prop.
refine (match c with
        |GetE l  => λ v, σ !! l = Some v /\ σ' = σ 
        |PutE l v' => λ _, is_Some (σ !! l) /\ σ' = <[l := v']> σ
        |AllocE v' => λ _, True
        |FreeE l => λ _, True 
        end
).
Defined.

Definition wp_pre {Σ} {V} (SI: gmap loc V -> iProp Σ)
     (go: discrete_funO (λ R, expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ)):
     discrete_funO (λ R, expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ).
refine(λ R e Φ,
        match e with
        |Answer x => Φ x 
        |Think e' => ▷ go R e' Φ
        |Fork e' k => ▷ (go R k Φ ∗ go unit e' (λ _, True))
        |Vis c k => ∀σ, SI σ ==∗ ∃σ' v, ⌜foo c σ σ' v⌝ ∗ SI σ' ∗ ▷ (go R (k v)) Φ
        end
)%I.
Defined.

Instance wp_pre_contractive {Σ A SI}: Contractive (@wp_pre Σ A SI).
Proof.
  rewrite /wp_pre => n wp wp' Hwp R e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp' {Σ} {V} (SI: gmap nat V -> iProp Σ)
              : ∀R, expr V R -> (R -> iProp Σ) ->iProp Σ :=
    fixpoint (wp_pre SI ).

Definition wp {Σ} {V R} (SI: gmap nat V -> iProp Σ) (e: expr V R) (Φ: R -> iProp Σ): iProp Σ := 
    wp' SI R e Φ.


Definition step_delay_st {ST A} (e: delay_st ST A): state ST (delay_st ST A) :=
    match e with
    | Answer x  => mret $ Answer x 
    | Get n k     => k <$> getS 
    | Put n s' k  => k <$> putS s'
    | Think e'  => mret e'
    end.

Definition heap := gmap nat nat.

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





