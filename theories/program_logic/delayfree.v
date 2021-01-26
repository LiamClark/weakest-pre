
From stdpp Require Import list base gmap fin_sets fin_map_dom.
From shiris.program_logic Require Import state.
Require Import Unicode.Utf8.

(*
This is the type algebra normalized form of:
∀ S, iTree (stateE S).

Do I need partiality on the get and put signatures? or can that be handled
completely at the semantic level?
*)
CoInductive delayST (ST A: Type): Type :=
| Answer: A -> delayST ST A
| Get : (ST -> delayST ST A) -> delayST ST A
| Put : ST -> (unit -> delayST ST A) -> delayST ST A
| Think: delayST ST A -> delayST ST A.

Arguments Answer {_ _}.
Arguments Get {_ _}.
Arguments Put {_ _}.
Arguments Think {_ _}.

(* Using the cofix to extract all parameters that are constant throughout the recursion
   Is crucial in having the guardness check work for loop and iter.
*)
Definition delayST_bind {ST A B} 
    (f: A -> delayST ST B):
    ∀ (ma: delayST ST A), delayST ST B :=
      cofix go (ma : delayST ST A) : 
      delayST ST B :=
        match ma with
        | Answer x => f x
        | Get k => Get (λ s, go (k s))
        | Put s k => Put s (λ s, go (k tt))
        | Think ma' => Think (go ma')
        end.

Instance mret_delayST ST: MRet (delayST ST) :=
 λ _ x, Answer x.

Instance mbind_delayST ST : MBind (delayST ST) := 
 λ _ _ f ma, delayST_bind f ma.

Instance fmap_delayST ST: FMap (delayST ST) :=
   λ A B f ma, ma ≫= mret ∘ f.

(* do I want to use the state monad here or expose the pairs? *)
Definition step_delayST {ST A} (e: delayST ST A): state ST (delayST ST A). 
refine(
    match e with
    | Answer x  => mret $ Answer x 
    | Get k     => k <$> getS 
    | Put s' k  => k <$> putS s'
    | Think e'  => mret e'
    end
).
Defined.

(* First a single threaded evaluator *)
Fixpoint eval_delayST {ST A} (n: nat) (e: delayST ST A) (s: ST) {struct n} : option A :=
    match n with
    | O => None
    | S n' => match (runState (step_delayST e) s) with 
              | Some (e', s') => eval_delayST n' e' s'
              | None => None
              end
    end.

Fixpoint split_and_circulate {A} (xs: list A) (f: A -> A) {struct xs}: (list A) :=
    match xs with
    | nil => nil
    | cons x xs' => xs' ++ [f x]
    end.

Definition step_delayST_threads {ST A} 
    (threads: list (delayST ST A)) (s: ST)
    :(ST * (list (delayST ST A))) :=
        match threads with 
        | nil => (s, nil)
        | cons e es' => match (runState (step_delayST e) s) with
                        | None => (s, nil)
                        | Some (e', s') => (s', es' ++ [e'])
                        end
        end.

Definition check_delayST {ST A} (e: delayST ST A): A + delayST ST A :=
    match e with
    | Answer x  => inl x
    | Get k     => inr $ e
    | Put s' k  => inr $ e
    | Think e'  => inr $ e
    end.

(* Todo check the order of effects with list and state here
   and remove all these nested pattern matches
*)
Fixpoint eval_threaded_delayST {ST A} 
    (n: nat) 
    (threads: list (delayST ST A))
    (s: ST) {struct n}: option A :=

    match n with
    | O => None
    | S n' => let (s', threads') := (step_delayST_threads threads s)
              in match threads' with
                 | nil => None
                 | cons e' _ => match check_delayST e' with
                                | inl x => Some x
                                | inr e'' => eval_threaded_delayST n' threads' s'
                                end
                 end
    end.





