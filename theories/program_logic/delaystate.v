From stdpp Require Import list option base gmap fin_sets fin_map_dom.
Require Import Unicode.Utf8.

(*First we define the delay monad and it's looping combinators *)
CoInductive delay (A: Type): Type :=
| Answer: A -> delay A
| Think: delay A -> delay A.

Arguments Answer {_}.
Arguments Think {_}.

(* Using the cofix to extract all parameters that are constant throughout the recursion
   Is crucial in having the guardness check work for loop and iter.
*)
Definition delay_bind {A B} (f: A -> delay B): delay A -> delay B :=
  cofix go (ma : delay A): delay B :=
    match ma with
    | Answer x => f x
    | Think ma' => Think (go ma')
    end.

Instance mret_delay : MRet delay := λ _ x, Answer x.

Instance mbind_delay : (MBind delay) := 
  λ _ _ f ma, delay_bind f ma.


Instance fmap_delay: (FMap delay) := 
  λ A B f ma,
        ma ≫= compose Answer f.


(* Coproduct lifting operations
 g >>> f /  f . g  *)
Definition delay_pipe {A B C}  (f: A -> delay B) (g: B -> delay C): A -> delay C := 
  λ x,  f x ≫= g.

Definition case_ {A B C}  (f: A -> C) (g: B -> C)
  : (A + B -> C).
refine(λ ab,  match ab with
              | inl a => f a
              | inr b => g b
              end 
).
Defined.

CoFixpoint iter' {A B} (f: A -> delay (A + B)) : A -> delay B :=
 λ x, ab ← f x ;
        match ab with
        | inl a => Think (iter' f a)
        | inr b => Answer b
        end.

CoFixpoint iter {A B} (f: A -> delay (A + B)) : A -> delay B.
refine (delay_pipe f ( case_ (Think ∘ iter _ _ f) Answer)).
Defined.

Definition delay_frob {A} (e: delay A): delay A.
refine ( match e with
          |Answer x => Answer x
          |Think e' => Think e'
end).
Defined.

Lemma delay_frob_eq {A} (e: delay A): delay_frob e = e.
Proof.
  by destruct e.
Qed.

Lemma iter_unfold {A B} (f: A -> delay (A + B)) (x: A):
   iter f x = f x ≫= case_ (Think ∘ iter f) Answer.
Proof.
  rewrite <- (delay_frob_eq (iter f x)).
  rewrite <- (delay_frob_eq (_ ≫= _)).
  done.
Qed.

(*
  Iter and loop are mutually derivable so here we implement loop in terms of iter
  the intuition is as follows: I don't actually get it yet let's just run it and see what it does.
*)
Definition loop {A B C} (f: C + A -> delay (C + B)): A -> delay B :=
  λ a,
    iter (λ ca: C + A,
          f ca ≫= λ cb: C + B,
                   match cb with
                   | inl c => Answer $ inl $ inl c
                   | inr b => Answer $ inr b
                   end
         )
         (inr a).

(*Now we define our computations in terms of StateT ST (OptionT Delay) *)
Record state_delay (ST A: Type) : Type := State {
  runState: ST -> delay $ option (ST * A)
}.

Arguments State {_ _}.
Arguments runState {_ _}.


Instance mret_state_delay ST : MRet (state_delay ST) :=
   λ A a, State $ λ s, Answer $ Some (s, a).

Definition map_option_product {A B ST} (f: A -> B) (ma: option (ST * A)): option (ST * B) :=
  fmap (prod_map id f) ma.

Instance fmap_state_delay ST : FMap (state_delay ST) :=
  (λ A B f ma, State $ λ st, 
    fmap (map_option_product f) (runState ma st)).

Instance mbind_state_delay ST: MBind (state_delay ST) :=
 λ A B f ma, State $ λ st, (runState ma st) ≫=
    (λ optsa, match optsa with
              | Some (s, x) => runState (f x) s
              | None => Answer $ None
              end
    ).

Definition distribute_delay_state {A B ST} (m: delay $ option (ST * (A + B))):
 delay (option (ST * A) + option (ST * B)).
refine ((λ x, match x with
              | Some (s, ab) => match ab with (* is there a bifunctor instance?*)
                                | inl a => inl $ Some (s, a)
                                | inr b => inr $ Some (s, b)
                                end
              | None => inr $ None (* choose inr to end recursion earlier?*)
              end
) <$> m).
Defined.


(*These combinators type check but could really use some testing! *)
Definition iter_state_delay {A B ST} (f: A -> state_delay ST (A + B)) : A -> state_delay ST B.
refine (λ a, State $ λ s, iter 
                     (λ optsa, match optsa with
                               | Some (s', a') => distribute_delay_state (runState (f a') s')
                               | None => Answer $ inr $ None 
                               end
                     )
                     (Some (s, a)) 
   ).
Defined.

(* This definition is here to show the type of the f in iter_state_delay without iter fixing it *)
Definition test {A B ST} (f: A -> state_delay ST (A + B))
    : A -> ST -> (option (ST * A) -> delay (option (ST * A) + option (ST * B))).
refine (λ (a: A) (s: ST) optsa,
            match optsa with
            | Some (s', a') => distribute_delay_state (runState (f a') s')
            | None => Answer $ inr $ None 
            end
).
Defined.

(* Write down an equality over state_delay that leaks all the state
   This can then be used for unrolling the first loop after that the layer of state becomes
   transparent anwyays and we can use iter delay.
*)
Lemma iter_state_delay_unfold_first {A B ST} (f: A -> state_delay ST (A + B)) (x: A):
  ∀ s, 
  runState (iter_state_delay f x) s = distribute_delay_state (runState (f x) s) ≫= 
   case_ (λ a, Think $ iter (λ optsa, match optsa with
            | Some (s', a') => distribute_delay_state (runState (f a') s')
            | None => Answer $ inr $ None 
            end) a) Answer.
Proof.
  intros s. unfold iter_state_delay. simpl.
  rewrite <- (delay_frob_eq (iter _ (Some (s, x)))).
  rewrite <- (delay_frob_eq (_ ≫= _)).
  done.
Qed.

(* Since runstate is exposed in the law above,
 can I prove something that puts it pack in the state abstraction?*)
Lemma runState_eq {A ST} (e: state_delay ST A):
  State $ (λ s, runState e s) = e.
Proof.
  destruct e.
  reflexivity.
Qed.

Definition loop_state_delay {A B C ST} (f: (C + A) -> state_delay ST (C + B)): A -> state_delay ST B.
refine (λ a, iter_state_delay
              (λ ca: C + A,
                (f ca) ≫= (λ cb: C + B,
                                match cb with
                                | inl c => mret $ inl $ inl c
                                | inr b => mret $ inr b
                                end
                              )
              )
              (inr a)
    ).
Defined.

(*Next up implement the state operations! *)
Definition modifyS {A ST} (f: ST -> ST * A): state_delay ST A :=
  State $ λ s, Answer $ Some $ f s.

Definition getS {ST}: state_delay ST ST :=
  State $ λ st, Answer $ Some $ (st, st).

Definition putS {ST} (st: ST): state_delay ST () :=
  State $ λ st', Answer $ Some $ (st, tt).

Definition fail {ST A}: state_delay ST A :=
  State $ λ st, Answer $ None.

Definition ret_fail {ST A} (m: option A): state_delay ST A :=
  match m with
  |Some x => mret x
  |None => fail
  end.

 Definition modifyS' {A} (n: nat) (f: gmap nat A -> gmap nat A): state_delay (gmap nat A) () :=
    State $ λ st, if decide (is_Some (st !! n)) then Answer $ Some (f st, tt) else  Answer $ None.

Definition get {A} (n: nat): state_delay (gmap nat A) A :=
  getS ≫= λ st, ret_fail $ lookup n st.

  Definition put {A} (n: nat) (x : A) : state_delay (gmap nat A) unit :=
  modifyS' n  <[n := x]>.

Definition alloc {A} (v: A) : state_delay (gmap nat A) nat :=
  modifyS $ λ st, 
              let fresh := fresh $ dom (gset nat) st
              in (<[fresh := v]> st, fresh). 

(* Definition free {A} (n: nat): state_delay (gmap nat A) unit :=
  modifyS $ delete n. *)

Definition free {A} (n: nat): state_delay (gmap nat A) unit :=
  modifyS' n (delete n).

Fixpoint eval_delay {A} (n: nat) (ma: delay A): option A :=
  match n with
  | O => None
  | S n' => match ma with
            | Answer x => Some x
            | Think ma' => eval_delay n' ma'
            end
  end.

Definition eval_state_delay' {ST A} (n: nat) (ma: state_delay ST A): ST -> option (ST * A).
refine(λ st, mjoin $ eval_delay n $ runState ma st).
Defined.

Definition eval_state_delay {ST A} (n: nat) (ma: state_delay ST A): ST -> option A.
refine(λ st, fmap snd $ mjoin $ eval_delay n $ runState ma st).
Defined.
