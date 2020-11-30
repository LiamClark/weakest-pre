From stdpp Require Import list base gmap fin_sets fin_map_dom.
Require Import Unicode.Utf8.

(*First we define the delay monad and it's looping combinators *)
CoInductive delay (A: Type): Type :=
| Answer: A -> delay A
| Think: delay A -> delay A.

Arguments Answer {_}.
Arguments Think {_}.


Instance fmap_delay : FMap delay := 
  λ A B f,
       cofix r fa := match fa with
                     | Answer x  => Answer $ f x
                     | Think fa' => Think $ r fa'
       end.

(* Using the cofix to extract all parameters that are constant throughout the recursion
   Is crucial in having the guardness check work for loop and iter.
*)
Definition TBind {A B} (f: A -> delay B): ∀ (ma: delay A), delay B :=
  cofix go (ma : delay A) : 
  delay B :=
    match ma with
    | Answer x => f x
    | Think ma' => Think (go ma')
    end.
Print TBind.

Instance mbind_delay : MBind delay := 
  λ _ _ f ma, TBind f ma.

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


CoFixpoint iter {A B} (body: A -> delay (A + B)) : A -> delay B.
refine (delay_pipe body ( case_ (Think ∘ iter _ _ body) Answer)).
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

Lemma iter_unfold {A B} (body: A -> delay (A + B)) (x: A):
   iter body x = body x ≫= case_ (Think ∘ iter body) Answer.
Proof.
  rewrite <- (delay_frob_eq (iter body x)).
  rewrite <- (delay_frob_eq (_ ≫= _)).
  done.
Qed.

(*
  Iter and loop are mutually derivable so here we implement loop in terms of iter
  the intuition is as follows: I don't actually get it yet let's just run it and see what it does.
*)
Definition loop {A B C} (body: C + A -> delay (C + B)): A -> delay B.
refine (λ a, iter 
              (λ ca: C + A, 
                (body ca) ≫= (λ cb: C + B, 
                         match cb with
                         | inl c => Answer $ inl $ inl c
                         | inr b => Answer $ inr b
                         end
                      )
                      
              )
         (inr a)).
Defined.

(*Now we define our computations in terms of StateT ST (OptionT Delay) *)
Record state_delay (ST A: Type) : Type := State {
  runState: ST -> delay $ option (ST * A)
}.

Arguments State {_ _}.
Arguments runState {_ _}.


Instance mret_state_delay ST : MRet (state_delay ST) :=
   λ A a, State $ λ s, Answer $ Some (s, a).

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
Definition iter_state_delay {A B ST} (body: A -> state_delay ST (A + B)) : A -> state_delay ST B.
refine (λ a, State $ λ s, iter 
                     (λ optsa, match optsa with
                               | Some (s', a') => distribute_delay_state (runState (body a') s')
                               | None => Answer $ inr $ None 
                               end
                     )
                     (Some (s, a)) 
   ).
Defined.

(* This definition is here to show the type of the body in iter_state_delay without iter fixing it *)
Definition test {A B ST} (body: A -> state_delay ST (A + B))
    : A -> ST -> (option (ST * A) -> delay (option (ST * A) + option (ST * B))).
refine (λ (a: A) (s: ST) optsa,
            match optsa with
            | Some (s', a') => distribute_delay_state (runState (body a') s')
            | None => Answer $ inr $ None 
            end
).
Defined.

(* Write down an equality over state_delay that leaks all the state
   This can then be used for unrolling the first loop after that the layer of state becomes
   transparent anwyays and we can use iter delay.
*)
Lemma iter_state_delay_unfold_first {A B ST} (body: A -> state_delay ST (A + B)) (x: A):
 ∀s,
   runState (iter_state_delay body x) s = distribute_delay_state (runState (body x) s) ≫= 
   case_ (λ a, Think $ iter (λ optsa, match optsa with
            | Some (s', a') => distribute_delay_state (runState (body a') s')
            | None => Answer $ inr $ None 
            end) a) Answer.
Proof.
  intros s. unfold iter_state_delay. simpl.
  rewrite <- (delay_frob_eq (iter _ (Some (s, x)))).
  rewrite <- (delay_frob_eq (_ ≫= _)).
  done.
Qed.

(*These combinators type check but could really use some testing! *)
Definition loop_state_delay {A B C ST} (body: (C + A) -> state_delay ST (C + B)): A -> state_delay ST B.
refine (λ a, iter_state_delay
              (λ ca: C + A,
                (body ca) ≫= (λ cb: C + B,
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
Definition modifyS' {A ST} (f: ST -> ST * A): state_delay ST A :=
  State $ λ s, Answer $ Some $ f s.

Definition modifyS {ST} (f: ST -> ST): state_delay ST () :=
  modifyS' $ λ st, (f st, tt).

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

Definition get {A} (n: nat): state_delay (gmap nat A) A :=
  getS ≫= λ st, ret_fail $ lookup n st.

Definition put {A} (n: nat) (x : A) : state_delay (gmap nat A) unit :=
  modifyS <[n := x]>.

Definition alloc {A} (v: A) : state_delay (gmap nat A) nat :=
  modifyS' $ λ st, 
              let fresh := fresh $ dom (gset nat) st
              in (<[fresh := v]> st, fresh). 

Definition free {A} (n: nat): state_delay (gmap nat A) unit :=
  modifyS $ delete n.

Fixpoint ev_delay {A} (n: nat) (ma: delay A): option A :=
  match n with
  | O => None
  | S n' => match ma with
            | Answer x => Some x
            | Think ma' => ev_delay n' ma'
            end
  end.


Definition eval_state_delay {ST A} (n: nat) (ma: state_delay ST A): ST -> option A.
refine(λ st, fmap snd $ mjoin $ ev_delay n $ runState ma st).
Defined.


(*
  Example programs and intermediate steps
 *)
Section delay.

(*Example programs *)
Definition fib' (st: nat * nat * nat): delay ((nat * nat * nat) + nat).
refine (match st with
|(0, x, y) => Answer $ inr $ x
|((S n), x, y) => Answer $ inl (n, y, x + y)
end).
Defined.

Definition fib (n: nat): delay nat := iter fib' (n, 0, 1).

Lemma test_fib: (λ n, ev_delay 10 (fib n)) <$> [0; 1; 2; 3; 4; 5; 6; 7] = Some <$> [0; 1; 1; 2; 3; 5; 8; 13].
Proof.
  reflexivity.
Qed.

Definition fib_pure' (st: nat * nat * nat): ((nat * nat * nat) + nat).
refine (match st with
|(0, x, y) => inr $ x
|((S n), x, y) => inl (n, y, x + y)
end).
Defined.

Definition fib_pure (n: nat): delay nat := iter_pure fib_pure' (n, 0, 1).

Lemma test_fib_pure: 
  (λ n, ev_delay 10 (fib_pure n)) <$> [0; 1; 2; 3; 4; 5; 6; 7] = Some <$> [0; 1; 1; 2; 3; 5; 8; 13].
Proof.
  reflexivity.
Qed.

Definition state (ST A: Type) : Type := ST -> delay (ST * A).

Instance mret_state ST : MRet (state ST) := λ A a s, Answer (s, a).

Instance mbind_state ST: MBind (state ST) :=
  λ _ _ f ma st, 
          TBind (λ '(s', x), f x s') (ma st). 

Definition put' {ST} (s: ST): state ST () :=
    λ _, Answer (s, tt).

Definition get' {ST} : state ST ST :=
  λ s, Answer (s, s).

Definition distribute_delay {ST A B} (msab: delay (ST * (A + B))): delay (ST * A + ST * B) :=
  (λ '(s, ab), match ab with
                |inl a => inl (s, a)
                |inr b => inr (s, b)
                end
  ) <$> msab.

Definition iter_state {A B ST} (body: A -> state ST (A + B)) : A -> state ST B :=
  λ a s, iter
     (λ '(s', a'), distribute_delay $ body a' s' )
     (s, a).


Fixpoint eval_state {ST A} (n: nat) (ma: state ST A) {struct n} : ST -> option A.
refine(λ s,
        match n with
        | S n' =>
          match ma s with
            | Answer (s', a) => Some a
            | Think m' => eval_state _ _ n' (λ _, m')  s
             (*This bothers me, it seems to indicate that state would be lost between recursive steps?*)
          end 
        | O => None
        end
      ).
Defined.

Definition iter_body (n: nat): state nat (nat + nat).
refine(get' ≫= λ s, match s with
                     | O => mret $ inr n
                     | S s' => put' s' ;; mret $ inl $ n + s
                     end
).
Defined.

Lemma test_state: eval_state 10 (iter_state (iter_body) 0) 5 = Some 15.
Proof.
  reflexivity.
Qed.

(* however this seems to work? WTF?*)
Lemma test_state': eval_state 10 (iter_state iter_body 0 ;; get') 5 = Some 0.
Proof.
  reflexivity.
Qed. 


Check fst.
(* This should illustrate the state passing better. We first run the state effect
   Then the think notes implicitly somehow capture the state passing in the iteration constructs 
*)


Definition iter_adder (l k: nat): () -> state_delay (gmap nat nat) (() + nat) :=
  λ _, x  ← get l ;
       y  ← get k ; 
       if x =? 0 then mret $ inr y 
       else put l (x - 1) ;; put k (y + 1) ;; mret $ inl () .


Definition init_state: gmap nat nat := (<[1 := 1]> (<[0 := 5]> ∅)).
Lemma test_gmap_adder: eval_state_delay 10 (iter_state_delay (iter_adder 0 1) tt) init_state = Some 6.
Proof.
  reflexivity.
Qed.

End delay.