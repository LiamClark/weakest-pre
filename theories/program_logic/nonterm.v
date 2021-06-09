From stdpp Require Import list base.
Require Import Unicode.Utf8.

Section delay.
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
(* Print TBind. *)

CoFixpoint iter {A B} (body: A -> delay (A + B)) : A -> delay B.
refine (λ a, TBind(λ ab,
              match ab with (* This is not actually guarded, are they lying in the paper? *)
              | inl a => Think (iter _ _ body a)
              | inr b => Answer b
              end 
) (body a) ).
Defined.

(*Iter and loop are mutually derivable so here we implement loop in terms of iter
  the intuition is as follows: I don't actually get it yet let's just run it and see what it does.

*)
Definition loop {A B C} (body: C + A -> delay (C + B)): A -> delay B.
refine (λ a, iter 
              (λ ca: C + A, 
                TBind (λ cb: C + B, 
                         match cb with
                         | inl c => Answer $ inl $ inl c
                         | inr b => Answer $ inr b
                         end
                      )
                      (body ca)
              )
         (inr a)).
Defined.

Definition state (ST A: Type) : Type := ST -> delay (ST * A).

Definition distribute_delay {ST A B} (msab: delay (ST * (A + B))): delay (ST * A + ST * B) :=
  (λ '(s, ab), match ab with
                |inl a => inl (s, a)
                |inr b => inr (s, b)
                end
  ) <$> msab.

CoFixpoint iter_state {A B ST} (body: A -> state ST (A + B)) : A -> state ST B :=
  λ a s, iter
     (λ '(s, a), distribute_delay $ body a s )
     (s, a).

(*Example programs *)
Definition fib' (st: nat * nat * nat): delay ((nat * nat * nat) + nat).
refine(match st with
|(0, x, y) => Answer $ inr $ x
|((S n), x, y) => Answer $ inl (n, y, x + y)
end).
Defined.

Definition fib (n: nat): delay nat := iter fib' (n, 0, 1).

Class Evaluator (m: Type -> Type)  := 
   eval: ∀(A: Type), nat -> (m A) -> option A.
Instance ev_delay: Evaluator delay :=
     λ A, fix r n ma := 
              match n with
              | O => None
              | S n' => match ma with
                        | Answer x => Some x
                        | Think ma' => r n' ma'
                        end
              end.

Arguments eval {_ _ _}.

Lemma test_fib: (λ n, eval 10 (fib n)) <$> [0; 1; 2; 3; 4; 5; 6; 7] = Some <$> [0; 1; 1; 2; 3; 5; 8; 13].
Proof.
  reflexivity.
Qed.

End delay.

(* CoInductive non-termination monad with explicit bind constructor
 *)
Section cocomputation.
  CoInductive comp (A: Type) : Type :=
  | Answer: A -> comp A
  | Bind: forall B, comp B -> (B -> comp A) -> comp A.

  Arguments Answer {A}.
  Arguments Bind {A} {B}.

  CoFixpoint rec {A B} (f: (A -> comp B) -> (A -> comp B)) (x: A): comp B.
  refine (f (rec _ _ f ) x).
  Defined.

  

  (* In order to evaluate a finite prefix of the CoInductive comp monad
     we define this exec relation that shows us how to evaluate a single
     constructor of comp.
   *)
  Inductive exec A : comp A -> A -> Prop :=
  |ExecAnswer : forall x, exec A (Answer x) x
  |ExecBnd: forall B (c : comp B) (f: B -> comp A) x1 x2,
      exec B c x1
      -> exec A (f x1) x2
      -> exec A (Bind c f) x2.

  Arguments exec {A}.

  Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2)) (right associativity, at level 70).
  (* Not sure if this is a good as an example since fib should be structuraly recursive normally? *)
  CoFixpoint fib (n: nat) : comp nat :=
    match n with
    | 0 => Answer 1
    | 1 => Answer 1
    | _ => n1 <- fib (pred n) ;
           n2 <- fib (pred (pred n)) ;
           Answer (n1 + n2)
    end.

  (* frob allows us to get a constructor around our expression to simplify a single step *)
  Definition frob {A} (c: comp A) :=
    match c with
    | Answer x => Answer x
    | Bind cB f => Bind cB f
    end.

  Lemma exec_frob A (x: A) (c : comp A) :
     exec (frob c) x -> exec c x.
  Proof.
    intro H.
    destruct c; unfold frob in H.
    - assumption.
    - assumption.
  Qed.

  Lemma test_fib: exec (fib 5) 8.
  Proof.
    apply exec_frob.
    simpl.
    eapply ExecBnd.
    - apply exec_frob. simpl. eapply ExecBnd.
      + apply exec_frob. simpl. eapply ExecBnd.
        * apply exec_frob. simpl. eapply ExecBnd.
          -- apply exec_frob. simpl. apply ExecAnswer.
          -- eapply ExecBnd.
             ++ apply exec_frob. simpl. apply ExecAnswer.
             ++ apply ExecAnswer.
        * eapply ExecBnd.
          -- apply exec_frob. simpl. apply ExecAnswer.
          -- apply ExecAnswer.
      + eapply ExecBnd.
        * apply exec_frob. simpl. eapply ExecBnd.
          -- apply exec_frob. simpl. apply ExecAnswer.
          -- eapply ExecBnd.
             ++ apply exec_frob. simpl. apply ExecAnswer.
             ++ apply ExecAnswer.
        * apply ExecAnswer.
    - eapply ExecBnd.
      + apply exec_frob. simpl. eapply ExecBnd.
        * apply exec_frob. simpl. eapply ExecBnd.
          -- apply exec_frob. simpl. apply ExecAnswer.
          -- eapply ExecBnd.
             ++ apply exec_frob. simpl. apply ExecAnswer.
             ++ apply ExecAnswer.
        * eapply ExecBnd.
          -- apply exec_frob. simpl. apply ExecAnswer.
          -- apply exec_frob. simpl. apply ExecAnswer.
      + apply ExecAnswer.
  Qed.
End cocomputation.


Arguments exist {A P} _ _.
Arguments proj1_sig {A P} _.
Section computation.
  Variable A : Type.
  (** The type [A] describes the result a computation will yield, if it terminates.

     We give a rich dependent type to computations themselves: *)

  Definition computation := nat -> option A.
(*    {f : nat -> option A
      | forall (n : nat) (v : A),
	      f n = Some v
        -> forall (n' : nat), n' >= n
	      -> f n' = Some v
    }. *)

  Definition runTo (m: computation) (n: nat) (v: A) :=
    proj1_sig m n = Some v.

  Definition run (m: computation) (v: A) :=
    exists n, runTo m n v.
End computation.

Arguments run {A}.
Arguments runTo {A}.

(* Locate "¬". *)
Section Bottom.
  Variable A: Type.

  Definition bottom: computation A.
    refine (exist (fun _ => @None A) _ ).
    intros n v heq.
    discriminate heq.
  Defined.

  Lemma run_Bottom v : not (run bottom v).
  Proof.
    intro Hrun.
    destruct Hrun as (n & r).
    unfold runTo in r.
    simpl in r.
    discriminate r.
  Qed.
End Bottom.

Section Return.
  Variable A: Type.
  Variable v: A.

  Definition ret: computation A.
    refine(exist (fun _ => Some v ) _).
    intros a b c d e. assumption.
  Defined.

  Lemma run_ret: run ret v.
  Proof.
    unfold run.
    exists 0.
    unfold runTo.
    reflexivity.
  Qed.

End Return.

Arguments ret {A}.

Section Bind.
  Variables A B: Type.
  Variable m1: computation A.
  Variable m2: A -> computation B.

  (* We implement bind for our bounded computation monad
     the computational part works as follows:
         1. run f1 the function contained in m1 for the bound we get from the function we are creating.
            if f1 succeeded, we obtain the value it returned.
         2. obtain the second function f2 from m2 and v.
         3. run f2 with the same recursion bound as f1 to obtain a option B.

     After this we need to prove that if forall n for which our composite computation succeeds.
     It will also succeed for an n' that is bigger than n.
   *)
  Definition bind: computation B.
    refine (exist  (fun n => let '(exist f1 _) := m1 in
                             match f1 n with
                             | None => None
                             | Some v =>
                               let '(exist f2 _) := m2 v in
                               f2 n
                             end
                   ) _).
    destruct m1 as [f1 prfm1].
    intros n b HCompsome n' Hgteq.
    (* we check if f1 would succeed for n *)
    destruct (f1 n) eqn: E.
    -
      (* f1 n = Some a *)
      (* Then we get the computation and monotonocity refinement from m2 *)
      destruct (m2 a) as [f2n prfm2n] eqn: E' .
      (* if f1n succeded we known f1 n' succeeds *)
      rewrite (prfm1 n a E n' Hgteq).
      rewrite E'.
      (* we use the monotonicity refinement from m2 to show that f2 holds for bigger n *)
      apply (prfm2n n b).
      + (* We know that the composite computation succeeded for n in Hcomp *)
        assumption.
      + assumption.
    - (*if f1n does not succeed our composite computation can never have succeded
        aka Hcompsome = False *)
      discriminate.
  Defined.

  (* Locate "≥". *)
  (* Print ge. *)
  Lemma run_bind (v1: A) (v2: B):
    run m1 v1
    -> run (m2 v1) v2
    -> run bind v2.
  Proof.
    unfold run.
    unfold runTo.
    (* Both computations ran successfully for some nat number *)
    intros (n & Hm1Some) (n' & Hm2Some).
    (* our composite computation will always run successfully with the max of the two *)
    exists (max n n').
    simpl.
    destruct m1 as (f1n & prf1n).
    rewrite (prf1n n v1 Hm1Some).
    - destruct m2 as (f2n & prf2n').
      apply (prf2n' n' v2 Hm2Some).
      apply Max.le_max_r.
    - apply Max.le_max_l.
  Qed.

End Bind.

Section lattice.
  Variable A :Type.

  Definition leq (x y: option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

Arguments leq {A}.

Section Fix.
  Variables A B : Type.
  Variable f: (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous :
    forall n v v1 x,
      runTo (f v1 x) n v
      -> forall (v2: A -> computation B),
        (forall x', leq (proj1_sig (v1 x') n) (proj1_sig (v2 x') n))
        -> runTo (f v2 x) n v.

  Fixpoint Fix' (n: nat) (x: A): computation B :=
    match n with
    | O => bottom _
    | S n' => f (Fix' n') x
    end.

  (* SearchAbout le. *)

  (* If fix succeeds for a n it should succeed for a bigger n' *)
  Lemma Fix'_ok steps n x v:
    proj1_sig (Fix' n x) steps = Some v
    -> forall n', ge n' n
                  -> proj1_sig (Fix' n' x) steps = Some v.
  Proof.
    revert v x.
    induction n;
    intros v x Hrecsuc n' Hge;
    unfold runTo in *.
    -
      (* n=0 *)
      simpl in Hrecsuc. discriminate.
    - (*n = S n' n' = 0 *)
      destruct n'.
      + (* n' = 0  *)
      apply Nat.nle_succ_0 in Hge.
      contradiction.
      + (* Here fix is allowed to take a step *)
        simpl. simpl in Hrecsuc.
        (* we use our monotonicity to say that a recursive occurence should also
           f (fix n') also works in f (fix n).
         *)
        apply (f_continuous steps v (Fix' n) x Hrecsuc (Fix' n')).
        (* we need to show that they produce the same answer *)
        unfold leq.
        intros x' v' Hfixn.
        (* our Ih allows us to go from n' to n again *)
        apply (IHn v' x').
        * assumption.
        * apply le_S_n in Hge. assumption.
  Qed.

  (*Easier interface to Fix'  *)
  Definition Fix: A -> computation B.
    (* the function we will use simply calls Fix' with steps = n *)
    refine (fun x => exist (fun n => proj1_sig (Fix' n x) n) _).
    (* we now need to prove that Fix' is monotome in n *)
    intros n v Hrec n' Hge.
    apply (Fix'_ok n' n x v).
    - unfold proj1_sig in *.
      destruct (Fix' n x) as (f' & Fix'prf).
      apply (Fix'prf n v Hrec n' Hge).
    - assumption.
  Defined.

  Theorem run_Fix x v:
    run (f Fix x) v
    -> run (Fix x) v.
  Proof.
    intro HFFix.
    destruct HFFix as (n & HFFix).
(*   destruct (Fix x) as (f' & monotoneprf) eqn: E. *)
    exists (S n).
    (* we want to drop down a step level so we use the monotonicity of computations *)
    (* This was reverse engineerd from the generated code from the automated proof *)
    (* Is there not a nice way to state this? *)
    pose (Hmono := proj2_sig (f (Fix' n) x) n v).
    unfold runTo in *. simpl.
    apply Hmono.
    - eapply f_continuous.
      + apply HFFix.
      + intros x' v' h'. assumption.
    - unfold ge.
      apply Nat.le_succ_diag_r.
  Qed.
End Fix.
Arguments Fix {A} {B}.

Definition looper: bool -> computation unit.
  refine (Fix (fun looper (b: bool) =>
                 if b then ret tt else looper b) _
         ).
  intros n v v1 x Hrun.
  intros f Hlat.
  destruct x.
  - assumption.
  - apply Hlat.
    assumption.
Defined.

Lemma test_looper: run (looper true) tt.
  exists 1.
  unfold runTo.
  reflexivity.
Qed.

