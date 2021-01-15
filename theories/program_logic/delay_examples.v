
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import delaystate.
From shiris.program_logic Require Import delaywp.

(*Example programs *)
Definition fib' (st: nat * nat * nat): delay ((nat * nat * nat) + nat).
refine (match st with
|(0, x, y) => Answer $ inr $ x
|((S n), x, y) => Answer $ inl (n, y, x + y)
end).
Defined.

Definition fib (n: nat): delay nat := delaystate.iter fib' (n, 0, 1).

Lemma test_fib: (λ n, eval_delay 10 (fib n)) <$> [0; 1; 2; 3; 4; 5; 6; 7] = Some <$> [0; 1; 1; 2; 3; 5; 8; 13].
Proof.
  reflexivity.
Qed.

(* 
    What is the intuition behind this?
*)
Fixpoint coq_fib (n1 n2: nat) (n: nat): nat :=
    match n with
    |O => n1
    |S n' => match n' with
             | O => n2 
             | S n'' => (coq_fib n1 n2 n') + (coq_fib n1 n2 n'')
             end
    end.

Lemma test_coq_fib:
  (coq_fib 0 1) <$>[0; 1; 2; 3; 4; 5; 6; 7] = [0; 1; 1; 2; 3; 5; 8; 13].
  reflexivity.
Qed.

Lemma test_coq_fib_move: coq_fib 13 21 4 = coq_fib 5 8 (S (S 4)).
Proof.
    reflexivity.
Qed.

Section state_ad.
Context `{! inG Σ (heapR natO)}.

Lemma post' (n1 n2 n: nat) (ret: nat): iProp Σ.
refine( ⌜ret = coq_fib n1 n2 n⌝%I).
Defined.

Lemma coq_fib_unfold n1 n2 n: 
    coq_fib n1 n2 (S (S n)) = coq_fib n1 n2 (S n) + coq_fib n1 n2 n.
Proof.
    done.
Qed.

Lemma pair_induction (P : nat -> Prop): 
    P 0 ->
    P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n))) ->
    forall n, P n.
Proof.
    intros H0 H1 Hstep n.
    assert (P n /\ P (S n)).
    induction n.
    - done.
    - destruct IHn. split.
        + done. 
        + by apply Hstep.
    - by destruct H.
Qed.

SearchAbout plus.
Lemma coq_fib_move n1 n2 n:
 coq_fib n2 (n1 + n2) (S n) = coq_fib n1 n2 (S (S n)).
Proof.
    induction n using pair_induction.
    - by rewrite Nat.add_comm.
    - by rewrite Nat.add_comm.
    - rewrite -> (coq_fib_unfold  n1 n2 (S (S (n)))).
      rewrite <- IHn0.
      rewrite <- IHn.
      rewrite -> coq_fib_unfold.
      reflexivity.
Qed.

Lemma coq_fib_move' n1 n2 n:
 coq_fib n2 (n1 + n2) n = coq_fib n1 n2 (S n).
 Proof.
     destruct n.
     + done.
     + apply coq_fib_move.
 Qed.

(* To get lob induction to work I need the numbers that are passed
    between loop states to vary. but then my post condition does
    not always hold that needs to be generalized too.
*)
Lemma verify_delay_fib' n1 n2 n:
    ⊢ wp_delay (delaystate.iter fib' (n, n1, n2)) (post' n1 n2 n).
Proof.
    (*How do i vary the IH here properly *)
    iLöb as "IH" forall (n n1 n2).
    iApply wp_delay_iter. 
    destruct n as [| n'] eqn: E .
    - iApply wp_delay_return. done.
    - iApply wp_delay_return. simpl. 
      iNext.
      iApply (wp_strong_mono_delay with "IH").
      unfold post'.
      iIntros (v Hv) "!%".
      subst v.
      apply coq_fib_move'.
Qed.

Lemma verify_delay_fib n:
    True -∗ wp_delay (fib n) (post n).
Proof.

Definition iter_adder (l k: nat): () -> state_delay (gmap nat nat) (() + nat) :=
  λ _, x  ← get l ;
       y  ← get k ; 
       if x =? 0 then mret $ inr y 
       else put l (x - 1) ;; put k (y + 1) ;; mret $ inl () .

Definition fib_state' (l1 l2: nat) (n: nat): state_delay (gmap nat nat) (nat + nat) :=
    match n with
    | S n' => n1 ← get l1 ;
              n2 ← get l2 ;
              put l1 n1 ;; put l2 (n1 + n2) ;; mret $ inl n'
    | O => inr <$> get l2
    end.

Definition fib_state (l1 l2 n: nat): state_delay (gmap nat nat) nat := 
    iter_state_delay (fib_state' l1 l2) n.

Lemma verify_delay_state_fib l1 l2 n:
    ∀ γ, points_to γ l1 1 ∗ points_to γ l2 1 -∗
            wp (state_interp γ) (fib_state l1 l2 n) (λ ret, ⌜ret = coq_fib 0 1 n⌝).
Proof.
Admitted.