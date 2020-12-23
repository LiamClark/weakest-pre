
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

Fixpoint coq_fib (n1 n2: nat) (n: nat): nat :=
    match n with
    |O => n1
    |S n' => match n' with
             | O => n2 
             | S n'' => coq_fib n1 n2 n' + coq_fib n1 n2 n''
             end
    end.

Section state_ad.
Context `{! inG Σ (heapR natO)}.

Lemma post' (n1 n2 n: nat) (ret: nat): iProp Σ.
refine( ⌜ret = coq_fib n1 n2 n⌝%I).
Defined.

Locate "+".
Lemma post'' (n1 n2 n: nat) (res: (nat * nat * nat) + nat): iProp Σ.
refine (match n with
        |O    => ⌜res = inr n1⌝
        |S n' => ⌜res = inl (n', n2, Nat.add n1 n2)⌝ 
end)%I.
Defined.

(* one execution of fib either returns the addition and takes one from n
   or n is zero and returns the answer 
*)
Lemma verify_fib' n1 n2 n: 
    True -∗ wp_delay (fib' (n, n1, n2)) (post'' n1 n2 n).
Proof.
    iIntros "_".
    unfold fib'. unfold post''.
    destruct n.
    - by iApply wp_delay_return.
    - by iApply wp_delay_return.
Qed.

(* If i pick a particular n I can just unroll the loop n times*)
Lemma verify_delay_fib_brute:
    True -∗ @wp_delay Σ _ (fib 4) (λ ret, ⌜ret = 3⌝).
Proof.
    iIntros "_".
    unfold fib.
    iApply wp_delay_iter. 
    iApply wp_delay_return.
    iApply wp_delay_iter.
    iApply wp_delay_return.
    iApply wp_delay_iter.
    iApply wp_delay_return.
    iApply wp_delay_iter.
    iApply wp_delay_return.
    iApply wp_delay_iter.
    iApply wp_delay_return.
    done.
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
    unfold fib.
    iApply wp_delay_iter. 
    destruct n eqn: E.
    - iApply wp_delay_return. done.
    - iApply wp_delay_return. simpl. 
      iNext.
      iApply (wp_strong_mono_delay with "IH").
      unfold post'.
      iIntros (v Hv) "!%".
      simpl.

      iDestruct ("IH" $! n0 n2) as "IH'".
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