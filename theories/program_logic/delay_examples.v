From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import heapmodel delaystate delaywp.

(*Example programs

  fib' is our loop body.
  st is the state that we use between iterations of our computation.
  it's components are: (n, x, y) where
  n is the amount of fibonacci numbers we still need to create,
   once we reach 0 we yield our result.
  x is the current number
  y is the next number

  now why do we yield x and not y>
*)
Definition fib' (st: nat * nat * nat): delay ((nat * nat * nat) + nat) :=
    match st with
    |(0, x, y) => Answer $ inr $ x 
    |((S n), x, y) => Answer $ inl (n, y, x + y)
    end.

Definition fib (n: nat): delay nat := delaystate.iter fib' (n, 0, 1).

Lemma test_fib: (λ n, eval_delay 10 (fib n)) <$> [0; 1; 2; 3; 4; 5; 6; 7] = Some <$> [0; 1; 1; 2; 3; 5; 8; 13].
Proof.
  reflexivity.
Qed.

Fixpoint coq_fib (a b: nat) (n: nat): nat :=
  match n with
  |O => a 
  |S n' => match n' with
           | O => b 
           | S n'' => (coq_fib a b n') + (coq_fib a b n'')
           end
  end.

Lemma test_coq_fib:
  (coq_fib 0 1) <$>[0; 1; 2; 3; 4; 5; 6; 7] = [0; 1; 1; 2; 3; 5; 8; 13].
Proof.
  reflexivity.
Qed.

Lemma test_coq_fib_move: coq_fib 13 21 4 = coq_fib 5 8 (S (S 4)).
Proof.
  reflexivity.
Qed.

Section delay_verif.
  Context `{! inG Σ (heapR natO)}.
  
  Definition post' (x y n: nat) (ret: nat): iProp Σ :=
    ⌜ret = coq_fib x y n⌝%I.
  
  Definition post (n ret: nat): iProp Σ := post' 0 1 n ret.
  
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
  
  Lemma coq_fib_move n1 n2 n:
   coq_fib n2 (n1 + n2) n = coq_fib n1 n2 (S n).
  Proof.
      induction n using pair_induction.
      - by rewrite Nat.add_comm.
      - by rewrite Nat.add_comm.
      - rewrite -> (coq_fib_unfold  n1 n2 (S (n))).
        rewrite <- IHn0.
        rewrite <- IHn.
        rewrite -> coq_fib_unfold.
        reflexivity.
  Qed.
  
  (* 
    To get lob induction to work we need the numbers that are passed
    between loop states to vary. This means the post condition needs the same generalisation.
  *)
  Lemma verify_delay_fib' x y n:
      ⊢ wp_delay (delaystate.iter fib' (n, x, y)) (post' x y n).
  Proof.
      iLöb as "IH" forall (n x y).
      iApply wp_delay_iter. destruct n as [| n'] eqn: E.
      - unfold fib'. iApply wp_delay_return. simpl. unfold post'.  simpl. done.
      - iApply wp_delay_return. simpl. 
        iNext.
        iApply (wp_strong_mono_delay with "IH").
        iIntros (v Hv) "!%". subst v.
        apply coq_fib_move.
  Qed.
  
  Lemma verify_delay_hoare_fib' x y n:
      ⊢ hoare_delay True (delaystate.iter fib' (n, x, y)) (post' x y n).
  Proof.
    iLöb as "IH" forall (n x y).
    iApply (hoare_delay_iter _ 
      (λ '(n',x',y'), hoare_delay True (delaystate.iter fib' (n', x', y')) (post' x y n))
    ).
     destruct n as [| n'] eqn: E.
    - simpl.  iApply hoare_delay_mret'. iIntros "!> _".
      done.
    - simpl. iApply hoare_delay_mret'. iIntros "!> _". simpl.
      iNext.
      iApply (hoare_delay_consequence True _); try done.
      iIntros "!>" (res H). iPureIntro. subst res. apply coq_fib_move.
    - iIntros ([[n' y'] x']).
      iApply (hoare_delay_consequence_l (True ∗ _)).
      + iIntros "!> H". iSplit. done. iApply "H".
      + iApply (hoare_delay_ctx' True _).
        iIntros "!> !> Hhd".
        done.
  Qed.
  
  Lemma verify_delay_fib n:
      ⊢ wp_delay (fib n) (post n).
  Proof.
      unfold fib. unfold post.
      apply (@verify_delay_fib' 0 1 n).
  Qed.
  
  Definition fib_state' (l1 l2: nat) (n: nat): state_delay (gmap nat nat) (nat + nat) :=
    match n with
    | S n' => n1 ← get l1 ;
              n2 ← get l2 ;
              put l1 n2 ;; put l2 (n1 + n2) ;; mret $ inl n'
    | O => inr <$> get l1
    end.
  
  Lemma verify_delay_state_fib' l1 l2 n1 n2 n:
    ∀ γ, points_to γ l1 n1 ∗ points_to γ l2 n2 -∗
            wp (state_interp γ) (iter_state_delay (fib_state' l1 l2) n) (post' n1 n2 n).
  Proof.
      iIntros (γ) "(Hl1 & Hl2)".
      iLöb as "IH" forall (n n1 n2).
      iApply wp_iter.
      destruct n as [| n'] eqn: E.
      - iApply wp_fmap. iApply (wp_get with "Hl1").
        iIntros "Hl1". done.
      -
       iApply wp_bind. iApply (wp_get with "Hl1"). iIntros "Hl1".
       iApply wp_bind. iApply (wp_get with "Hl2"). iIntros "Hl2".
       iApply wp_bind. iApply (wp_put with "Hl1"). iIntros "Hl1".
       iApply wp_bind. iApply (wp_put with "Hl2"). iIntros "Hl2".
       iApply wp_return. 
       iNext. 
       iSpecialize ("IH" with "Hl1 Hl2").
       iApply (wp_strong_mono with "IH").
       iIntros (v Hv) "!%". subst v.
       apply coq_fib_move.
  Qed.
  
  Definition fib_state (n: nat): state_delay (gmap nat nat) nat := 
      l1 ← alloc 0 ;
      l2 ← alloc 1 ;
      iter_state_delay (fib_state' l1 l2) n.
  
  Lemma verify_delay_state_fib γ n:
       ⊢ wp (state_interp γ) (fib_state n) (post n).
  Proof.
      iApply wp_bind. iApply wp_alloc. iIntros (l1) "Hl1".
      iApply wp_bind. iApply wp_alloc. iIntros (l2) "Hl2".
      iApply verify_delay_state_fib'. iFrame.
  Qed.
End delay_verif.

Definition loop_body {A}: unit -> delay A :=
  delaystate.iter (λ x, mret $ inl ()).

Definition loop_prog {A}: delay A :=
    loop_body ().

Section loop_verif.
  Context `{! inG Σ (heapR natO)}.

  Lemma loop_verif {A}: 
    ⊢ @wp_delay Σ A loop_prog (λ _, False).
  Proof.
    iLöb as "IH".
    iApply wp_delay_iter.
    iApply wp_delay_return.
    simpl.
    iApply "IH". 
  Qed.
End loop_verif.