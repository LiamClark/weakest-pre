From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import delaystate.
Set Default Proof Using "Type".

(*
  We run into the same problem here as with the evaluator for state_delay: 
  We need the state aspect for our state interpretation and our notion of separation.
  We need to get to the Think constructor to recurse in our wp definition on the sub expression.
  However once we get to the Think node, although it does contain pre_wired stateful operations they are now
  completely opaque to us.

  In the evaluator we work around this by having the (co-)recursion only work for the delay monad
  Then add state on top as an extra layer. Can we write a wp that works just for delay?
*)

Definition wp_delay_pre {Σ} {A} (go: delay A -d> (A -d> iPropO Σ) -d> iPropO Σ):
      delay A -d> (A -d> iPropO Σ) -d> iPropO Σ.
refine(λ e Φ, |==> match e with
                   | Answer x => Φ x
                   | Think e' => ▷ go e' Φ
                   end
              )%I.
Defined.

Instance wp_delay_pre_contractive {Σ A}: Contractive (@wp_delay_pre Σ A ).
Proof.
  rewrite /wp_delay_pre => n wp wp' Hwp e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.
 
Definition wp_delay {Σ} {A}: delay A -> (A -> iProp Σ)-> iProp Σ := fixpoint wp_delay_pre.

Definition wp {Σ} {ST A} (SI: ST -> iProp Σ) (e: state_delay ST A) (Φ: A -> iProp Σ): iProp Σ.
refine(∀ σ, 
    SI σ ==∗
     wp_delay (runState e σ) (λ (res: option (ST * A)), 
       match res with   
       | Some (σ', x) => SI σ' ∗ Φ x 
       | None => True
       end)
)%I.
Defined.

Lemma wp_delay_unfold {Σ A} (e: delay A) (Φ: A -> iProp Σ): wp_delay e Φ ≡ wp_delay_pre wp_delay e Φ.
Proof.
  apply (fixpoint_unfold wp_delay_pre).
Qed.

Lemma wp_delay_return {Σ A}(x: A) (Φ: A -> iProp Σ): Φ x -∗ wp_delay (Answer x) Φ.
Proof.
   rewrite wp_delay_unfold.
   iIntros "H".
   iModIntro. done.
Qed.

Lemma wp_delay_think {Σ A}(e: delay A) (Φ: A -> iProp Σ): ▷ wp_delay e Φ -∗ wp_delay (Think e) Φ.
Proof.
  iIntros "Hwp".
  iEval(rewrite wp_delay_unfold). unfold wp_delay_pre.
  done.
Qed.

Lemma wp_delay_bind {Σ A B} (f: A -> delay B) (Φ: B -> iProp Σ) (e: delay A): 
  wp_delay e (λ x, wp_delay (f x) Φ) -∗ wp_delay (e ≫= f) Φ.
Proof.
  unfold mbind, mbind_delay.
  iIntros "H". iLöb as "IH" forall (e).
  iEval (rewrite wp_delay_unfold).
  unfold wp_delay_pre.
  destruct e; simpl.
  - rewrite wp_delay_unfold /=. iMod "H" as "H". rewrite wp_delay_unfold /=.
    unfold wp_delay_pre. done.
  - iEval (rewrite wp_delay_unfold /=) in "H".
    iMod "H" as "H".
    iModIntro.
    iNext. iApply "IH". done.
Qed.


Lemma wp_strong_mono_delay {Σ A} (e: delay A) (Φ Ψ: A -> iProp Σ) :
  wp_delay e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp_delay e Ψ.
Proof.
  iLöb as "IH" forall (e).
  rewrite wp_delay_unfold.
  rewrite wp_delay_unfold.
  iIntros "Hwp H".
  unfold wp_delay_pre.
  destruct e; simpl.
  - iMod "Hwp" as "Hwp". iApply ("H" with "Hwp").
  - iMod "Hwp" as "Hwp". iModIntro.
    iNext. iApply ("IH" $! e with "Hwp H"). 
Qed.

Lemma wp_delay_fmap {Σ A B} (f: A -> B) (Φ: B -> iProp Σ) (e: delay A): 
  wp_delay e (Φ ∘ f ) -∗ wp_delay (f <$> e) Φ. 
Proof.
  iIntros "Hwp".
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros (x) "Hpost !> /=".
  by iApply wp_delay_return.
Qed.

Lemma wp_delay_iter {Σ A B} (Φ: B -> iProp Σ)
  (x: A)
  (f: A -> delay (A + B)):
  wp_delay (f x) (case_ (λ x, ▷ wp_delay (iter f x) Φ) Φ) -∗
  wp_delay (iter f x) Φ.
Proof.
  iIntros "Hwp".
  rewrite iter_unfold.
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([a | b]) "H !> /=".
  - by iApply wp_delay_think.
  - by iApply wp_delay_return.
Qed.


Lemma bupd_wp_delay {Σ A} (e: delay A) (Φ : A -> iProp Σ) : (|==> wp_delay e Φ) ⊢ wp_delay e Φ.
Proof.
  iIntros "Hwp".
  rewrite wp_delay_unfold.
  unfold wp_delay_pre.
  by iMod "Hwp" as "Hwp".
Qed.

Lemma wp_bupd_delay {Σ A} (e: delay A) (Φ : A -> iProp Σ) : wp_delay e (λ v, |==> Φ v) ⊢ wp_delay e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono_delay with "Hwp").
  auto.
Qed.

Check uPred.later_soundness.
Locate uPred.later_soundness.
Check step_fupdN_soundness.


From iris.bi Require Import derived_laws_later plainly.
Import derived_laws_later.bi.

Lemma step_bupd_bupd {M} φ:
  ((|==> ▷ φ) ⊢@{uPredI M} |==> ▷ |==> φ).
Proof.
  iIntros "H".
  iMod "H" as "H'". 
  iModIntro.
  by rewrite -bupd_intro.
Qed.

Lemma bupd_plain_later {M} (φ: Prop):
  (⊢@{uPredI M} (▷ |==> ⌜φ⌝) ==∗ ▷ ◇ ⌜φ⌝).
Proof.
  iIntros "H".
  iModIntro. iNext.
  iApply bupd_plain. 
  by iMod "H" as "H'".
Qed.

Lemma step_bupd_plain {M} φ `{!Plain φ}:
  (⊢@{uPredI M} (|==> ▷ φ) ==∗ ▷ ◇ φ).
Proof.
  iIntros "H".
  iMod "H" as "H'".
  iModIntro. iNext.
  done.
Qed.

Lemma bupd_step_bupd {M} n φ:
  (⊢@{uPredI M} (|==> ▷ (|==> ▷^n ◇ ⌜φ⌝)) -∗ (|==> ▷ ▷^n ◇ ⌜φ⌝)) .
Proof.
  iIntros "H".
  iMod "H" as "H". iModIntro. iNext.
  by iApply bupd_plain.
Qed.

Check bupd_trans.
Lemma step_bupdN_plain {M} n (φ: Prop): 
  (⊢@{uPredI M}(Nat.iter n (λ P, |==> ▷ P) ⌜φ⌝) ==∗ ▷^n ◇ ⌜φ⌝).
Proof.
  induction n as [|n IH]; iIntros "H".
  - by rewrite -bupd_intro -except_0_intro.
  - rewrite Nat_iter_S. rewrite step_bupd_bupd.
    iDestruct (IH with "H") as "H'".
    rewrite !bupd_trans. 
    by iDestruct (bupd_step_bupd with "H'") as "H''".
Qed.

(* The version in fancy updates has an extra bupd around φ does that matter? *)
(*found in iris/baselogic/lib/fancyupdate *)
Lemma later_bupdN_soundness {M} (n: nat) (φ: Prop):
  (⊢@{uPredI M} Nat.iter n (λ P, |==> ▷ P) (⌜φ⌝)) -> φ.
Proof.
  intro H.
  apply (@uPred.soundness M _ (S n)).
  iPoseProof (H) as "H'".
  induction n. 
  - 
    done.
   (* simpl in *. *)
   (* iApply bupd_plain. *)
   (* by iMod "H'" as %H'. *)
  - 
    iDestruct (step_bupdN_plain with "H'") as "H''".
    iApply bupd_plain.
    iMod "H''" as "H''". iModIntro. iNext.
    rewrite -later_laterN laterN_later.
    iNext. by iMod "H''". 
Qed.

Lemma nlaters {Σ} (n: nat) (Q: iProp Σ):
 Q ⊢ Nat.iter n (λ P : iPropI Σ, |==> ▷ P) Q.
Proof.
  iIntros "Q".
  induction n.
  - done.
  - iModIntro. iNext. done.
Qed.

(* (⊢ ▷ P) -> (⊢ P) *)
(* (∀n, P (n - 1)) -> (∀n, P n) *)
(* 
 H: (∀n, P (n - 1)) 
 n
 P n 
*)
(* (▷ P ⊢ P) *)

(* 
  (⊢ |==> P) -> (⊢ P )
  (∀res, ∀f, ∃res', res = f + res' -> P (res' * f)) -> (∀ res,  P res)
  
  (|==> P ⊢ P)

*)

Lemma adequacy_delay_own_try {A} {Σ} (φ: A -> Prop) (n: nat) (x: A) (prog : delay A):
    (⊢ @wp_delay Σ A prog (λ x, ⌜φ x⌝)) ->
    eval_delay n prog = Some x -> φ x.
Proof.
  revert prog.
  intros prog Hpre Heval.
  (* apply (@later_bupdN_soundness (iResUR Σ) n). *)
  revert Heval Hpre.
  revert prog.
  induction n as [|n' IHn]; intros prog Heval Hpre; simplify_eq/=.
  rewrite -> wp_delay_unfold in Hpre.
  unfold wp_delay_pre in Hpre.
  destruct prog.
  simplify_eq/=.
  -
    apply (uPred.pure_soundness (M := iResUR Σ)).
    iMod Hpre as "H". done.
  - 
    apply (@later_bupdN_soundness (iResUR Σ) (S n')). simpl.
    iMod Hpre as "H". iModIntro.
    iNext. 
Admitted.

(* |==> ▷ wp_delay prog (λ x: A, ⌜ φ x ⌝) ⊢ |==> ▷ Nat.iter n' (λ P, |==> ▷ P) ⌜ φ x⌝) ->
wp_delay prog (λ x: A, ⌜ φ x ⌝) ⊢ Nat.iter n' (λ P, |==> ▷ P) ⌜ φ x⌝) *)

(* 
r1: (⊢ P) -> (⊢ Q)
   (∀n, P n) -> (∀n, Q n)

   (∀n, P n -> Q n)
r2:   P ⊢ Q

r1 -> r2
  H:((∀n, P n) -> (∀n, Q n))
  n
  H2: P n
  Q n

r2 -> r1
  H:   P n -> Q n)
  H2:  P n)
  n
  Q n

(P ⊢ Q) -> ((True ⊢ P) -> (True ⊢ Q))
H: (P ⊢ Q) 
H2: (True ⊢ P)
(True ⊢ Q)
entail_trans H2 H
True ⊢ Q
*)
Print Transitive.
Lemma lift_entails {Σ} (P Q: iProp Σ): (P ⊢ Q) -> ((⊢ P) -> (⊢ Q)).
Proof.
  unfold bi_emp_valid.
  intros H H2.
  by trans P.
Qed.

Lemma adequacy_delay {A} {Σ} (φ: A -> Prop) (n: nat) (x: A) (prog : delay A):
    (⊢ @wp_delay Σ A prog (λ x, ⌜φ x⌝)) ->
    eval_delay n prog = Some x -> φ x.
Proof.
  revert prog.
  intros prog Hpre Heval.
  apply (@later_bupdN_soundness (iResUR Σ) n).
  revert Hpre.
  apply lift_entails.
  iIntros "Hpre".
  iInduction n as [|n'] "IH" forall (prog Heval).
  - done.
  - simpl in *.
    rewrite wp_delay_unfold.
    unfold wp_delay_pre.
    destruct prog as [a| prog']; simplify_eq/=.
    +  iMod "Hpre" as %Hpre.
       iModIntro. iNext.
       by iApply nlaters.
    + iMod "Hpre". iModIntro. iNext.
      by iApply "IH".



  rewrite -> wp_delay_unfold in Hpre.
  unfold wp_delay_pre in Hpre.
  destruct prog.
  simplify_eq/=.
  - 
    (* how do I strip the n modalities here*)
    iMod Hpre as "H".
    iModIntro. iNext.
    admit. 


  simpl in Hpre.

Qed.


Lemma wp_strong_mono {Σ A ST SI} (e: state_delay ST A) (Φ Ψ : A -> iProp Σ):
  wp SI e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp SI e Ψ .
Proof.
  unfold wp.
  iIntros "Hwp H" (σ) "HSi".
  iDestruct ("Hwp" with "HSi") as "Hwp".
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([[s x] | ]). 
  - iIntros "($ & HPost)".
    by iApply "H".
  - done.
Qed.

Lemma bupd_wp {Σ A ST SI} (e: state_delay ST A) (Φ : A -> iProp Σ): (|==> wp SI e Φ) ⊢ wp SI e Φ.
Proof.
  iIntros "Hwp".
  unfold wp. iIntros (σ) "Hsi". 
  by iMod ("Hwp" with "Hsi").
Qed.

Lemma wp_bupd {Σ A ST SI} (e: state_delay ST A) (Φ : A -> iProp Σ): wp SI e (λ v, |==> Φ v) ⊢ wp SI e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono with "Hwp").
  auto.
Qed.


Lemma wp_return {Σ A ST } {SI: ST -> iProp Σ} (x: A) (Φ: A -> iProp Σ): Φ x -∗ wp SI (mret x) Φ.
Proof.
  iIntros "H" (σ) "HSi".
  simpl.
  iApply wp_delay_return. by iFrame.
Qed.

Locate "|==>".
Print bupd.
Lemma wp_bind {Σ A B ST} {SI: ST -> iProp Σ}
  (f: A -> state_delay ST B)
  (Φ: B -> iProp Σ)
  (e: state_delay ST A)
  : wp SI e (λ x, wp SI (f x) Φ) -∗ wp SI (e ≫= f) Φ.
Proof.
  iIntros "H" (σ) "HSi". rewrite /mbind /mbind_state_delay /=.
  iApply wp_delay_bind.
  iMod ("H" with  "HSi") as "H".
  iModIntro.
  iApply (wp_strong_mono_delay with "H").
  iIntros ([[s x] | ]).
  - iIntros "(HSi & Hwp)".
    unfold wp. iApply ("Hwp" $! (s) with "HSi").
  - iIntros "_ !>".
    by iApply wp_delay_return.
Qed.

Section state_wp.
  Context {Σ} {ST} (SI: ST -> iProp Σ).

 Lemma wp_iter {A B} (Φ: B -> iProp Σ)
  (x: A)
  (f: A -> state_delay ST (A + B)):
  wp SI (f x) (case_ (λ x, ▷ wp SI (iter_state_delay f x) Φ) Φ) -∗
  wp SI (iter_state_delay f x) Φ.
Proof.
  iIntros "Hwp" (σ) "Hsi".
  iApply wp_delay_iter.
  iMod ("Hwp" $! (σ) with "Hsi") as "Hwp /=".
  iModIntro.
  unfold distribute_delay_state.
  iApply wp_delay_fmap.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([[s [a| b]]| ]) "Hpost /="; [ |auto..].
  iDestruct "Hpost" as "(Hsi & Hwp')".
  iIntros "!> !>".
  unfold iter_state_delay.
  unfold distribute_delay_state.
  iApply bupd_wp_delay.
  iMod ("Hwp'" with "Hsi") as "Hwp' /= ".
  iModIntro.
  done.
Qed. 

Lemma wp_getS Φ : (∀σ, SI σ ==∗ SI σ ∗ Φ σ) -∗ wp SI (getS) Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost".
  by iApply wp_delay_return.
Qed.

Lemma wp_modifyS' {A} Φ (f: ST -> ST * A): 
  (∀σ, SI σ ==∗ let '(σ', x) := f σ in SI σ' ∗ Φ x) -∗ wp SI (modifyS' f) Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost /=".
  destruct (f σ) as [x s'].
  by iApply wp_delay_return.
Qed.

Lemma wp_modifyS Φ f: (∀σ, SI σ ==∗ SI (f σ) ∗ Φ tt) -∗ wp SI (modifyS f) Φ.
Proof.
  iIntros "Hpost". 
  iApply wp_modifyS'. done.
Qed.

Lemma wp_putS Φ σ' : (∀σ, SI σ ==∗ SI σ' ∗ Φ tt) -∗ wp SI (putS σ') Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost /=".
  by iApply wp_delay_return.
Qed.
End state_wp.

(*Heap rules *)
Definition heapR (A: ofeT): cmraT := authR (gmapUR nat (exclR A)).

Lemma fresh_none (σ: gmap nat nat): 
  let l := fresh (dom (gset nat) σ)
  in σ !! l = None.
Proof.
  apply (not_elem_of_dom (D := gset nat)).
  apply is_fresh.
Qed.

Section state_wp_gp.
  Context `{! inG Σ (heapR natO)}.

 (* Now come the rule that needs the points to connective in their weakest pre definition.
     We therefore first define this in terms of the Authorative camera.
   *)

  Definition points_to (γ: gname) (n: nat) (v: nat): iProp Σ :=
    own γ ( ◯ {[ n := Excl v ]}).

  Definition lift_excl (σ: gmap nat nat): (gmap nat (excl nat)) := (Excl <$> σ).
  Definition state_interp (γ: gname) (σ: gmap nat nat) := own γ (● (lift_excl σ)).
  Context (γ: gname).

  Lemma rewrite_lookups σ n v : lift_excl σ !! n ≡ Excl' v -> (σ !! n) = Some v.
  Proof.
    intros H.
    rewrite (lookup_fmap Excl σ n) in H.
    destruct (leibniz_equiv_iff (Excl <$> σ !! n) (Excl' v)).
    apply H0 in H.
    destruct (σ !! n) eqn: E.
    - injection H. auto.
    - done.
  Qed.

  Lemma si_points_to_agree σ n v: state_interp γ σ -∗ points_to γ n v -∗ ⌜σ !! n = Some v⌝.
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp. unfold points_to.
    iDestruct (own_valid_2 with "Hsi Hpt") as "%".
    pose (cmr := (gmapUR nat (exclR natO))).
    pose (proj1 (@auth_both_valid cmr _ (lift_excl σ) ({[n := Excl v]}))).
    destruct (a H) as [H1 H2].
    iPureIntro.
    pose (proj1 (singleton_included_exclusive_l (lift_excl σ) n (Excl v) _ H2) H1).
    apply rewrite_lookups.
    assumption.
  Qed.

  Lemma lift_excl_some σ n v: σ !! n = Some v -> lift_excl σ !! n = Some (Excl v).
  Proof.
    intro H.
    rewrite lookup_fmap. rewrite H.
    reflexivity.
  Qed.

  Lemma points_to_update σ n v w:
    state_interp γ σ -∗ points_to γ n v ==∗ state_interp γ (<[n := w ]> σ) ∗ points_to γ n w.
  Proof.
    iIntros "Hsi Hpt".
    iDestruct (si_points_to_agree with "Hsi Hpt") as "%".
    unfold state_interp. unfold points_to.
    iApply own_op.
    iApply (own_update_2 with "Hsi Hpt").
    apply auth_update. unfold lift_excl.
    rewrite fmap_insert.
    eapply singleton_local_update.
    * apply lift_excl_some. apply H.
    * apply exclusive_local_update.
      done.
    Qed.

  Lemma si_alloc σ v:
    let l := fresh (dom (gset nat) σ)
    in  state_interp γ σ ==∗ state_interp γ (<[l := v ]> σ) ∗ points_to γ l v.
  Proof.
    iIntros "Hsi".
    iApply own_op.
    iApply (own_update with "Hsi").
    -  apply auth_update_alloc.
       unfold lift_excl. rewrite fmap_insert. 
       apply alloc_singleton_local_update.
       + rewrite lookup_fmap. rewrite fresh_none. done.
       + done. 
  Qed.

  Lemma si_free σ v l:
   state_interp γ σ -∗ points_to γ l v ==∗ state_interp γ (delete l σ).
  Proof.
    iIntros "Hsi Hpt".
    iApply (own_update).
    - apply auth_update_dealloc.
      unfold lift_excl. rewrite fmap_delete.
      apply (delete_singleton_local_update _ l (Excl v)).
    - iApply own_op.
      iFrame.
  Qed.

  Lemma wp_get n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ wp (state_interp γ) (get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_return. by iApply "Hpost".
  Qed.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ wp (state_interp γ) (put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_modifyS.
    iIntros (σ) "Hsi". 
    iMod (points_to_update with "Hsi Hpt") as "($ & Hup)". 
    by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ wp (state_interp γ) (alloc v) Ψ.
  Proof.
    iIntros "Hpost". iApply wp_modifyS'.
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "($ & Hpt)".
    iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ wp (state_interp γ) (free l) Ψ.
  Proof.
    iIntros "Hpt Hpost". iApply wp_modifyS.
    iIntros (σ) "Hsi".
    iMod (si_free with "Hsi Hpt") as "$".
    done.
  Qed.

End state_wp_gp.

