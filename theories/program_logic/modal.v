From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Import derived.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Import derived_laws_later plainly.
Import derived_laws_later.bi.

Set Default Proof Using "Type".


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

(* Lemma later_bupdN_soundness' {Σ} (n: nat) (φ: Prop):
  (Nat.iter n (λ P: iProp Σ, |==> ▷ P) (⌜φ⌝)) -∗ ⌜φ⌝.
Proof.
  induction n as [|n IH]; iIntros "H".
  - by rewrite -bupd_intro -except_0_intro.
  - rewrite Nat_iter_S. rewrite step_bupd_bupd.
    iDestruct (IH with "H") as "H'".
    rewrite !bupd_trans. 
    by iDestruct (bupd_step_bupd with "H'") as "H''".
Qed. *)


(* The version in fancy updates has an extra bupd around φ does that matter? *)
(*found in iris/baselogic/lib/fancyupdate *)
Lemma later_bupdN_soundness {M} (n: nat) (φ: Prop):
  (⊢@{uPredI M} Nat.iter n (λ P, |==> ▷ P) (⌜φ⌝)) -> φ.
Proof.
  intro H.
  apply (@uPred.soundness M _ (S n)).
  iPoseProof (H) as "H'".
  induction n. 
  - done.
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

Lemma nlaters' {Σ} (n: nat) (Q: iProp Σ):
 Q ⊢ Nat.iter n (λ P : iPropI Σ, |==> ▷ |==> P) Q.
Proof.
  iIntros "Q".
  induction n.
  - done.
  - iModIntro. iNext. iModIntro. done.
Qed.

(* Search fupd. *)

(* 
  This was convenient but let's cover this with Robbert
*)
Lemma fupd_nlaters {Σ} `{!invG Σ} (n: nat) (E1 E2: coPset) (Q: iProp Σ):
  E2 ⊆ E1 ->
  Q ⊢ Nat.iter n (λ P : iPropI Σ, |={E1, E2}=> ▷ |={E2, E1}=> P) Q.
Proof.
  iIntros (Hsub) "Q".
  iApply step_fupdN_intro; first done.
  by iApply laterN_intro.
Qed.

Lemma step_bupdN_plain' {M} n (φ: Prop): 
  (⊢@{uPredI M}(Nat.iter n (λ P, |==> ▷ |==> P) ⌜φ⌝) ==∗ ▷^n ◇ ⌜φ⌝).
Proof.
  induction n as [|n IH]; iIntros "H".
  - by rewrite -bupd_intro -except_0_intro.
  - rewrite Nat_iter_S. rewrite step_bupd_bupd.
    iDestruct (IH with "H") as "H'".
    rewrite !bupd_trans. 
    by iDestruct (bupd_step_bupd with "H'") as "H''".
Qed.

Lemma later_bupdN_soundness' {M} (n: nat) (φ: Prop):
  (⊢@{uPredI M} Nat.iter n (λ P, |==> ▷ |==> P) (⌜φ⌝)) -> φ.
Proof.
  intro H.
  apply (@uPred.soundness M _ (S n)).
  iPoseProof (H) as "H'".
  induction n. 
  - done.
  - 
    iDestruct (step_bupdN_plain' with "H'") as "H''".
    iApply bupd_plain.
    iMod "H''". iModIntro. iNext.
    rewrite -later_laterN laterN_later.
    iNext. by iMod "H''". 
Qed.

Lemma later_bupdN_soundness'' {M} (n: nat) (φ: Prop):
  (⊢@{uPredI M} |==> Nat.iter n (λ P, |==> ▷ |==> P) (⌜φ⌝)) -> φ.
Proof.
  intro H.
  apply (@uPred.soundness M _ (S n)).
  iPoseProof (H) as "H'".
  induction n. 
  - simpl. iNext. 
    iApply bupd_plain. 
    done.
  - 
    iDestruct (step_bupdN_plain' with "H'") as "H''".
    iApply bupd_plain.
    iMod "H''". iMod "H''". iModIntro. iNext.
    rewrite -later_laterN laterN_later.
    iNext. by iMod "H''". 
Qed.

Lemma lift_entails {Σ} (P Q: iProp Σ): (P ⊢ Q) -> ((⊢ P) -> (⊢ Q)).
Proof.
  unfold bi_emp_valid.
  intros H H2.
  by trans P.
Qed.