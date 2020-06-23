From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import state.
Set Default Proof Using "Type".


Definition state_wp `{invG Σ} {ST A} (SI: ST -> iProp Σ)
           (e: state ST A) (Φ: A -> iProp Σ): iProp Σ := ∀ σ,
  SI σ ==∗
  ∃ a σ', ⌜runState e σ = Some (a, σ') ⌝ ∗
          SI σ' ∗
          Φ a.

Section state_wp.
  Context `{invG Σ} {ST} (SI: ST -> iProp Σ).
  Implicit Types P Q R: iProp Σ.

  (*
    Definable: wp_ret, wp_bind, wp_get, wp_put. Derived rules from heaplang wps.
    Define: fail as operation

    For multiheap look at: base-logic/lib/genheap.v
   *)

  Global Instance wp_ne {A} (e: state ST A) n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (state_wp SI e).
  Proof. solve_proper. Qed.

  Global Instance wp_proper {A} (e: state ST A):
    Proper (pointwise_relation _ (≡) ==> (≡)) (state_wp SI e).
  Proof. solve_proper. Qed.

  Lemma wp_strong_mono {A} (e: state ST A) Φ Ψ :
    state_wp SI e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ state_wp SI e Ψ.
  Proof.
    iIntros "Hwp H" (σ) "Hsi".
    iMod ("Hwp" $! σ with "Hsi") as (a σ') "(Hrun & HSi & HPhi)".
    iDestruct ("H" $! a with "HPhi") as "HPsi".
    iMod "HPsi" as "HPsi".
    eauto with iFrame.
  Qed.


  Lemma fupd_wp {A} (e: state ST A) Φ : (|==> state_wp SI e Φ) ⊢ state_wp SI e Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi".
    iMod "Hwp" as "Hwp".
    iDestruct ("Hwp" $! σ with "HSi" ) as "$".
  Qed.

  Lemma wp_fupd {A} (e: state ST A) Φ : state_wp SI e  (λ v, |==> Φ v) ⊢ state_wp SI e Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi".
    iMod ("Hwp" $! σ with "HSi") as (a σ') "(Hrun & HSi & HPhi)".
    iMod "HPhi" as "HPhi".
    eauto with iFrame.
  Qed.

  Lemma wp_ret {A} (v: A) Φ: Φ v ⊢ state_wp SI (mret v) Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi".
    iModIntro.
    iExists v, σ.
    eauto with iFrame.
  Qed.

  Lemma wp_bind {A B} (e: state ST A) (f: A -> state ST B) Φ:
    state_wp SI e (λ v, state_wp SI (f v) Φ) ⊢ state_wp SI (e ≫= f) Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi".
    iMod ("Hwp" $! (σ) with "HSi") as (x σ') "(Hrun & HSi' & Hwp')".
    iMod ("Hwp'" $! (σ') with "HSi'") as (y σ'') "(Hrun' & HSi'' & Hpost)".
    iModIntro.
    iExists y, σ''.
    simpl.
    iDestruct "Hrun" as %->.
    iDestruct "Hrun'" as %->.
    eauto with iFrame.
  Qed.


End state_wp.
