From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
Set Default Proof Using "Type".

Record state (ST A: Type): Type := State {
                                      runState: ST -> option (A * ST)
                                     }.


Arguments State {_ _} _.
Arguments runState {_ _} _.
Instance mret_state ST : MRet (state ST) := λ A a, State $ λ s, Some (a, s).
(* 
Definition mret {A} (x: A): State A := fun m => (x, m).
Definition mbind {A B} (e: State A) (f: A -> State B) :=
  fun m => let '(x, m') := e m in f x m'.
(* rewrite in terms of bind and re proof seq-wp-rule. *)
Definition seq {A B} (e: State A) (e2: State B): State B :=
  fun m => let '(_, m') := e m in e2 m'.
Definition get (l: loc) : State nat :=  λ h , (maybe (mlookup h l) 0, h).
Definition put (l: loc) (v : nat) : State unit :=  λ h, (tt, minsert l v h).
Definition alloc (v: nat) : State loc := (λ h, let loc := msize h in (loc, (minsert loc v h))).
Definition free (l: loc): State unit := λ h, (tt, mdelete l h).

 *)

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
End state_wp.
