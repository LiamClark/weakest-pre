From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import state heapmodel.
Set Default Proof Using "Type".


Definition state_wp {Σ} {ST A} (SI: ST -> iProp Σ)
           (e: state ST A) (Φ: A -> iProp Σ): iProp Σ := ∀ σ,
  SI σ ==∗
  ∃ a σ', ⌜runState e σ = Some (a, σ') ⌝ ∗
          SI σ' ∗
          Φ a.

Section state_wp.
  Context  {Σ} {ST} (SI: ST -> iProp Σ).
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

  Lemma bupd_wp {A} (e: state ST A) Φ : (|==> state_wp SI e Φ) ⊢ state_wp SI e Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi".
    iMod "Hwp" as "Hwp".
    iDestruct ("Hwp" $! σ with "HSi" ) as "$".
  Qed.

  Lemma wp_bupd {A} (e: state ST A) Φ : state_wp SI e  (λ v, |==> Φ v) ⊢ state_wp SI e Φ.
  Proof.
    iIntros "Hwp".
    iApply (wp_strong_mono with "Hwp").
    auto.
  Qed.

  Lemma wp_ret {A} (v: A) Φ: Φ v ⊢ state_wp SI (mret v) Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi !>".
    eauto with iFrame.
  Qed.

  Lemma wp_bind {A B} (e: state ST A) (f: A -> state ST B) Φ:
    state_wp SI e (λ v, state_wp SI (f v) Φ) ⊢ state_wp SI (e ≫= f) Φ.
  Proof.
    iIntros "Hwp" (σ) "HSi /=".
    iMod ("Hwp" $! (σ) with "HSi") as (x σ' ->) "(HSi' & Hwp')".
    iMod ("Hwp'" $! (σ') with "HSi'") as (y σ'' ->) "(HSi'' & Hpost)".
    eauto with iFrame.
  Qed.

  (* The way the post condition gets implied here seems, dodgy? *)
  Lemma wp_getS Φ : (∀σ, SI σ ==∗ SI σ ∗ Φ σ) -∗ state_wp SI (getS) Φ.
  Proof.
    iIntros "Hpost" (σ) "Hsi".
    iMod("Hpost" with "Hsi") as "Hpost".
    iExists σ, σ. iModIntro.
    iSplit.
    - iPureIntro. done.
    - iFrame. 
  Qed.

  Lemma wp_modifyS {A} Φ (f: ST -> A * ST): 
    (∀σ, SI σ ==∗ let '(x, σ') := f σ in SI σ' ∗ Φ x) -∗ state_wp SI (modifyS f) Φ.
  Proof.
    iIntros "Hpost" (σ) "Hsi".
    iMod ("Hpost" with "Hsi") as "Hpost".
    destruct (f σ) as [x s'] eqn: E.
    iExists x, s'.
    iModIntro.
    iSplit.
    - unfold modifyS. simpl. rewrite E. done.
    - iFrame.
  Qed.

  Lemma wp_putS Φ σ' : (∀σ, SI σ ==∗ SI σ' ∗ Φ tt) -∗ state_wp SI (putS σ') Φ.
  Proof.
    iIntros "Hpost" (σ) "Hsi".
    iMod ("Hpost" with "Hsi") as "Hpost".
    iExists tt, σ'. iModIntro.
    iSplit.
    - iPureIntro. done.
    - iFrame.
  Qed.

  (*Derived rules *)
  Lemma wp_mono {A} Φ Ψ (e: state ST A): (∀ v, Φ v ⊢ Ψ v) → state_wp SI e Φ ⊢ state_wp SI e Ψ.
  Proof.
     iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
     iIntros (v) "?". by iApply HΦ.
  Qed.

  Lemma wp_value_bupd' {A} Φ (v: A) : (|==> Φ v) ⊢ state_wp SI (mret v) Φ.
  Proof. by rewrite -wp_bupd -wp_ret. Qed.

End state_wp.


Section state_wp_gp.
  Context `{! inG Σ (heapR A)}.
  Context (γ: gname).

  Lemma wp_get n v (Ψ: A -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ state_wp (state_interp γ) (get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_get with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_ret. by iApply "Hpost".
  Qed.

  Check is_Some.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ state_wp (state_interp γ) (put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost". unfold put. unfold modifyS'.
    iIntros (σ) "Hsi". 
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_put with "Hsi Hpt") as "(? & Hup)".
    iModIntro. simpl. rewrite Hsome. simpl.
    iExists tt, (<[n := v']> σ).
    iFrame. iSplit; try done.
    by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ state_wp (state_interp γ) (alloc v) Ψ.
  Proof.
    iIntros "Hpost". iApply wp_modifyS.
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "(Hsi' & Hpt)".
    iModIntro.
    iFrame.
    iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ state_wp (state_interp γ) (free l) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iIntros (σ) "Hsi".
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_free with "Hsi Hpt") as "Hsi".
    iModIntro. iExists tt, (delete l σ).
    iFrame. iPureIntro. simpl. by rewrite Hsome. 
  Qed.
End state_wp_gp.

Section state_ad.
  Context `{! inG Σ (heapR V)}.

  Lemma adequacy {A} (Q: A -> Prop) (prog : state (gmap nat V) A) (st: gmap nat V):
    (∀γ, ⊢ state_wp (state_interp γ) prog (λ x, ⌜Q x⌝)) ->
    ∃ x st', runState prog st = Some (x, st') /\ Q x.
  Proof.
    iIntros (Hpre).
    apply (uPred.pure_soundness (M := iResUR Σ)).
    iMod (own_alloc (● (lift_excl st))) as (γ) "Hγ".
    - apply auth_auth_valid. intro i. 
      rewrite lookup_fmap. destruct (st !! i); done.
    - iMod (Hpre γ $! st with "Hγ") as (x σ' ?) "(Hsi & %)".
      eauto 10.
  Qed.
End state_ad.

Section state_verification.
  Context `{! inG Σ (heapR nat)}.
  Definition prog_swap (l k: nat): state (gmap nat nat) unit := 
    x ← get l ;
    y ← get k ;
    put l y ;; put k x.

  Definition prog_swap' (l k: nat): state (gmap nat nat) unit := 
    get l ≫= λ x,
      get k ≫= λ y,  
        put l y ;; put k x.

  (*for linked lists 
    https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/countable.v#L21
  *)
  Lemma swap_verif l k x y :
   ∀γ Φ, points_to γ l x ∗ points_to γ k y -∗ 
       (points_to γ l y ∗ points_to γ k x -∗ Φ tt) -∗
       state_wp (state_interp γ) (prog_swap' l k) Φ. 
  Proof.
    iIntros (γ Φ) "Hpre Hpost".
    unfold prog_swap. 
    iDestruct "Hpre" as "(Hlx & Hky)".
    iApply wp_bind.
    iApply (wp_get with "Hlx"). iIntros "Hlx".
    iApply wp_bind.
    iApply (wp_get with "Hky"). iIntros "Hky".
    iApply wp_bind.
    iApply (wp_put with "Hlx"). iIntros "Hly".
    iApply (wp_put with "Hky"). iIntros "Hkx".
    iApply ("Hpost" with "*").
    iFrame.
    Qed.

  Lemma swap_verif' l k x y :
   ∀γ, points_to γ l x ∗ points_to γ k y -∗ 
       state_wp (state_interp γ) (prog_swap' l k) (λ _, points_to γ l y ∗ points_to γ k x). 
  Proof.
    iIntros (γ) "Hpre".
    unfold prog_swap. 
    iDestruct "Hpre" as "(Hlx & Hky)".
    iApply wp_bind.
    iApply (wp_get with "Hlx"). iIntros "Hlx".
    iApply wp_bind.
    iApply (wp_get with "Hky"). iIntros "Hky".
    iApply wp_bind.
    iApply (wp_put with "Hlx"). iIntros "Hly".
    iApply (wp_put with "Hky"). iIntros "Hkx".
    iFrame.
    Qed.
End state_verification.