From stdpp Require Import base. 
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From shiris.program_logic Require Import evaluation heapmodel itree itreewp.

Definition prog_swap  (l k: nat): expr nat unit := 
    x ← itree.get l ;
    y ← itree.get k ;
    itree.put l y ;; itree.put k x.

Definition loop_body {A}: unit -> expr nat A :=
  itree.iter (λ x, mret $ inl ()).

Definition loop_prog {A}: expr nat A :=
    loop_body ().

Variant cell :=
|Locked
|UnLocked.

Global Instance cell_inhabited: Inhabited (cell) := populate UnLocked.

Definition new_lock: expr cell loc :=
  alloc UnLocked.

Definition try_aquire (l: loc): expr cell bool :=
  snd <$> cmpXchg l UnLocked Locked.

Definition aqcuire_body (acq: bool): expr cell (() + ()) :=
  if acq then mret $ inr $ () else mret $ inl $ ().

Definition acquire (l: loc): expr cell () :=
  itree.iter 
    (λ _, try_aquire l ≫= aqcuire_body)  
    tt.

(* Definition acquire' (l: loc): expr cell () :=
  itree.iter 
    (λ _, try_aquire l ≫= (λ acq, if acq then mret $ inr $ () else mret $ inl $ ()))  
    tt. *)

Definition release (l: loc): expr cell () :=
  put l UnLocked.

Section lock_verification.
  Context `{! inG Σ (heapR cell)}.
  Context `{! invGS Σ}.
  Context {γ: gname}.

  Definition lock_inv (l: loc) (R: iProp Σ): iProp Σ :=
    (∃ c: cell, 
      points_to γ l c ∗
      match c with
      | Locked => True
      | UnLocked => R
      end
    )%I.

  Definition lockN: namespace := nroot .@ "lock".

  Definition is_lock (l: loc) (R: iProp Σ): iProp Σ :=
    inv lockN (lock_inv l R).
    
  (*
    texan triple
    ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ v, Φ v }}
  *)
  Lemma new_lock_spec (Φ: loc -> iProp Σ) (R: iProp Σ) (E: coPset):
    R -∗ (∀l, is_lock l R -∗ Φ l) -∗ wp (state_interp γ) E new_lock (Φ).
  Proof.
    iIntros "R Hpost". iApply wp_fupd.
    iApply wp_alloc. iIntros (l) "Hpt".
    iMod (inv_alloc lockN _ (lock_inv l R) with "[R Hpt]") as "Hinv".
    - iNext. iExists UnLocked. iFrame.
    - iModIntro. iApply ("Hpost"). done.
  Qed.


  Lemma try_aquire_spec (lk: loc) (Φ: bool -> iProp Σ) (R: iProp Σ):
    is_lock lk R -∗ (∀ b: bool, (if b then R else True) -∗ Φ b) -∗ wp (state_interp γ) ⊤ (try_aquire lk) Φ.
  Proof.
    iIntros "#Hlock HPost".
    unfold is_lock.
    unfold try_aquire. iApply wp_fmap. 
    iInv "Hlock" as "Hinv" "Hclose".
    unfold lock_inv.
    - apply vis_atomic.
    - iEval (unfold lock_inv) in "Hinv".
      iDestruct "Hinv" as (c) "[Hpt HR]".
      destruct (c) eqn: E.
      + iApply (wp_cmpXchg_fail' _ _ Locked with "[] Hpt"); try done.
        iIntros "!> Hpt".
        iMod ("Hclose" with "[Hpt]") as "_".
        { iNext. iExists Locked.  iFrame. }
        iModIntro. iSimpl. by iApply ("HPost" $! false).
      + iApply (wp_cmpXchg_suc' with "Hpt").
        iIntros "!> Hpt".
        iMod ("Hclose" with "[Hpt]") as "_".
        { iNext. iExists Locked.  iFrame. }
        iModIntro. iSimpl. iApply ("HPost" $! true with "HR") .
  Qed.
End lock_verification.