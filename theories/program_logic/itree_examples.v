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
|UnLocked
|Value (n: nat).

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
      | Nat => False
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
    iIntros "#Hlock Hpost".
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
        iModIntro. iSimpl. by iApply ("Hpost" $! false).
      + iApply (wp_cmpXchg_suc' with "Hpt").
        iIntros "!> Hpt".
        iMod ("Hclose" with "[Hpt]") as "_".
        { iNext. iExists Locked.  iFrame. }
        iModIntro. iSimpl. iApply ("Hpost" $! true with "HR") .
        + iApply (wp_cmpXchg_fail' _ _ (Value n) with "[] Hpt"); try done.
          iNext. iExFalso. iApply "HR".
    Qed.

  Lemma aqcuire_spec (lk: loc) (Φ: unit -> iProp Σ) (R: iProp Σ):
    is_lock lk R -∗ (R -∗ Φ tt) -∗ wp (state_interp γ) ⊤ (acquire lk) Φ.
  Proof.
    iIntros "#Hlock Hpost".
    iLöb as "IH".
    iApply wp_iter. iApply wp_bind. 
    iApply (try_aquire_spec with "Hlock"). 
    iIntros (b) "HR".
    destruct b.
    - iApply wp_return. iApply ("Hpost" with "HR"). 
    - iApply wp_return. iSimpl. iNext. iApply ("IH" with "Hpost").
  Qed.

  Lemma release_spec (lk: loc) (Φ: unit -> iProp Σ) (R: iProp Σ):
    (is_lock lk R ∗ R) -∗ (True -∗ Φ tt) -∗ wp (state_interp γ) ⊤ (release lk) Φ.
  Proof.
    iIntros "(#Hlock & Hr) Hpost".
    iInv "Hlock" as (c) "[Hl HR]" "Hclose".
    { apply vis_atomic. }
    iApply (wp_put' with "Hl").
    iIntros "!> Hpt".
    iMod ("Hclose" with "[Hpt Hr]") as "_".
    { iNext. iExists UnLocked. iFrame. } 
    by iApply "Hpost".
  Qed.

End lock_verification.

Section bank.

  Definition onValue (c: cell) (f: nat -> expr cell ()): expr cell () :=
    match c with
    | Locked => mret ()
    | UnLocked => mret ()
    | Value n => f n
    end.

  Definition getValue (c: cell) : expr cell (option nat) :=
    match c with
    | Locked => mret $ None 
    | UnLocked => mret $ None 
    | Value n => mret $ Some $  n
    end.


  Definition withdraw (amount: nat) (balanceLoc: loc): expr cell () :=
    balanceCell ← get balanceLoc;
    onValue balanceCell (λ balance, 
      if (amount <=? balance) 
      then put balanceLoc (Value (balance - amount)) else mret () 
    ).


  Definition withdrawLocked (amount: nat) (lockLoc: loc) (balanceLoc: loc): expr cell () :=
    acquire lockLoc ;; withdraw amount balanceLoc ;; release lockLoc.

  Definition bank_prog: expr cell (option nat) :=
    balanceLoc  ← alloc (Value 100) ; 
    lockLoc     ← new_lock ; 
    Fork 
      (withdrawLocked 5  lockLoc balanceLoc ;; withdrawLocked 25 lockLoc balanceLoc) 
      ( withdrawLocked 20 lockLoc balanceLoc ;;
        withdrawLocked 2  lockLoc balanceLoc ;;  
        withdrawLocked 10 lockLoc balanceLoc ;; 
        c ← get balanceLoc ;
        getValue c)
      .

End bank.


Section bank_verification.
  Context `{! inG Σ (heapR cell)}.
  Context `{! invGS Σ}.
  Context {γ: gname}.

  Locate "<=?".
  Search le Nat.leb.
  Check Nat.leb_le.

  Lemma withdraw_spec_suc n n' lval (Φ: () -> iProp Σ)
  : n' <= n ->
  points_to γ lval (Value n)
  -∗ (points_to γ lval (Value (n - n')) -∗ Φ ())
  -∗ wp (state_interp γ) ⊤ (withdraw n' lval) Φ.
  Proof.
    iIntros (Hle) "Hpt Hpost". 
    iApply wp_bind. iApply (wp_get with "Hpt"). iIntros "Hpt".
    iSimpl. apply Nat.leb_le in Hle. rewrite Hle.
    iApply (wp_put with "Hpt"). iApply "Hpost".
  Qed.

  Lemma withdraw_spec_fail n n' lval (Φ: () -> iProp Σ)
  : ¬(n' <= n) ->
  points_to γ lval (Value n)
  -∗ (points_to γ lval (Value n) -∗ Φ ())
  -∗ wp (state_interp γ) ⊤ (withdraw n' lval) Φ.
  Proof.
    iIntros (Hle) "Hpt Hpost". 
    iApply wp_bind. iApply (wp_get with "Hpt"). iIntros "Hpt".
    iSimpl. apply Nat.leb_nle in Hle. rewrite Hle.
    iApply wp_return. iApply ("Hpost" with "Hpt").
  Qed.

  Lemma withdraw_locked_suc_spec n n' lval llock (Φ: () -> iProp Σ)
  : n' <= n ->
  (@is_lock _ _ _ γ llock (points_to γ lval (Value n)))
  -∗ wp (state_interp γ) ⊤ (withdrawLocked n' llock lval) Φ.
  Proof.
    iIntros (Hle) "#Hlock". unfold withdrawLocked.
    iApply wp_bind. iApply (aqcuire_spec with "Hlock").
    iIntros "Hpt". iApply wp_bind. 
    iApply (withdraw_spec_suc _ _ _ _ Hle  with "Hpt"). iIntros "Hpt".
    iApply (release_spec with "Hlock" ).

  Admitted.


  Lemma bank_spec : ⊢ wp (state_interp γ) ⊤ (bank_prog) 
     (λ balanceOpt,
      match balanceOpt with
      | Some balance => ⌜balance = 38⌝
      | None => False
      end)%I.
  Proof.
    iApply wp_bind.
    iApply wp_alloc. iIntros (lval) "Hval".
    iApply wp_bind.
    iApply (new_lock_spec with "Hval"). iIntros (llock) "#Hinv".
    iApply wp_fork.
    - iNext. iApply wp_bind. iApply wp_a
    -
  Qed.
End bank_verification.