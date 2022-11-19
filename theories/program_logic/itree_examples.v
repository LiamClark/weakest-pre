From stdpp Require Import base. 
From iris.algebra Require Import lib.frac_auth numbers auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From shiris.program_logic Require Import evaluation heapmodel itree itreewp.

Definition prog_swap (l k: nat): expr nat unit := 
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

Definition try_acquire (l: loc): expr cell bool :=
  snd <$> cmpXchg l UnLocked Locked.

Definition acquire (l: loc): expr cell () :=
  itree.iter 
    (λ _, try_acquire l ≫= λ (b : bool), if b then mret $ inr $ () else mret $ inl $ ())
    tt.

Definition release (l: loc): expr cell () :=
  put l UnLocked.

Section lock_verification.
  Context `{! inG Σ (heapR cell)}.
  Context `{! invGS Σ}.
  Context {γ: gname}.

  Definition lock_inv (l: loc) (R: iProp Σ): iProp Σ :=
    ∃ c: cell, 
      points_to γ l c ∗
      match c with
      | Locked => True
      | UnLocked => R
      | Nat => False
      end.

  Definition lockN: namespace := nroot .@ "lock".

  Definition is_lock (l: loc) (R: iProp Σ): iProp Σ :=
    inv lockN (lock_inv l R).
    
  (*
    texan triple
    ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ v, Φ v }}
  *)
  Lemma new_lock_spec (Φ: loc -> iProp Σ) (R: iProp Σ) (E: coPset):
    R -∗ (∀l, is_lock l R -∗ Φ l) -∗ wp (state_interp γ) E new_lock Φ.
  Proof.
    iIntros "R Hpost". iApply wp_fupd.
    iApply wp_alloc. iIntros (l) "Hpt".
    iMod (inv_alloc lockN _ (lock_inv l R) with "[R Hpt]") as "Hinv".
    - iNext. iExists UnLocked. iFrame.
    - iModIntro. iApply "Hpost". done.
  Qed.

  Lemma try_aquire_spec (lk: loc) (Φ: bool -> iProp Σ) (R: iProp Σ):
    is_lock lk R -∗ (∀ b: bool, (if b then R else True) -∗ Φ b) 
    -∗ wp (state_interp γ) ⊤ (try_acquire lk) Φ.
  Proof.
    iIntros "#Hlock Hpost".
    unfold is_lock.
    unfold try_acquire. iApply wp_fmap. 
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
    is_lock lk R -∗ R -∗ Φ tt -∗ wp (state_interp γ) ⊤ (release lk) Φ.
  Proof.
    iIntros "#Hlock Hr Hpost".
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

  Definition as_value (c: cell): expr cell nat :=
    match c with
    | Locked => itree.fail
    | UnLocked => itree.fail 
    | Value n => mret n
    end.

  Definition withdraw (amount: nat) (balanceLoc: loc): expr cell bool :=
    balanceCell ← get balanceLoc ;
    balance ← as_value balanceCell ; 
    if (amount <=? balance) 
    then put balanceLoc (Value (balance - amount)) ;; mret true 
    else mret false.

  Definition withdraw_locked (amount: nat) (lockLoc: loc) (balanceLoc: loc): expr cell () :=
    acquire lockLoc ;; 
    b ← withdraw amount balanceLoc ;
    if b : bool then release lockLoc else itree.fail.

  Definition bank_prog: expr cell () :=
    balanceLoc  ← alloc (Value 100) ; 
    lockLoc     ← new_lock ; 
    fork (withdraw_locked 5 lockLoc balanceLoc ;; withdraw_locked 25 lockLoc balanceLoc) ;;
    withdraw_locked 20 lockLoc balanceLoc ;;
    withdraw_locked 2  lockLoc balanceLoc ;;
    withdraw_locked 10 lockLoc balanceLoc ;;
    mret tt.
End bank.

Class ccounterG Σ :=
  CCounterG { ccounter_inG : inG Σ (authR natUR) }.
Local Existing Instance ccounter_inG.

Definition ccounterΣ : gFunctors :=
  #[GFunctor (authR natUR)].

Global Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Section bank_verification.
  Context `{! inG Σ (heapR cell)}.
  Context `{! invGS Σ}.
  Context `{! ccounterG Σ }.
  Context {γ: gname}.

  Definition ccounter (γ: gname) (n: nat) :iProp Σ :=
      own γ (◯ n).

  Lemma ccounter_split (γc: gname) n1 n2 :
    ccounter γc (n1 + n2) ⊣⊢ ccounter γc n1 ∗ ccounter γc n2.
  Proof. by rewrite /ccounter auth_frag_op -own_op. Qed.

  Definition lock_payload (γc: gname) (l : loc) : iProp Σ :=
    ∃ n, own γc (● n) ∗ points_to γ l (Value n).

  Lemma withdraw_spec_suc (γc: gname) n m lval (Φ: bool -> iProp Σ):
    m <= n -> points_to γ lval (Value n) 
    -∗ (points_to γ lval (Value (n - m)) -∗ Φ true) 
    -∗ wp (state_interp γ) ⊤ (withdraw m lval) Φ.
  Proof.
    iIntros (Hle) "Hpt Hpost". 
    iApply wp_bind. iApply (wp_get with "Hpt"). iIntros "Hpt".
    iApply wp_bind. iApply wp_return.
    apply Nat.leb_le in Hle. rewrite Hle.
    iApply wp_bind. iApply (wp_put with "Hpt"). 
    iIntros "Hpt". iApply wp_return. by iApply "Hpost".
  Qed.

  Lemma auth_frag_lte (γc: gname) (n m: nat): own γc (● n) -∗ own γc (◯ m) -∗ ⌜m <= n⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag")
    as %[?%nat_included _]%auth_both_valid_discrete; done.
  Qed.

  Lemma auth_frag_update (n m: nat): m <= n -> ● n ⋅ ◯ m ~~> ● (n - m) ⋅ ◯ 0.
  Proof.
    intros Hlte.
    apply auth_update.
    apply nat_local_update.
    by rewrite (Nat.sub_add _ _ Hlte).
  Qed.

  Lemma auth_frag_own_update (γc: gname) (n m: nat): own γc (● n) -∗ own γc (◯ m) ==∗ own γc (● (n - m)).
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (auth_frag_lte with "Hauth Hfrag") as %Hlte.
    iMod (own_update_2 with "Hauth Hfrag").
    { by apply auth_frag_update. }
    done.
  Qed.

  Lemma withdraw_locked_spec (γc: gname) m lbal llock (Φ: () -> iProp Σ):
  (@is_lock _ _ _ γ llock (lock_payload γc lbal))
  -∗ own γc (◯ m)
  -∗ Φ () 
  -∗ wp (state_interp γ) ⊤ (withdraw_locked m llock lbal) Φ.
  Proof.
    iIntros "#Hlock Hfrag Hpost". unfold withdraw_locked.
    iApply wp_bind. iApply (aqcuire_spec with "Hlock").
    iIntros "(%n & Hauth & Hpt)". iDestruct (auth_frag_lte with "Hauth Hfrag") as %Hlt.
    iApply wp_bind. iApply (withdraw_spec_suc γc _ _ _ _ Hlt with "Hpt"). iIntros "Hpt".
    iApply bupd_wp. iMod (auth_frag_own_update with "Hauth Hfrag") as "Hauth". iModIntro.
    iApply (release_spec with "Hlock [Hpt Hauth]"); try done.
    unfold lock_payload. iExists (n - m). iFrame.
  Qed.

  Lemma bank_spec : ⊢ wp (state_interp γ) ⊤ (bank_prog) (λ x, ⌜x = tt⌝). 
  Proof.
    iApply bupd_wp.
    iMod (own_alloc (● 100 ⋅ ◯ (38 + (5 + (20 + (10 + (2 + 25))))))) as (γc) "(Hauth & Hrest & H5 & H20 & H10 & H2 & H25)".
    { apply auth_both_valid. simpl. done. } iModIntro.
    iApply wp_bind.
    iApply wp_alloc. iIntros (lval) "Hval".
    iApply wp_bind.
    iApply (new_lock_spec _ (lock_payload γc lval ) with "[Hval Hauth]"). 
    { iExists 100. iFrame. }
    iIntros (llock) "#Hinv".
    iApply wp_bind. iApply (wp_fork with "[H5 H25]").
    - 
     iNext. iApply wp_bind.
      iApply (withdraw_locked_spec with "Hinv H5").
      iApply (withdraw_locked_spec with "Hinv H25"). done.
    - iApply wp_bind. iApply (withdraw_locked_spec with "Hinv H20").
      iApply wp_bind. iApply (withdraw_locked_spec with "Hinv H2").
      iApply wp_bind. iApply (withdraw_locked_spec with "Hinv H10"). 
      by iApply wp_return.
  Qed.
End bank_verification.