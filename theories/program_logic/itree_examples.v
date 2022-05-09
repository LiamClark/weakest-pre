From stdpp Require Import base. 
From iris.algebra Require Import lib.frac_auth numbers auth.
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

Definition try_acquire (l: loc): expr cell bool :=
  snd <$> cmpXchg l UnLocked Locked.

Definition aqcuire_body (acq: bool): expr cell (() + ()) :=
  if acq then mret $ inr $ () else mret $ inl $ ().

Definition acquire (l: loc): expr cell () :=
  itree.iter 
    (λ _, try_acquire l ≫= aqcuire_body)  
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
    is_lock lk R -∗ (∀ b: bool, (if b then R else True) -∗ Φ b) -∗ wp (state_interp γ) ⊤ (try_acquire lk) Φ.
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
    is_lock lk R -∗ R -∗ (True -∗ Φ tt) -∗ wp (state_interp γ) ⊤ (release lk) Φ.
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

  Definition asValue (c: cell): expr cell nat :=
    match c with
    | Locked => itree.fail
    | UnLocked => itree.fail 
    | Value n => mret n
    end.

  Definition getValue (c: cell) : expr cell (option nat) :=
    match c with
    | Locked => mret $ None 
    | UnLocked => mret $ None 
    | Value n => mret $ Some $  n
    end.


  Definition withdraw (amount: nat) (balanceLoc: loc): expr cell bool :=
    balanceCell ← get balanceLoc;
    balance ← asValue balanceCell ; 
    if (amount <=? balance) 
    then put balanceLoc (Value (balance - amount)) ;; mret true 
    else mret false.

  Definition withdrawLocked (amount: nat) (lockLoc: loc) (balanceLoc: loc): expr cell () :=
    let ret: bool -> expr cell () :=  λ (b: bool), if b then release lockLoc else itree.fail in
    acquire lockLoc ;; 
    ( b ) ← withdraw amount balanceLoc ;
    ret b.

  Definition bank_prog: expr cell (option nat) :=
    balanceLoc  ← alloc (Value 100) ; 
    lockLoc     ← new_lock ; 
    fork (withdrawLocked 5  lockLoc balanceLoc ;; withdrawLocked 25 lockLoc balanceLoc) ;;
    withdrawLocked 20 lockLoc balanceLoc ;;
    withdrawLocked 2  lockLoc balanceLoc ;;  
    withdrawLocked 10 lockLoc balanceLoc ;; 
    c ← get balanceLoc ;
    getValue c.
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
  (* Context `{! inG Σ (authR natUR)}. *)
  Context {γ: gname}.
(* 
  Locate "<=?".
  Search le.
  Search (?n <= ?m \/ _).
  Check Nat.le_gt_cases.
  Search (?n <= ?m -> ¬ _).
  (*
   I need to arrive at <=? = false
  I did that using: Nat.leb: n <=? m = false <-> ¬ n <= m *)
  Check Nat.leb_le.
  (* I however have m < n from le_gt_cases.
  Thus I need m < n -> ¬ (n <= m)  *) 
  Search (?m < ?n -> ¬ (?n <= ?m)).
  Check lt_not_le.
  Check le_not_lt.
  Search le Nat.leb. *)

  Definition ccounter (γ: gname) (n: nat) :iProp Σ :=
      own γ (◯ n).

  Lemma ccounter_split (γc: gname) n1 n2 :
    ccounter γc (n1 + n2) ⊣⊢ ccounter γc n1 ∗ ccounter γc n2.
  Proof. by rewrite /ccounter auth_frag_op -own_op. Qed.

  Definition ccounter_inv (γc: gname) (l : loc) : iProp Σ :=
    ∃ n, own γc (● n) ∗ points_to γ l (Value n).

  Lemma withdraw_spec_suc (γc: gname) n n' lval (Φ: bool -> iProp Σ)
  : n' <= n ->
  points_to γ lval (Value n)
  -∗ (points_to γ lval (Value (n - n')) -∗ Φ true)
  -∗ wp (state_interp γ) ⊤ (withdraw n' lval) Φ.
  Proof.
    iIntros (Hle) "Hpt Hpost". 
    iApply wp_bind. iApply (wp_get with "Hpt"). iIntros "Hpt".
    iApply wp_bind. iApply wp_return.
    apply Nat.leb_le in Hle. rewrite Hle.
    iApply wp_bind. iApply (wp_put with "Hpt"). 
    iIntros "Hpt". iApply wp_return. by iApply "Hpost".
  Qed.

  (* ● γ 100
  ◯ γ 60
  ◯ γ 40 *)

  (* ● γ n ∗ ◯ γ m -∗ m <= n.  done
  ● γ n ∗ ◯ γ m -∗ |==>  ● γ (n - m). done.
  ◯ γ (n + m) ⊣⊢ (◯ γ n ∗ ◯ γ m) doen in ccounter op.
  True -∗ |==> ∃ γ, ● γ n ∗ ◯ γ n *)

  Locate auth_both_valid_discrete.
  Search (?n - ?m + ?m = ?n) .
  Lemma auth_frag_lte (γc: gname) (n m: nat): own γc (● n) -∗ own γc (◯ m) -∗ ⌜m <= n⌝.
  Proof.
    iIntros "Hauth Hfrag".
    (* What is this construct? *)
    iDestruct (own_valid_2 with "Hauth Hfrag")
    as %[?%nat_included]%auth_both_valid_discrete.
    by iPureIntro.
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

  Lemma withdraw_locked_spec (γc: gname) m lval llock (Φ: () -> iProp Σ)
  : (@is_lock _ _ _ γ llock (ccounter_inv γc lval))
  -∗ own γc (◯ m)
  -∗ (True -∗ Φ ())
  -∗ wp (state_interp γ) ⊤ (withdrawLocked m llock lval) Φ.
  Proof.
    iIntros "#Hlock Hfrag Hpost". unfold withdrawLocked.
    iApply wp_bind. iApply (aqcuire_spec with "Hlock").
    iIntros "(%n & Hauth & Hpt)". iDestruct (auth_frag_lte with "Hauth Hfrag") as %Hlt.
    iApply wp_bind. iApply (withdraw_spec_suc γc _ _ _ _ Hlt with "Hpt"). iIntros "Hpt".
    iApply bupd_wp. iMod (auth_frag_own_update with "Hauth Hfrag") as "Hauth". iModIntro.
    iApply (release_spec with "Hlock [Hpt Hauth]"); try done.
     unfold ccounter_inv. iExists (n - m). iFrame.
  Qed.

  Lemma split_100: 100 = 70 + 30. Proof. lia. Qed.
  Lemma split_70: 70 = 38 + 32.   Proof. lia. Qed.
  Lemma split_30: 30 = 25 + 5.    Proof. lia. Qed.
  Lemma split_32: 32 = 12 + 20.   Proof. lia. Qed.
  Lemma split_12: 12 = 10 + 2.    Proof. lia. Qed.


  (* The last thing remaining here is to allocate the ghost state, see the last undone lemma above *)
  Lemma bank_spec : ⊢ wp (state_interp γ) ⊤ (bank_prog) 
     (λ balanceOpt,
      match balanceOpt with
      | Some balance => ⌜balance = 38⌝
      | None => False
      end)%I.
  Proof.
    iApply bupd_wp.
    iMod (own_alloc (● 100 ⋅ ◯ 100)) as (γc) "Hghost".
    { apply auth_both_valid. done. } iModIntro.
    iDestruct (own_op with "Hghost") as "(Hauth & Hfrag)".
    iEval (rewrite split_100) in "Hfrag". iDestruct (ccounter_split with "Hfrag") as "(Hmain & Hfork)".
    iEval (rewrite split_70) in "Hmain".  iDestruct (ccounter_split with "Hmain") as "(Hrest & Hmain)".
    iApply wp_bind.
    iApply wp_alloc. iIntros (lval) "Hval".
    iApply wp_bind.
    iApply (new_lock_spec _ (ccounter_inv γc lval ) with "[Hval Hauth]"). 
    { iExists 100. iFrame. }
    iIntros (llock) "#Hinv".
    iApply wp_bind. iApply (wp_fork with "[Hfork]").
    - iNext. iApply wp_bind.
      iEval (rewrite split_30) in "Hfork". iDestruct (ccounter_split with "Hfork") as "(Hfork & Hpay)".
      iEval (unfold ccounter) in "Hpay".
      iApply (withdraw_locked_spec with "Hinv Hpay").
      iIntros "_".  iApply (withdraw_locked_spec with "Hinv Hfork"). done.
    - iEval (rewrite split_32) in "Hmain". iDestruct (ccounter_split with "Hmain") as "(Hmain & Hpay)".
      iApply wp_bind. iApply (withdraw_locked_spec with "Hinv Hpay"). iIntros "_".
      iEval (rewrite split_12) in "Hmain". iDestruct (ccounter_split with "Hmain") as "(Hmain & Hpay)".
      iApply wp_bind. iApply (withdraw_locked_spec with "Hinv Hpay"). iIntros "_".
      iApply wp_bind. iApply (withdraw_locked_spec with "Hinv Hmain"). iIntros "_".
      (* Can I use Hrest here??  Perhaps something as the auth in Hinv needs to be atleast 38 because that's the fragment I still own *)
      (* Sounds like a Robbert question for tomorrow! *)
      admit.
  Admitted.
End bank_verification.