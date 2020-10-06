From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import state.
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

  Print state_wp.
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

  (* Isn't this just another tautology? *)
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

  About own.
 (* Now come the rule that needs the points to connective in their weakest pre definition.
     We therefore first define this in terms of the Authorative camera.
   *)

  Definition points_to (γ: gname) (n: nat) (v: nat): iProp Σ :=
    own γ ( ◯ {[ n := Excl v ]}).

  Definition lift_excl (σ: gmap nat nat): (gmap nat (excl nat)) := (Excl <$> σ).
  Definition state_interp (γ: gname) (σ: gmap nat nat) := own γ (● (lift_excl σ)).

  About auth_both_valid.
  About singleton_included_exclusive.
  Locate "=".
  About Excl'.
  About Excl.
  Search equiv f_equal.
  Search LeibnizEquiv.
  Search fmap f_equal.
  About leibniz_equiv_iff.
  About f_equiv.

  Context (γ: gname).

  Lemma rewrite_lookups σ n v : lift_excl σ !! n ≡ Excl' v -> (σ !! n) = Some v.
  Proof.
    intros H.
    rewrite (lookup_fmap Excl σ n) in H.
    destruct (leibniz_equiv_iff (Excl <$> σ !! n) (Excl' v)).
    apply H0 in H.
    unfold fmap in H.
    unfold option_fmap in H.
    unfold option_map in H.
    destruct (σ !! n) eqn: E.
    - injection H. auto.
    - discriminate H.
  Qed.

  Lemma si_points_to_agree σ n v: state_interp γ σ -∗ points_to γ n v -∗ ⌜σ !! n = Some v⌝.
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp.
    unfold points_to.
    iDestruct (own_valid_2 with "Hsi Hpt") as "%".
    pose (cmr := (gmapUR nat (exclR natO))).
    pose (proj1 (@auth_both_valid cmr _ (lift_excl σ) ({[n := Excl v]}))).
    destruct (a H) as [H1 H2].
    iPureIntro.
    pose (proj1 (singleton_included_exclusive_l (lift_excl σ) n (Excl v) _ H2) H1).
    apply rewrite_lookups.
    assumption.
  Qed.

  (*useful helper lemmas for combining owns *)
  About own_valid.
  About own_op.
  About own_valid_2.
  About own_update_2.
  (*useful helper lemmas for deriving equality from validity*)
  Search auth valid.
  Search excl.
  About excl_valid.
  Print excl_valid.
  About auth_both_valid.
  Search included gmap.
  About singleton_included_exclusive.
  About bi_iff.
  About bi_and.
  Locate "∧".
  Search bi_iff.
  Search bi_and.
  Search fmap lookup.
  About map_fmap_equiv_ext.
  About lookup_fmap.
  About map_fmap_ext.
  About Excl'.

  Locate "~~>".
  Search cmra_update.
  (* update both parts of a composition with a frame perserving update *)
  About cmra_update_op.
  About prod_local_update.
  About singleton_local_update.
  About fmap_insert.
  About replace_local_update.
  About IdFree.

  About lookup_fmap.
  Lemma lift_excl_some σ n v: σ !! n = Some v -> lift_excl σ !! n = Some (Excl v).
  Proof.
    intro H.
    unfold lift_excl.
    rewrite lookup_fmap.
    rewrite H.
    reflexivity.
  Qed.

  Search fmap insert.
  About exclusive_local_update.
  About excl_valid.
  Locate "✓".

  Lemma points_to_update σ n v w:
    state_interp γ σ -∗ points_to γ n v ==∗ state_interp γ (<[n := w ]> σ) ∗ points_to γ n w.
  Proof.
    iIntros "Hsi Hpt".
    iDestruct (si_points_to_agree with "Hsi Hpt") as "%".
    unfold state_interp.
    unfold points_to.
    iApply own_op.
    iApply (own_update_2 with "[Hsi]").
    2: iAssumption.
    2: iAssumption.
    -
      apply auth_update.
      unfold lift_excl.
      rewrite fmap_insert.
      eapply singleton_local_update.
      * apply lift_excl_some. apply H.
      * apply exclusive_local_update.
        reflexivity.
    Qed.

  Locate "∉".
  Locate "∅". 
  Locate "◯".
  Search dom.
  Search empty.

  Lemma si_alloc σ v:
    let l := fresh (dom (gset nat) σ)
    in  state_interp γ σ ==∗ state_interp γ (<[l := v ]> σ) ∗ points_to γ l v.
  Proof.
    iIntros "Hsi".
    unfold state_interp. unfold points_to.
    iApply own_op.
    iApply (own_update).
    -  apply auth_update_alloc.
       unfold lift_excl. rewrite fmap_insert. 
       apply alloc_singleton_local_update.
       + rewrite lookup_fmap. rewrite fresh_none. done.
       + done. 
    - unfold lift_excl. done.
  Qed.


  SearchAbout fmap_delete.
  About Exclusive.
  Lemma si_free σ v l:
   state_interp γ σ -∗ points_to γ l v ==∗ state_interp γ (delete l σ).
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp. unfold points_to.
    iApply (own_update).
    - apply auth_update_dealloc.
      unfold lift_excl. rewrite fmap_delete.
      (* why does this fail type class resolution? *)
      (* apply delete_singleton_local_update with (x := Excl v). *)
      apply (delete_singleton_local_update _ l (Excl v)).
    - iApply own_op.
      iFrame.
  Qed.

  Lemma wp_get' n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ state_wp (state_interp γ) (get' n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_ret. by iApply "Hpost".
  Qed.


  Lemma wp_get n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ state_wp (state_interp γ) (get n) Ψ.
  Proof.
    iIntros "Hpt ϕ" (σ) "HSi".
    iModIntro. iExists v, σ .
    iSplit.
    - unfold runState. unfold get. unfold fmap.
      iDestruct (si_points_to_agree with "HSi Hpt") as "%".
      rewrite H. done.
    - simpl.
      iDestruct ("ϕ" with "Hpt") as "$".
      iFrame.
  Qed.

  Lemma wp_put' n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ state_wp (state_interp γ) (put' n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    unfold put'.
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "$". 
    iModIntro.
    iApply wp_putS.
    iIntros (σ') "Hsi".
    iMod ((points_to_update  _ _ v v') with "Hsi Hpt") as "Hup". 

  Qed.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ state_wp (state_interp γ) (put n v') Ψ.
  Proof.
    iIntros "Hpt ϕ" (σ) "HSi".
    iMod ((points_to_update  _ _ v v') with "HSi Hpt") as "Hup".
    iModIntro. iExists tt, (<[n:=v']> σ).
    iSplit.
    - done.
    - iDestruct "Hup" as "($ & Hup')".
      iApply ("ϕ" with "Hup'").
  Qed.



  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ state_wp (state_interp γ) (alloc v) Ψ.
  Proof.
    iIntros "Hpost" (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "(Hsi' & Hpt)".
    simpl.
    pose (l:= fresh (dom (gset nat) σ)).
    iModIntro. iExists l, (<[l := v]> σ).
    iSplit.
    - done.
    - iDestruct ("Hpost" with "Hpt") as "$".
      done.
  Qed.

  About si_free.
  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ state_wp (state_interp γ) (free l) Ψ.
    iIntros "Hpt Hpost" (σ) "Hsi".
    iMod (si_free with "Hsi Hpt") as "Hsi'".
    iModIntro. iExists tt, (delete l σ).
    iSplit.
    - done.
    - iFrame. 
  Qed.

End state_wp_gp.

Set Printing Coercions.
About uPred.pure_soundness.
About bupd_plain.
About own_alloc.
About bi_emp_valid.
Locate "⊢".
About Excl.
(*
  alloc+ free.
  adequacy.
  Example programs.
  abstract state.

 *)
 Section state_ad.
  Context `{! inG Σ (heapR natO)}.

  About cmra_valid.
  About excl_valid.
  Print gmap_valid.

  Lemma adequacy {A} (Q: A -> Prop) (prog : state (gmap nat nat) A) (st: gmap nat nat):
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

  Definition prog_swap (l k: nat): state (gmap nat nat) unit := 
    x ← get l ;
    y ← get k ;
    put l y ;; put k x.

  (*for linked lists 
    https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/countable.v#L21
  *)
  Lemma swap_verif l k x y :
   ∀γ Φ, points_to γ l x ∗ points_to γ k y -∗ 
       (points_to γ l y ∗ points_to γ k x -∗ Φ tt) -∗
       state_wp (state_interp γ) (prog_swap l k) Φ. 
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
End state_ad.


