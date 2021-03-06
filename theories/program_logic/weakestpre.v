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

  Lemma wp_modifyS' {A} Φ (f: ST -> A * ST): 
    (∀σ, SI σ ==∗ let '(x, σ') := f σ in SI σ' ∗ Φ x) -∗ state_wp SI (modifyS' f) Φ.
  Proof.
    iIntros "Hpost" (σ) "Hsi".
    iMod ("Hpost" with "Hsi") as "Hpost".
    destruct (f σ) as [x s'] eqn: E.
    iExists x, s'.
    iModIntro.
    iSplit.
    - unfold modifyS'. simpl. rewrite E. done.
    - iFrame.
  Qed.

  Lemma wp_modifyS Φ f: (∀σ, SI σ ==∗ SI (f σ) ∗ Φ tt) -∗ state_wp SI (modifyS f) Φ.
  Proof.
    iIntros "Hpost". 
    iApply wp_modifyS'. done.
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

Definition heapR (A: ofe): cmra := authR (gmapUR nat (exclR A)).



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
    pose (proj1 (@auth_both_valid_discrete cmr _ (lift_excl σ) ({[n := Excl v]}))).
    destruct (a H) as [H1 H2].
    iPureIntro.
    pose (proj1 (singleton_included_exclusive_l (lift_excl σ) n (Excl v) _ H2) H1).
    apply rewrite_lookups.
    assumption.
  Qed.
  
  Lemma lift_excl_some σ n v: σ !! n = Some v -> lift_excl σ !! n = Some (Excl v).
  Proof.
    intro H.
    unfold lift_excl.
    rewrite lookup_fmap.
    rewrite H.
    reflexivity.
  Qed.

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

  Lemma wp_get n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ state_wp (state_interp γ) (get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_ret. by iApply "Hpost".
  Qed.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ state_wp (state_interp γ) (put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_modifyS.
    iIntros (σ) "Hsi". 
    iMod (points_to_update with "Hsi Hpt") as "($ & Hup)". 
    by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ state_wp (state_interp γ) (alloc v) Ψ.
  Proof.
    iIntros "Hpost". iApply wp_modifyS'.
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "(Hsi' & Hpt)".
    iModIntro.
    iFrame.
    iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ state_wp (state_interp γ) (free l) Ψ.
  Proof.
    iIntros "Hpt Hpost". iApply wp_modifyS.
    iIntros (σ) "Hsi".
    iMod (si_free with "Hsi Hpt") as "$".
    done.
  Qed.


End state_wp_gp.

Set Printing Coercions.
(*
  alloc+ free.
  adequacy.
  Example programs.
  abstract state.

 *)
 Section state_ad.
  Context `{! inG Σ (heapR natO)}.

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
End state_ad.


