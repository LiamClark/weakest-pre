From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
Set Default Proof Using "Type".

Definition heapR (A: Type): cmra := authR (gmapUR nat (exclR (leibnizO A))).

Section heap.
  Context `{! inG Σ (heapR A)}.
  Context (γ: gname).
 (* Now come the rule that needs the points to connective in their weakest pre definition.
     We therefore first define this in terms of the Authorative camera.
   *)

  Definition points_to (n: nat) (v: A): iProp Σ :=
    own γ ( ◯ {[ n := Excl v ]}).

  Definition lift_excl (σ: gmap nat A): gmap nat (excl (leibnizO A)) := Excl <$> σ.
  Definition state_interp (σ: gmap nat A) := own γ (● (lift_excl σ)).
  

  Lemma fresh_none (σ: gmap nat A): 
    let l := fresh (dom (gset nat) σ)
    in σ !! l = None.
  Proof.
    apply (not_elem_of_dom (D := gset nat)).
    apply is_fresh.
  Qed.

  Lemma rewrite_lookups σ n v : lift_excl σ !! n = Excl' v -> (σ !! n) = Some v.
  Proof.
    intros H.
    rewrite lookup_fmap in H.
    destruct (σ !! n) eqn: E; naive_solver.
  Qed.

  Lemma si_get σ n v: state_interp σ -∗ points_to n v -∗ ⌜σ !! n = Some v⌝.
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp.
    unfold points_to.
    iDestruct (own_valid_2 with "Hsi Hpt") as "%H".
    apply auth_both_valid_discrete in H as [H1 H2].
    iPureIntro.
    pose proof (proj1 (singleton_included_exclusive_l (lift_excl σ) n (Excl v) _ H2) H1).
    apply leibniz_equiv_iff in H.
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

  Lemma si_put σ n v w:
    state_interp σ -∗ points_to n v ==∗ state_interp (<[n := w ]> σ) ∗ points_to n w.
  Proof.
    iIntros "Hsi Hpt".
    iDestruct (si_get with "Hsi Hpt") as "%H".
    unfold state_interp.
    unfold points_to.
    iApply own_op.
    iApply (own_update_2 with "Hsi Hpt").
    apply auth_update.
    unfold lift_excl.
    rewrite fmap_insert.
    apply: singleton_local_update.
    * apply lift_excl_some. apply H.
    * apply exclusive_local_update.
      reflexivity.
    Qed.

  Lemma si_alloc σ v:
    let l := fresh (dom (gset nat) σ)
    in  state_interp σ ==∗ state_interp (<[l := v ]> σ) ∗ points_to l v.
  Proof.
    iIntros "Hsi".
    unfold state_interp. unfold points_to.
    iApply own_op.
    iApply (own_update).
    -  apply auth_update_alloc.
       unfold lift_excl. rewrite fmap_insert. 
       apply: alloc_singleton_local_update.
       + rewrite lookup_fmap. rewrite fresh_none. done.
       + done. 
    - unfold lift_excl. done.
  Qed.

  Lemma si_free σ v l:
   state_interp σ -∗ points_to l v ==∗ state_interp (delete l σ).
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp. unfold points_to.
    iApply (own_update).
    - apply auth_update_dealloc.
      unfold lift_excl. rewrite fmap_delete.
      (* why does this fail type class resolution? *)
      (* apply delete_singleton_local_update with (x := Excl v). *)
      apply (delete_singleton_local_update _ l (Excl (v: leibnizO A))).
    - iApply own_op.
      iFrame.
  Qed.
End heap.