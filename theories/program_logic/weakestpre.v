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


  (*Derived rules *)
  Lemma wp_mono {A} Φ Ψ (e: state ST A): (∀ v, Φ v ⊢ Ψ v) → state_wp SI e Φ ⊢ state_wp SI e Ψ.
  Proof.
     iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
     iIntros (v) "?". by iApply HΦ.
  Qed.

  Lemma wp_value_fupd' {A} Φ (v: A) : (|==> Φ v) ⊢ state_wp SI (mret v) Φ.
  Proof. by rewrite -wp_bupd -wp_ret. Qed.

End state_wp.

Definition heapR (A: ofeT): cmraT := authR (gmapUR nat (exclR A)).

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


  (*
    I'm trying to prove that if I own an entire heap and I own a fragment of that heap then
    Looking up the fragment in the heap will give me the value that corresponds to the fragment.

    Robbert stated that the equality can be derived from the idea of validity.

    The way to get from validity to equality is through singleton_included_exclusive.
    Lets apply that first. It's hard to apply that since it is a pure statement, not one in a seperation logic context.
    Instead let's try to build it's requirements, these are:
    An x over which we have exclusive ownership, here: Excl v.
    A map which is valid, we want: valid σ.
    Then we have to show inclusion of the singleton in σ.

    Step one: getting Valid of σ. Would be using own_valid on Hsi.
    Step two: show inclusion of our singleton map in σ.
              The lemma auth_both_valid gives us inclusion
   *)
  About auth_both_valid.
  About singleton_included_exclusive.
  Locate "=".
  About Excl'.
  About Excl.
  SearchAbout equiv f_equal.
  SearchAbout LeibnizEquiv.
  SearchAbout fmap f_equal.
  About leibniz_equiv_iff.
  About f_equiv.

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

  Lemma si_points_to_agree γ σ n v: state_interp γ σ -∗ points_to γ n v -∗ ⌜σ !! n = Some v⌝.
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp.
    unfold points_to.
    iDestruct (own_valid_2 with "Hsi Hpt") as "%".
    pose (cmr := (gmapUR nat (exclR natO))).
    pose (proj1 (@auth_both_valid cmr _ (lift_excl σ) ({[n := Excl v]}))).
    destruct (a H) as [H1 H2].
    iPureIntro.
    pose (proj1 (singleton_included_exclusive (lift_excl σ) n (Excl v) _ H2) H1).
    apply rewrite_lookups.
    assumption.
  Qed.

   (* Todo state additional lemmas about the heap, alloc / store*)
  (*usefull helper lemmas for combining owns *)
  About own_valid.
  About own_op.
  About own_valid_2.
  About own_update_2.
  (*usefull helper lemmas for deriving equality from validity*)
  SearchAbout auth valid.
  SearchAbout excl.
  About excl_valid.
  Print excl_valid.
  About auth_both_valid.
  SearchAbout included gmap.
  About singleton_included_exclusive.
  About bi_iff.
  About bi_and.
  Locate "∧".
  SearchAbout bi_iff.
  SearchAbout bi_and.
  SearchAbout fmap lookup.
  About map_fmap_equiv_ext.
  About lookup_fmap.
  About map_fmap_ext.
  About Excl'.

  Locate "~~>".
  SearchAbout cmra_update.
  (* update both parts of a composition with a frame perserving update *)
  About cmra_update_op.
  About prod_local_update.
  About singleton_local_update.


  About lookup_fmap.
  Lemma lift_excl_some σ n v: σ !! n = Some v -> lift_excl σ !! n = Some (Excl v).
  Proof.
    intro H.
    unfold lift_excl.
    rewrite lookup_fmap.
    rewrite H.
    reflexivity.
  Qed.


  Lemma points_to_update γ σ n v w:
    state_interp γ σ -∗ points_to γ n v ==∗ state_interp γ (<[n := w ]> σ) ∗ points_to γ n w.
  Proof.
    iIntros "Hsi Hpt".
    iDestruct (si_points_to_agree with "Hsi Hpt") as "%".
    unfold state_interp.
    unfold points_to.
    iApply own_op.
    iApply (own_update_2 with "[Hsi]").
    -
      (*To prove: ?Goal ⋅ ?Goal0 ~~> ● lift_excl (<[n:=w]> σ) ⋅ ◯ {[n := Excl w]} *)
      apply auth_update. (*Or perhaps cmra_update_op *)
      (*To prove: (?a, ?b) ~l~> (lift_excl (<[n:=w]> σ), {[n := Excl w]}) *)
      pose (singleton_local_update (lift_excl σ) n _ _ _ _ (lift_excl_some _ _ _ H)).
      apply singleton_local_update.
      apply: prod_update. (*This doesn't apply, how do I split this into two seperate updates? *) 
      + (*use insert_update *)
      + (*use singleton update  *).
    - iAssumption.
    - iAssumption.

  Admitted.



  Context (γ: gname).


  Lemma wp_load n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ state_wp (state_interp γ) (get _ n) Ψ.

                       End. 
