From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import modal itree evaluation.
Set Default Proof Using "Type".

Section itreewp.
  Context `{!invG Σ}. 

(* Curry the value R so it can be changed by the dependent pattern match on c *)
Definition command_predicate {V R} (c: envE V R) (σ σ': gmap loc V): R -> Prop :=
  match c with
  | GetE l    => λ v, σ !! l = Some v /\ σ' = σ 
  | PutE l v' => λ _, is_Some (σ !! l) /\ σ' = <[l := v']> σ
  | AllocE v' => λ l, l = fresh_loc σ /\ σ' = <[l := v']> σ
  | FreeE l   => λ _, is_Some (σ !! l) /\ σ' = delete l σ
  end.


(*
 Now I want to change these update modalities to fancy update modalities
 How do I want to do that? let's peak at the Iris wp definition.

 I want to import
 From iris.base_logic.lib Require Export fancy_updates oh that's already imported.
 The definition of wp_pre requires an extra argument E for a mask.
 The wand however can have two masks and iris uses empty there a lot.
 
 1. Research the meanings of the two masks?
 2. Why is it a coPset?
 3. where is the notation defined.
*)

Locate "|={ _ }=> _".
Locate "|={ _ , _ }=> _".
Check fupd.
(* 
  A fupd with one mask simply keeps the same mask.
  A fupd with two masks goes from mask one to mask two.
*)
(* 
  now I can take the mask after the type variable udner a -d> arrow. works.
  The step for answer should never include any fupds so there we can use the same mask on both sides.
  However, what do I do for Think, Fork and Vis.
  So the coPset is a set of names, I can think tomorrow about how to use those.

  So the definition for Wp with fupds in Iris from the ground up drops and re-enables
  all masks to allow the reduction reasoning to not bother about the invariants.
  It also gives the forked-off thread the "full" mask because it won't reduce in
  this step anyways.
  Let me try proving a fancy update rule to see what I need.
*)

Search FUpd.
Definition wp_pre {V} (SI: gmap loc V -> iProp Σ)
     (go: discrete_funO (λ R, coPset -d> expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ)):
     discrete_funO (λ R, coPset -d> expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ).
refine(λ R E e Φ,
        match e with
        |Answer x  => |={E}=> Φ x 
        |Think e'  => |={E, ∅}=> ▷ |={∅, E}=> go R E e' Φ
        |Fork e' k => |={E, ∅}=> ▷ |={∅, E}=> (go R E k Φ ∗ go unit ⊤ e' (λ _, True))
        (* make wp less determinstic  *)
        (* |Vis c k   => ∀σ, SI σ ==∗ ▷ |==> (∃σ' v, ⌜command_predicate c σ σ' v⌝) ∗
            ∀ σ' v, ⌜command_predicate c σ σ' v⌝ -∗ SI σ' ∗ (go R (k v)) Φ *)
        |Vis c k   => ∀σ, SI σ ={E, ∅}=∗ ▷ |={∅, E}=> ∃σ' v, ⌜command_predicate c σ σ' v⌝ ∗ SI σ' ∗ (go R E (k v)) Φ
        end
)%I.
Defined.

Instance wp_pre_contractive {A SI}: Contractive (@wp_pre A SI).
Proof.
  rewrite /wp_pre => n wp wp' Hwp R E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp' {V} (SI: gmap nat V -> iProp Σ)
              : ∀R, coPset -> expr V R -> (R -> iProp Σ) ->iProp Σ :=
    fixpoint (wp_pre SI ).

Definition wp {V R} (SI: gmap nat V -> iProp Σ) (E: coPset) (e: expr V R) (Φ: R -> iProp Σ): iProp Σ := 
    wp' SI R E e Φ.

Definition wp_thread {V R} (SI: gmap nat V -> iProp Σ) (t: thread V R) 
: (R -> iProp Σ) -> iProp Σ.
refine (
  match t with
  | Main e => wp SI ⊤ e
  | Forked e => λ _,  wp SI ⊤ e (λ _, True)
  end
)%I.
Defined.

Lemma wp'_unfold {V R} (SI: gmap nat V -> iProp Σ) (E: coPset) (e: expr V R)  (Φ: R -> iProp Σ)
  : wp' SI R E e Φ  ≡  wp_pre SI (wp' SI) R E e Φ.
Proof.
  apply (fixpoint_unfold (wp_pre SI)).
Qed.

Lemma wp_unfold {V R} (SI: gmap nat V -> iProp Σ) (E: coPset) (e: expr V R)  (Φ: R -> iProp Σ)
  : wp SI E e Φ  ≡  wp_pre SI (wp' SI) R E e Φ.
Proof.
  apply (fixpoint_unfold (wp_pre SI)).
Qed.

Lemma wp_return {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
   (x: R) (Φ: R -> iProp Σ): Φ x -∗ wp SI E (mret x) Φ.
Proof.
  iIntros"H".
  by rewrite wp_unfold.
Qed.

Locate "|={ _ }[ _ ]▷=>".
Locate "|={ _ }[ _ ]▷=> _".
(* on newer versions of Iris *)
Check fupd_mask_intro. 

(* Check fupd_intro_mask. *)
Check fupd_mask_weaken.

(* ||={E1} P -∗ |={E1,E2}=> P *)
Lemma wp_think {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
   (e: expr V R) (Φ: R -> iProp Σ): ▷ wp SI E e Φ -∗ wp SI E (Think e) Φ.
Proof.
  iIntros "Hwp".
  iEval (rewrite wp_unfold). 
  unfold wp_pre. 
  iApply fupd_mask_intro; first set_solver.
  iIntros "H".
  iNext. iMod "H". iModIntro.
  done.
Qed.

Lemma wp_bind {V R B: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
  (f: R -> expr V B) (Φ: B -> iProp Σ) (e: expr V R): 
  wp SI E e (λ x, wp SI E (f x) Φ) -∗ wp SI E (e ≫= f) Φ.
Proof.
  unfold mbind, itree_bind.
  iIntros "H". iLöb as "IH" forall (e).
  iEval (rewrite wp_unfold).
  unfold wp_pre.
  destruct e; simpl.
  - do 2 (rewrite wp_unfold /=). unfold wp_pre.
    by destruct (f r); iMod "H".
  - iEval (rewrite wp_unfold /=) in "H".
    iMod "H". iIntros "!> !>". iApply "IH". done.
  - iEval (rewrite wp_unfold /=) in "H".
    iMod "H". iIntros "!> !>". iMod "H" as "(H & $)".
    iApply "IH". done.
  - iIntros (σ)  "HSi".
    iEval (rewrite wp_unfold /=) in "H".
    iMod ("H" $! σ with "HSi") as "H". iModIntro.
    iNext.
    iMod ("H") as (σ' v) "H". iModIntro.
    iExists σ', v.
    iDestruct "H" as "($ & $ & Hwp)". 
    iApply "IH". done.
Qed.


Print uPred_fupd.
Lemma wp_vup {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
  (e: expr V R) (Φ: R -> iProp Σ)
  : (|={E}=> wp SI E e (λ v, |={E}=> Φ v)) ⊢ wp SI E e Φ.
Proof.
  iLöb as "IH" forall (e).
  iIntros "Hwp".
  rewrite wp_unfold. rewrite wp_unfold.
  unfold wp_pre.
  destruct e; simpl.
  - repeat (iMod "Hwp"). done.
  - iMod "Hwp". 
    iMod "Hwp". iModIntro.
    iNext. 
    iMod "Hwp". iModIntro.
    iApply "IH". done.
  - repeat (iMod "Hwp"). 
    iModIntro. iNext.
    iMod "Hwp" as "(Hwp & $)".
    iApply "IH". done.
  - iIntros (σ) "HSi".
    iMod "Hwp".
    iDestruct ("Hwp" with "HSi" ) as "Hwp".
    iMod "Hwp". iModIntro. iNext.
    iMod "Hwp". iModIntro.
    iDestruct ("Hwp") as (σ' v) "(Hcmd & HSi & Hwp)".
    iExists σ', v. iFrame.
    iApply "IH". done.
Qed.

Inductive atomic {V R: Type}: expr V R -> Prop :=
|answer_atomic:  ∀ x, atomic (Answer x)
|think_atomic:  ∀ x, atomic (Think (Answer x))
|vis_atomic: ∀c, atomic (Vis c Answer).

Lemma wp_atomic {V R: Type} (SI: gmap nat V -> iProp Σ) (E1 E2: coPset)
  (e: expr V R) (Φ: R -> iProp Σ)
  (a: atomic e)
  (* Perhaps some premisse about e being atomic *)
  : (|={E1, E2}=> wp SI E2 e (λ v, |={E2, E1}=> Φ v)) ⊢ wp SI E1 e Φ.
Proof.
  iIntros "Hwp".
  rewrite wp_unfold. 
  rewrite wp_unfold. 
  destruct a; simpl.
  - iMod "Hwp". iMod "Hwp". iMod "Hwp".
    done.
  - iMod "Hwp". iMod "Hwp". iModIntro.
    iNext. iMod "Hwp". 
    rewrite wp'_unfold. rewrite wp'_unfold. simpl.
    iMod "Hwp".  iMod "Hwp". done.
  - iIntros (σ) "HSi".
    iMod "Hwp". iDestruct ("Hwp" with "HSi") as "Hwp".
    iMod "Hwp". iModIntro. iNext. iMod "Hwp".
    iDestruct ("Hwp") as (σ' v) "(Hcmd & HSi & Hwp)".
    iExists σ', v. iFrame.
    rewrite wp'_unfold. rewrite wp'_unfold. simpl.
    iMod "Hwp". iMod "Hwp".
    done.
Qed.


Check fupd_mask_mono.
Lemma wp_strong_mono_fupd {V R: Type} (SI: gmap nat V -> iProp Σ) (E1 E2: coPset)
  (e: expr V R) (Φ Ψ: R -> iProp Σ)
  : E1 ⊆ E2 -> wp SI E1 e Φ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ wp SI E2 e Ψ.
Proof.
  iIntros (Hmask).
  iLöb as "IH" forall (e).
  rewrite wp_unfold.
  rewrite wp_unfold.
  iIntros "Hwp H".
  destruct e; simpl.
  - 
   iDestruct ("H" with "Hwp") as "H". 
   iDestruct (fupd_mask_mono _ _ _ Hmask with "H") as "H'".
   repeat (iMod "H'").
   done. 
  - 
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done. 
    iMod "Hwp". iIntros "!> !>". 
    iMod "Hwp". iMod "Hclose".
    iModIntro.
    iApply ("IH" $! e with "Hwp H").
  - 
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done. 
    iMod "Hwp". iIntros "!> !>".
    iMod "Hwp" as "(Hwpe2 & $)".
    iMod "Hclose".
    iModIntro.
    iApply ("IH" $! e2 with "Hwpe2 H").
  - iIntros (σ) "HSi".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done. 
    iMod ("Hwp" with "HSi") as "Hwp".
    iIntros "!> !>".
    iMod "Hwp". iMod "Hclose". iModIntro.
    iDestruct "Hwp" as (σ' v) "(Hcom & HSi & Hwp)".
    iExists σ', v. iFrame. 
    iApply ("IH"  with "Hwp H"). 
Qed.

Lemma wp_strong_mono_bupd {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
  (e: expr V R) (Φ Ψ: R -> iProp Σ)
  : wp SI E e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp SI E e Ψ.
Proof.
  iIntros "Hwp Hf".
  iApply (wp_strong_mono_fupd with "Hwp"); first set_solver.
  - iIntros (v) "Hphi".
    iMod ("Hf" with "Hphi") as "Hf".
    iModIntro. done.
Qed.

Lemma wp_mono {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
   (e: expr V R) (Φ Ψ: R -> iProp Σ)
   :wp SI E e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ wp SI E e Ψ.
Proof.
  iIntros "Hwp H".
  iApply (wp_strong_mono_fupd with "Hwp"); first set_solver.
  - iIntros (v) "Hphi". 
    iModIntro.
    iApply ("H" with "Hphi").
Qed.

Lemma wp_fmap {V R B: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
  (f: R -> B) (Φ: B -> iProp Σ) (e: expr V R)
  : wp SI E e (Φ ∘ f ) -∗ wp SI E (f <$> e) Φ. 
Proof.
  iIntros "Hwp".
  iApply wp_bind.
  iApply (wp_mono with "Hwp").
  iIntros (x) "Hpost /=".
  iApply (wp_return with "Hpost").
Qed.

Lemma wp_iter  {V R B: Type} (SI: gmap nat V -> iProp Σ) (E: coPset) (Φ: B -> iProp Σ)
  (x: R)
  (f: R -> expr V (R + B)):
  wp SI E (f x) (case_ (λ x, ▷ wp SI E (iter f x) Φ) Φ) -∗
  wp SI E (iter f x) Φ.
Proof.
  iIntros "Hwp".
  rewrite iter_unfold.
  iApply wp_bind.
  iApply (wp_mono with "Hwp").
  iIntros ([a | b]) "H /=".
  - by iApply wp_think.
  - by iApply wp_return.
Qed.

Lemma fupd_wp  {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
 (e: expr V R) (Φ : R -> iProp Σ)
 : (|={E}=> wp SI E e Φ) ⊢ wp SI E e Φ.
Proof.
  iIntros "Hwp".
  rewrite wp_unfold.
  unfold wp_pre.
  destruct e.
  - iMod "Hwp" as "Hwp".
    by iMod "Hwp" as "Hwp".
  - iMod "Hwp" as "Hwp".
    by iMod "Hwp" as "Hwp".
  - iMod "Hwp" as "Hwp".
    by iMod "Hwp" as "Hwp".
  - by iMod "Hwp" as "Hwp".
Qed.

Lemma bupd_wp  {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
 (e: expr V R) (Φ : R -> iProp Σ)
 : (|==> wp SI E e Φ) ⊢ wp SI E e Φ.
Proof.
  iIntros "Hwp".
  rewrite wp_unfold.
  unfold wp_pre.
  destruct e.
  - iMod "Hwp" as "Hwp".
    by iMod "Hwp" as "Hwp".
  - iMod "Hwp" as "Hwp".
    by iMod "Hwp" as "Hwp".
  - iMod "Hwp" as "Hwp".
    by iMod "Hwp" as "Hwp".
  - by iMod "Hwp" as "Hwp".
Qed.


Lemma wp_fupd {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
 (e: expr V R) (Φ : R -> iProp Σ) 
 : wp SI E e (λ v, |={E}=> Φ v) ⊢ wp SI E e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono_fupd with "Hwp"); first set_solver.
  auto.
Qed.

Lemma wp_bupd {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
 (e: expr V R) (Φ : R -> iProp Σ) 
 : wp SI E e (λ v, |==> Φ v) ⊢ wp SI E e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono_bupd with "Hwp").
  auto.
Qed.


Lemma wp_think' {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset) 
  (e: expr V R) (Φ: R -> iProp Σ)
  : wp SI E (Think e) Φ ={E, ∅}=∗ ▷ |={∅, E}=> wp SI E e Φ .
Proof.
  iIntros "Hwp".
  rewrite wp_unfold. 
  unfold wp_pre.
  done.
Qed.

End itreewp.

(*Heap rules *)
Definition heapR (A: ofe): cmra := authR (gmapUR nat (exclR A)).

Lemma fresh_none (σ: gmap nat nat): 
 σ !! fresh_loc σ = None.
Proof.
  apply (not_elem_of_dom (D := gset nat)).
  unfold fresh_loc.
  apply is_fresh.
Qed.

Section heap_wp.
  Context `{! inG Σ (heapR natO)}.
  Context`{!invG Σ}. 
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
    destruct (σ !! n) eqn: E.
    - injection H. auto.
    - done.
  Qed.

  Lemma si_points_to_agree σ n v: state_interp γ σ -∗ points_to γ n v -∗ ⌜σ !! n = Some v⌝.
  Proof.
    iIntros "Hsi Hpt".
    unfold state_interp. unfold points_to.
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
    rewrite lookup_fmap. rewrite H.
    reflexivity.
  Qed.

  Lemma points_to_update σ n v w:
    state_interp γ σ -∗ points_to γ n v ==∗ state_interp γ (<[n := w ]> σ) ∗ points_to γ n w.
  Proof.
    iIntros "Hsi Hpt".
    iDestruct (si_points_to_agree with "Hsi Hpt") as "%".
    unfold state_interp. unfold points_to.
    iApply own_op.
    iApply (own_update_2 with "Hsi Hpt").
    apply auth_update. unfold lift_excl.
    rewrite fmap_insert.
    eapply singleton_local_update.
    * apply lift_excl_some. apply H.
    * apply exclusive_local_update.
      done.
    Qed.

  
  Lemma si_alloc σ v:
    let l := fresh_loc σ
    in  state_interp γ σ ==∗ state_interp γ (<[l := v ]> σ) ∗ points_to γ l v.
  Proof.
    iIntros "Hsi".
    iApply own_op.
    iApply (own_update with "Hsi").
    -  apply auth_update_alloc.
       unfold lift_excl. rewrite fmap_insert. 
       apply alloc_singleton_local_update.
       + rewrite lookup_fmap. rewrite fresh_none. done.
       + done. 
  Qed.

  Lemma si_free σ v l:
   state_interp γ σ -∗ points_to γ l v ==∗ state_interp γ (delete l σ).
  Proof.
    iIntros "Hsi Hpt".
    iApply (own_update).
    - apply auth_update_dealloc.
      unfold lift_excl. rewrite fmap_delete.
      apply (delete_singleton_local_update _ l (Excl v)).
    - iApply own_op.
      iFrame.
  Qed.

  Lemma wp_get n v E (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ wp (state_interp γ) E (itree.get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro. iExists σ, v. simpl.
    iDestruct (si_points_to_agree with "Hsi Hpt") as %H. 
    iSplit; try done.
    iFrame. 
    iApply wp_return. by iApply "Hpost".
  Qed.

  Lemma wp_put n v v' E (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ wp (state_interp γ) E (itree.put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi". 
    iDestruct (si_points_to_agree with "Hsi Hpt") as %Hsome.
    iMod (points_to_update with "Hsi Hpt") as "(Hsi & Hpt)". 
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iExists (<[n := v']> σ), tt. simpl.
    iSplit.
    - iPureIntro. split.
      + apply (mk_is_Some _ _ Hsome).
      + done.
    - iFrame. iApply wp_return.
      by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v E (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ wp (state_interp γ) E (itree.alloc v) Ψ.
  Proof.
    iIntros "Hpost". 
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "(Hsi & Hpt)".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iExists (<[fresh_loc σ := v]> σ), (fresh_loc σ). simpl.
    iSplit.
    - iPureIntro. split.
      + done.
      + done.
    - iFrame. iApply wp_return.
      iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l E (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ wp (state_interp γ) E (itree.free l) Ψ.
  Proof.
    iIntros "Hpt Hpost". 
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %Hsome.
    iMod (si_free with "Hsi Hpt") as "Hsi".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iExists (delete l σ), tt. simpl.
    iSplit.
    - iPureIntro. split.
      + apply (mk_is_Some _ _ Hsome).
      + done.
    - iFrame. 
      by iApply wp_return.
  Qed.
End heap_wp.



Section adequacy.
 Context `{! inG Σ (heapR natO)}.
 Context`{!invG Σ}. 
(*
  Ok what does this bugger say again?

  We are stepping in e.
  With two post conditions ψ is the post condition for the expression
  we are stepping right now.
  Φ is the post condition for the main thread, thus it is the one that matters
  for the rest of the threadpool. Since forked threads discard it, it only applies
  to the main thread.

  Since this is the deepest level it seems we should use the soundness lemmas at this point.
  Except no. We do not take in account that Φ and Ψ are pure. They are any iProp predicates.
  Hence none of the soundness lemma's apply here.
*)
Lemma step_expr_adequacy {R A} (γ: gname) (Φ: R -> iProp Σ) (Ψ: A -> iProp Σ) 
  (h: heap nat)
  (ts: list (thread nat R))
  (e: expr nat A)
  : wp (state_interp γ) ⊤ e Ψ 
  -∗ state_interp γ h
  ={⊤, ∅}=∗ 
   ▷ |={∅, ⊤}=> match runState (step_expr e) h ts with
     | Here (e', h', ts') => ∃ts'', ⌜ts' = ts ++ ts''⌝ 
                             ∗ wp (state_interp γ) ⊤ e' Ψ ∗ state_interp γ h'
                             ∗ [∗ list] t ∈ ts'', wp_thread (state_interp γ) t Φ
     | ProgErr => False
     | EvalErr => True
     end.
Proof.
  iIntros "Hwp Hsi".
  destruct e; simpl.
  - 
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". 
    iModIntro. iMod "Hclose". iModIntro.
    iExists []. rewrite right_id_L.
    iFrame. auto.
  - 
    iMod (wp_think' with "Hwp") as "Hwp".
    iIntros "!> !>". iMod "Hwp". iModIntro.
    iExists []. rewrite right_id_L.
    iFrame. auto.
  -
   rewrite wp_unfold. unfold wp_pre. simpl.
   iMod "Hwp". iIntros "!> !>".
   iMod "Hwp" as "(Hwpe2 & Hwpe1)".
   iModIntro. iFrame. simpl.
   iExists [_].
   iSplit; first done. by iFrame.
  -
    rewrite wp_unfold. unfold wp_pre.
    iMod ("Hwp" with "Hsi") as "Hwp".
    iIntros "!> !>".
    iMod "Hwp" as (σ' v) "(% & Hsi & Hwp)".
    destruct e; simpl.
    + destruct H as (Hlookup & Heq). rewrite Hlookup. subst h. simpl.
      iExists []. rewrite right_id_L.
      iFrame. auto.
    + destruct H as (Hlookup & Heq). subst σ'. destruct v.
      iExists []. rewrite right_id_L.
      iFrame. auto.
    + destruct H as (Hlookup & Heq). subst σ' v. 
      iExists []. rewrite right_id_L.
      iFrame. auto.
    + destruct H as (Hlookup & Heq). subst σ'. destruct v.
      iExists []. rewrite right_id_L.
      iFrame. auto.
Qed.

(* 
 We still have two post conditions, but they operate on the same type now.
 Ψ is for the thread we are stepping. Ah so this is the above lifted to a thread.
 Φ is still the post condition for the main thread.
*)
Lemma step_thread_adequacy {R} (γ: gname) (Φ Ψ: R -> iProp Σ) 
  (h: heap nat)
  (ts: list (thread nat R))
  (ct: thread nat R)
  : wp_thread (state_interp γ) ct Ψ 
  -∗ state_interp γ h 
  ={⊤, ∅}=∗ 
   ▷ |={∅, ⊤}=> 
    match runState (step_thread ct) h ts with
    | Here (ct', h', ts') => ∃ts'', ⌜ts' = ts ++ ts''⌝
                            ∗ wp_thread (state_interp γ) ct' Ψ ∗ state_interp γ h'
                            ∗ [∗ list] t ∈ ts'', wp_thread (state_interp γ) t Φ
    | ProgErr => False
    | EvalErr => True
    end.
Proof.
  iIntros "Hwp Hsi".
  simpl.
  destruct ct; simpl.
  - 
    iMod (step_expr_adequacy _ _ _ _ ts  with "Hwp Hsi") as "Hexpr".
    iIntros "!> !>". iMod "Hexpr". iModIntro.
    simpl. 
    by destruct (runState (step_expr e) h ts) as [[[e' σ'] ts'] | | ].
  -
    iMod (step_expr_adequacy _ _ _ _ ts with "Hwp Hsi") as "Hexpr".
    iIntros "!> !>". iMod "Hexpr". iModIntro.
    simpl. 
    by destruct (runState (step_expr e) h ts) as [[[e' σ'] ts'] | | ].
Qed.

Lemma mod_lookup_some {A} (l: list A) (i: nat):
 l ≠ [] -> is_Some (l !! (i mod (length l))).
Proof.
  intro Hnil.
  apply lookup_lt_is_Some_2. 
  apply Nat.mod_upper_bound.
  by destruct l.
Qed.

(*  OK third one up, now there is just one post condition left.
    Φ for the main thread. All the other threads namely have the trivial
    post condition
*)
Lemma scheduled_adequacy {R} (γ: gname) (Φ: R -> iProp Σ) 
  (h: heap nat)
  (s: scheduler nat R)
  (ts: list (thread nat R))
  : ts ≠ [] -> 
  state_interp γ h 
  -∗ ([∗ list] t ∈ ts, wp_thread (state_interp γ) t Φ) 
  ={⊤, ∅}=∗ 
   ▷ |={∅, ⊤}=> 
    match runState (single_step_thread s) h ts with
    | Here (s', h', ts') => ⌜length ts <= length ts'⌝
                            ∗ state_interp γ h'
                            ∗ [∗ list] t ∈ ts', wp_thread (state_interp γ) t Φ
    | ProgErr => False
    | EvalErr => True
    end.
Proof.
  iIntros (Hnil) "HSi Hbigop".
  unfold single_step_thread. simpl. destruct (schedule s (ts, h)) as [i s'].
  simpl. 
  destruct (mod_lookup_some ts i Hnil) as [t Hsome].
  iDestruct (big_sepL_insert_acc with "Hbigop") as "(Hwpct & Hrestore)"; first done.
  iMod (step_thread_adequacy _ _ _ _ ts with "Hwpct HSi" ) as "H".
  iIntros "!> !>".
  iMod "H". iModIntro.
  rewrite Hsome /=.  
  destruct (runState _ h ts) as [[[t' σ'] ts'] | | ]; try done; simpl.
  iDestruct "H" as (ts'' ->) "(Hwpt' & $ & Hbigop)".
  iSplit. 
  - iPureIntro. rewrite insert_length app_length. lia. 
  - rewrite insert_app_l; last first. 
    { apply Nat.mod_upper_bound. destruct ts; done. }
   iFrame.
   by iApply "Hrestore".
Qed.

Arguments mbind_state : simpl never.

Lemma run_get_threads {V A} σ (ts: list (thread V A))
  : runState get_threads σ ts = Here (ts, σ, ts).
Proof.
  done.
Qed.

Lemma non_nil_bigger_than {A} {ts ts' : list A}
  : ts ≠ [] -> length ts ≤ length ts' -> ts' ≠ [].
Proof.
  intros Hnil Hlength.
  destruct ts'.
  -  destruct ts.
    + done.
    + simpl in *.
    pose (Nat.nle_succ_0 _ Hlength). 
    contradiction.
  - done. 
Qed.

(*
  I need the conclusion to say something about how ts can be split up
*)
Lemma check_main_head {A V: Type} (ts: list (thread V A)) (r: A)
  : check_main ts = Some r -> ∃ts', ts = (Main $ Answer r) :: ts'.
  Proof.
    intro H.
    destruct ts as [|t ts'].
    - done.
    - exists ts'. simpl in *.
      destruct t.
      + simpl in *.
        destruct e; try done.
        simpl in *.
        injection H. intro Heq.
        subst r. done.
      + done.
  Qed.
(* 
  Get the iterated update lemma's into their own file,
  iApply nlaters to introduce them
  Then use the eqn from check_main to prove that:
  the first entry in ts' is a Main.
  That that thread is a Here.
  Then get the post condition out.

  The modalities seem to misallign here, it looks like
  it should be iterating |==> ▷ |==>?
  is that legal? Yes, Yes it is.
*)
Lemma fuel_adequacy {R} (γ: gname) (Φ: R -> iProp Σ) (n: nat)
  (h: heap nat)
  (s: scheduler nat R)
  (ts: list (thread nat R))
  : ts ≠ [] -> 
  state_interp γ h
  -∗ ([∗ list] t ∈ ts, wp_thread (state_interp γ) t Φ) 
  -∗ Nat.iter n (λ P : iPropI Σ, |={⊤, ∅}=> ▷ |={∅,⊤}=> P) 
      match runState (eval_threaded n s) h ts with
      | Here (x, h', ts') => Φ x 
      | ProgErr => False
      | EvalErr => True
      end.
Proof.
  iInduction n as [|n'] "IH" forall (s h ts);
  iIntros (Hnil) "Hsi Hbigop".
  - done.
  - iPoseProof (scheduled_adequacy _ _ _ s  with "Hsi Hbigop" ) as "H"; try done.
    iEval (unfold eval_threaded). fold (eval_threaded (V := nat) (R := R)).
    rewrite run_bind_dist.
    destruct (runState (single_step_thread _)  h ts) as [[[s' σ'] ts'] | | ]; try done.
    +
      rewrite run_bind_dist. 
      rewrite run_get_threads.
      destruct (check_main ts') eqn: E'. 
      * iSimpl. 
        iMod "H". iIntros "!> !>". 
        iApply fupd_nlaters; first set_solver. iMod "H". 
        apply check_main_head in E'.
        destruct E' as [ts'' E']. rewrite E'. simpl.
        iDestruct "H" as "(% & Hsi' & Hwp & Hbigop)".
        rewrite wp_unfold /=. done.
      * iSimpl.
        iMod "H". iIntros "!> !>".
        iMod "H". iModIntro.
        iDestruct "H" as "(% & Hsi' & Hbigop)".
        pose (Hnil' := non_nil_bigger_than  Hnil H).
        iApply ("IH" $! s' σ' ts' Hnil' with "Hsi' Hbigop").
    + iSimpl. iMod "H". iIntros "!> !>". iMod "H". iModIntro. 
      iApply fupd_nlaters; first set_solver. done.
    + iSimpl. iMod "H". iIntros "!> !>". iMod "H". iModIntro. 
      iApply fupd_nlaters; first set_solver. done.
Qed.

(*
  So what needs to happen here?
  1. I need to be in an iris context to use fuel_adequacy
     because it uses wands rather than coq arrows.
  2. To be able to lift the entailment from hpre like in adequacy_state_delay
     I will need to get a gname to allocate the initial heap.
     Why is there a gname in my context already? ok that was from the section,
     it is removed now.
  3. How do I get a gname? that is from this snippet:
    but that requires a bupd at the top level.
    can I change the soundness lemma to give me that?
     iMod (own_alloc (● (lift_excl st))) as (γ) "Hsi".
  4. When should I call lift entailment?
  5. Atleast I have my initial bupd from the soundness lemma now.
  6. I want to call fuel_adequacy, for that I need a big op of
     wp's for all threads. That list is [Main e]. However
     I have a wp for e in Hpre as expr not a thread.
     let's lift that.
     Now I need to get it in a big op
*)
Lemma adequacy {R} (φ: R -> Prop) (n: nat) 
  (SI: gmap nat nat -> iProp Σ)
  (s: scheduler nat R)
  (e: expr nat R)
  : (∀ γ, ⊢ wp (state_interp γ) ⊤ e (λ x, ⌜φ x⌝)) ->
  match run_program n s e with
  | Here x => φ x
  | ProgErr => False
  | EvalErr => True
  end.
  Proof.
    intros Hpre.
    unfold run_program.
    apply (step_fupdN_soundness' _ (S n)). simpl. iIntros (inv).
    (* apply (@later_bupdN_soundness'' (iResUR Σ) n). *)
    iMod (own_alloc (● (lift_excl ∅))) as (γ) "Hsi".
    { by apply auth_auth_valid. }
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iModIntro. iMod "Hclose". iModIntro.
    iDestruct (Hpre γ) as "Hwp". 
    iPoseProof (fuel_adequacy _ _ n  _ s ([Main e]) with "Hsi [$Hwp]" ) as "H"; try done. 
    destruct (runState _ _ _) as [[[v st] ts] | | ]; simpl.
    - iAssumption.  done.
    -
    -
  Qed.

Print Assumptions adequacy.

End adequacy.
(* 
  1. fancy update modality.
  2. CmpSwp primitive?
  
  CmpSwp 

  adequacy statement : voor alle schedelures alle initieele heaps.
  - Als het interpret naar een value in een aantal stappen
  - En er is een wp voor die expressie
  - Dan krijgen we die pure post conditie er uit.
  - En het programma loopt af.
  - 
*)