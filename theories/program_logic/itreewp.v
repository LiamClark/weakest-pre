From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.bi Require Import derived_laws.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import heapmodel modal itree evaluation.
Set Default Proof Using "Type".

Section itreewp.
  Context `{!invGS Σ}. 

(* Curry the value R so it can be changed by the dependent pattern match on c *)
Definition command_predicate {V R} (c: envE V R) (σ σ': gmap loc V): R -> Prop.
refine (
  match c with
  | GetE l           => λ v, σ !! l = Some v /\ σ' = σ 
  | PutE l v'        => λ _, is_Some (σ !! l) /\ σ' = <[l := v']> σ
  | AllocE v'        => λ l, l = fresh_loc σ /\ σ' = <[l := v']> σ
  | FreeE l          => λ _, is_Some (σ !! l) /\ σ' = delete l σ
  | CmpXchgE l v1 v2 => λ '(vret, upd), if upd then σ !! l = Some v1 /\ vret = v1 /\ σ' = <[l := v2]> σ  
                                   else ∃x, σ !! l = Some x /\ vret = x /\ σ = σ' /\ x ≠ v1
  | FailE            => λ v, False
  end
).
Defined.

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

(* Locate "|={ _ }=> _". *)
(* Locate "|={ _ , _ }=> _". *)
(* Check fupd. *)
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

(* Search FUpd. *)
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

(* Locate "|={ _ }[ _ ]▷=>". *)
(* Locate "|={ _ }[ _ ]▷=> _". *)
(* on newer versions of Iris *)
(* Check fupd_mask_intro.  *)

(* Check fupd_intro_mask. *)
(* Check fupd_mask_weaken. *)

(* (IH * P) ⊢ wp e Φ*)
(* ▷ (IH * P) ⊢ ▷ wp e Φ*)
(* ▷ IH * ▷ P ⊢ ▷ wp e Φ *)
(* ▷ IH * P ⊢ ▷ wp e Φ *)
(* ▷ IH * P ⊢ wp (Think e) Φ *)

(* loop x = loop x

iter (_. inl ()) *)

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


(* Print uPred_fupd. *)
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

(* Check fupd_mask_mono. *)
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

Lemma wp_mono' {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
   (e: expr V R) (Φ Ψ: R -> iProp Σ)
   : (∀ v, Φ v -∗ Ψ v) -> wp SI E e Φ -∗  wp SI E e Ψ.
Proof.
  iIntros (Hv) "Hwp".
  iApply (wp_strong_mono_fupd with "Hwp"); first set_solver.
  - iIntros (v) "Hphi". 
    iModIntro.
    iApply (Hv with "Hphi").
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

Lemma wp_iter {V R B: Type} (SI: gmap nat V -> iProp Σ) (E: coPset) (Φ: B -> iProp Σ)
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

Lemma fupd_wp {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
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

Lemma bupd_wp {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset)
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

Lemma wp_frame_r {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset) 
  (e: expr V R) (Φ: R -> iProp Σ) (P: iProp Σ)
  : ((wp SI E e Φ) ∗ P) ⊢ wp SI E e (λ v, Φ v ∗ P).
  Proof.
    iIntros "[Hwp Hp]".
    iApply (wp_strong_mono_bupd with "Hwp").
    auto with iFrame.
  Qed.

Lemma wp_frame_l {V R: Type} (SI: gmap nat V -> iProp Σ) (E: coPset) 
  (e: expr V R) (Φ: R -> iProp Σ) (P: iProp Σ)
  : (P ∗ (wp SI E e Φ) ) ⊢ wp SI E e (λ v, P ∗ Φ v ).
  Proof.
    iIntros "[Hp Hwp]".
    iApply (wp_strong_mono_bupd with "Hwp").
    auto with iFrame.
  Qed.

  (* Lemma wp_fork {V R: Type} (SI: gmap nat V -> iProp Σ) (e1: expr V ()) (e2: expr V R) (E: coPset) (Φ: R -> iProp Σ):
   ▷ wp SI  ⊤ e1 (λ _, True) -∗ wp SI E e2 Φ -∗  wp SI E (Fork e1 e2) Φ.
  Proof.
    iIntros "Hwpf HwpΦ".
    iEval( rewrite wp_unfold). unfold wp_pre.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iFrame.
  Qed. *)

  Lemma wp_fork {V R: Type} (SI: gmap nat V -> iProp Σ) (e: expr V ()) (E: coPset) (Φ: () -> iProp Σ):
   ▷ wp SI ⊤ e (λ _, True) -∗ Φ () -∗ wp SI E (itree.fork e) Φ.
  Proof.
    iIntros "Hwpf HΦ".
    iEval( rewrite wp_unfold). unfold wp_pre.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iFrame. by iApply wp_return.
  Qed.
End itreewp.

Section heap_wp.
  Context `{! inG Σ (heapR V)}.
  Context `{!invGS Σ}.
  Context (γ: gname).

  Lemma wp_get n v E (Ψ: V -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ wp (state_interp γ) E (itree.get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro. iExists σ, v. simpl.
    iDestruct (si_get with "Hsi Hpt") as %H. 
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
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_put with "Hsi Hpt") as "(Hsi & Hpt)". 
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

  Lemma wp_put' n v v' E (Ψ: unit -> iProp Σ) :
    ▷ points_to γ n v -∗ ▷ (points_to γ n v' -∗ Ψ tt) -∗ wp (state_interp γ) E (itree.put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi". 
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>".
    iDestruct (si_get with "Hsi Hpt") as %Hsome.   
    iMod (si_put with "Hsi Hpt") as "(Hsi & Hpt)". 
    iMod "Hclose". iModIntro.
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
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
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

  Lemma wp_cmpXchg_suc l v1 v2 E (Φ: (V * bool) -> iProp Σ):
    points_to γ l v1
    -∗ ▷(points_to γ l v2  -∗ Φ (v1, true))
    -∗ wp (state_interp γ) E (itree.cmpXchg l v1 v2) Φ.
  Proof.
    iIntros "Hpt HPost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_put with "Hsi Hpt") as "(Hsi & Hpt)".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iExists (<[l := v2]> σ), (v1, true). simpl.
    iSplit.
    - by iPureIntro.
    - iFrame.
      iApply wp_return.
      by iApply "HPost".
  Qed.

  Lemma wp_cmpXchg_suc' l v1 v2 E (Φ: (V * bool) -> iProp Σ):
    ▷ points_to γ l v1
    -∗ ▷(points_to γ l v2  -∗ Φ (v1, true))
    -∗ wp (state_interp γ) E (itree.cmpXchg l v1 v2) Φ.
  Proof.
    iIntros "Hpt HPost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". 
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_put with "Hsi Hpt") as "(Hsi & Hpt)".
    iMod "Hclose". iModIntro.
    iExists (<[l := v2]> σ), (v1, true). simpl.
    iSplit.
    - by iPureIntro.
    - iFrame.
      iApply wp_return.
      by iApply "HPost".
  Qed.

  Lemma wp_cmpXchg_fail l v1 v2 v3 E (Φ: (V * bool) -> iProp Σ):
    ⌜v1 <> v3⌝ -∗
    points_to γ l v1
    -∗ ▷(points_to γ l v1  -∗ Φ (v1, false))
    -∗ wp (state_interp γ) E (itree.cmpXchg l v3 v2) Φ.
  Proof.
    iIntros "%Hneq Hpt HPost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iExists  σ, (v1, false). simpl.
    iSplit.
    - iPureIntro. by exists v1.
    - iFrame.
      iApply wp_return.
      by iApply "HPost".
  Qed.
 
  Lemma wp_cmpXchg_fail' l v1 v2 v3 E (Φ: (V * bool) -> iProp Σ):
    ⌜v1 <> v3⌝ -∗
    ▷ points_to γ l v1
    -∗ ▷ (points_to γ l v1  -∗ Φ (v1, false))
    -∗ wp (state_interp γ) E (itree.cmpXchg l v3 v2) Φ.
  Proof.
    iIntros "%Hneq Hpt HPost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose !>". iMod "Hclose". iModIntro.
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iExists  σ, (v1, false). simpl.
    iSplit.
    - iPureIntro. by exists v1.
    - iFrame.
      iApply wp_return.
      by iApply "HPost".
  Qed.


End heap_wp.


(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!invGS Σ}.
  Context `{!inG Σ (heapR V)}.
  Context (A: Type).
  Context (SI: gmap nat V -> iProp Σ).
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : A -> iProp Σ.
  Implicit Types v : A.
  Implicit Types e : expr V A.

  Global Instance frame_wp p E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (wp SI E e Φ) (wp SI E e Ψ) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono', HR.
  Qed.

  Global Instance is_except_0_wp E e Φ : IsExcept0 (wp SI E e Φ).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E e P Φ :
    ElimModal True p false (|==> P) P (wp SI E e Φ) (wp SI E e Φ ).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p E e P Φ :
    ElimModal True p false (|={E}=> P) P (wp SI E e Φ ) (wp SI E e Φ).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p E1 E2 e P Φ :
    ElimModal (atomic e) p false
            (|={E1,E2}=> P) P
            (wp SI E1 e Φ) (wp SI E2 e (λ v, |={E2,E1}=> Φ v))%I | 100.
  Proof.
    intros ?. by rewrite bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp E e P Φ :
    AddModal (|={E}=> P) P (wp SI E e Φ).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e Φ :
    ElimAcc (X:=X) (atomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (wp SI E1 e Φ)
            (λ x, wp SI E2 e (λ v, |={E2}=> β x ∗ (γ x -∗? Φ v)))%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_mono with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (wp SI E e Φ)
            (λ x, wp SI E e (λ v, |={E}=> β x ∗ (γ x -∗? Φ v)))%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_mono with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.


Section adequacy.
  Context `{!inG Σ (heapR V)}.
  Context `{!invGS Σ}. 

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
  Lemma step_expr_adequacy {R A} {cmp: EqDecision V} (γ: gname) (Φ: R -> iProp Σ) (Ψ: A -> iProp Σ)
    (h: heap V)
    (ts: list (thread V R))
    (e: expr V A)
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
      destruct e.
      + simpl. destruct H as (Hlookup & Heq). rewrite Hlookup. subst h. simpl.
        iExists []. rewrite right_id_L.
        iFrame. auto.
      + simpl. destruct H as ((v' & Hsome) & Heq). subst σ'. destruct v.
        rewrite Hsome. simpl.
        iExists []. rewrite right_id_L.
        iFrame. auto.
      + simpl. destruct H as (Hlookup & Heq). subst σ' v.
        iExists []. rewrite right_id_L.
        iFrame. auto.
      + simpl. destruct H as ((v' & Hsome) & Heq). subst σ'. destruct v.
        rewrite Hsome. simpl.
        iExists []. rewrite right_id_L.
        iFrame. auto.
      + destruct v as [vret [|]]; simpl in H.
        * destruct H as (HLookup & -> & ->).
        unfold step_vis. unfold cmpXchg.
        simpl.
        rewrite HLookup. simpl.
        rewrite decide_True //. simpl.
        rewrite HLookup.
        iExists []. rewrite right_id_L.
        iFrame. auto.
        * destruct H as (x & HLookup & -> & -> & Hneq).
          unfold step_vis. unfold cmpXchg. simpl.
          rewrite HLookup. simpl.
          rewrite decide_False //.
          iExists []. rewrite right_id_L.
          iFrame. auto.
      +  iModIntro. done.
  Qed.

  (* 
   We still have two post conditions, but they operate on the same type now.
   Ψ is for the thread we are stepping. Ah so this is the above lifted to a thread.
   Φ is still the post condition for the main thread.
  *)
  Lemma step_thread_adequacy {R} {cmp: EqDecision V} (γ: gname) (Φ Ψ: R -> iProp Σ)
    (h: heap V)
    (ts: list (thread V R))
    (ct: thread V R)
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
  Lemma scheduled_adequacy {R} {cmp: EqDecision V} (γ: gname) (Φ: R -> iProp Σ)
    (h: heap V)
    (s: scheduler V R)
    (ts: list (thread V R))
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

  Lemma run_get_threads {A} σ (ts: list (thread V A))
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
  Lemma check_main_head {A: Type} (ts: list (thread V A)) (r: A)
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
  Lemma fuel_adequacy {R} {cmp: EqDecision V} (γ: gname) (Φ: R -> iProp Σ) (n: nat)
    (h: heap V)
    (s: scheduler V R)
    (ts: list (thread V R))
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

End adequacy.


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
Lemma adequacy {V Σ} {cmp: EqDecision V} `{!inG Σ (heapR V)} `{!invGpreS Σ} {R} (φ: R -> Prop) (n: nat)
  (SI: gmap nat V -> iProp Σ)
  (s: scheduler V R)
  (e: expr V R)
  : (∀ `{!invGS Σ} γ, ⊢ wp (state_interp γ) ⊤ e (λ x, ⌜φ x⌝)) ->
  match run_program n s e with
  | Here x => φ x
  | ProgErr => False
  | EvalErr => True
  end.
  Proof.
    intros Hpre.
    unfold run_program.
    apply (step_fupdN_soundness' _ (S n)). simpl. iIntros (inv).
    iMod (own_alloc (● (lift_excl ∅))) as (γ) "Hsi".
    { by apply auth_auth_valid. }
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iModIntro. iMod "Hclose". iModIntro.
    iDestruct (Hpre inv γ) as "Hwp".
    iPoseProof (fuel_adequacy _ _ n  _ s ([Main e]) with "Hsi [$Hwp]" ) as "H"; try done.
    destruct (runState _ _ _) as [[[v st] ts] | | ]; simpl; done.
Qed.

Print Assumptions adequacy.