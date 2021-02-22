From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import delayfree.
Set Default Proof Using "Type".

(* Curry the value R so it can be changed by the dependent pattern match on c *)
Definition command_predicate {V R} (c: envE V R) (σ σ': gmap loc V): R -> Prop.
refine (match c with
        |GetE l  => λ v, σ !! l = Some v /\ σ' = σ 
        |PutE l v' => λ _, is_Some (σ !! l) /\ σ' = <[l := v']> σ
        |AllocE v' => λ l, σ !! l = None /\ σ' = <[l := v']> σ
        |FreeE l => λ _, is_Some (σ !! l) /\ σ' = delete l σ
        end
).
Defined.

Definition wp_pre {Σ} {V} (SI: gmap loc V -> iProp Σ)
     (go: discrete_funO (λ R, expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ)):
     discrete_funO (λ R, expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ).
refine(λ R e Φ,
        match e with
        |Answer x => Φ x 
        |Think e' => ▷ go R e' Φ
        |Fork e' k => ▷ (go R k Φ ∗ go unit e' (λ _, True))
        |Vis c k => ∀σ, SI σ ==∗ ∃σ' v, ⌜command_predicate c σ σ' v⌝ ∗ SI σ' ∗ ▷ (go R (k v)) Φ
        end
)%I.
Defined.

Instance wp_pre_contractive {Σ A SI}: Contractive (@wp_pre Σ A SI).
Proof.
  rewrite /wp_pre => n wp wp' Hwp R e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp' {Σ} {V} (SI: gmap nat V -> iProp Σ)
              : ∀R, expr V R -> (R -> iProp Σ) ->iProp Σ :=
    fixpoint (wp_pre SI ).

Definition wp {Σ} {V R} (SI: gmap nat V -> iProp Σ) (e: expr V R) (Φ: R -> iProp Σ): iProp Σ := 
    wp' SI R e Φ.

Lemma wp_unfold {Σ} {V R} (e: expr V R) (SI: gmap nat V -> iProp Σ) (Φ: R -> iProp Σ)
  : wp SI e Φ ≡  wp_pre SI (wp' SI) R e Φ.
Proof.
  apply (fixpoint_unfold (wp_pre SI)).
Qed.

Section wp_rules.
  Context {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ).

  Lemma wp_return (x: R) (Φ: R -> iProp Σ): Φ x -∗ wp SI (mret x) Φ.
  Proof.
    iIntros"H".
    by rewrite wp_unfold.
  Qed.

  Lemma wp_think (e: expr V R) (Φ: R -> iProp Σ): ▷ wp SI e Φ -∗ wp SI (Think e) Φ.
  Proof.
    iIntros "Hwp".
    iEval (rewrite wp_unfold). 
    done.
  Qed.

 (*
   This proof is huge becasue of the case distinction on commands
   is that avoidable?
 *)
  Lemma wp_bind {B} (f: R -> expr V B) (Φ: B -> iProp Σ) (e: expr V R): 
    wp SI e (λ x, wp SI (f x) Φ) -∗ wp SI (e ≫= f) Φ.
  Proof.
    unfold mbind, itree_bind.
    iIntros "H". iLöb as "IH" forall (e).
    iEval (rewrite wp_unfold).
    unfold wp_pre.
    destruct e; simpl.
    - do 2 (rewrite wp_unfold /=). unfold wp_pre.
      done.
    - iEval (rewrite wp_unfold /=) in "H".
      iNext. iApply "IH". done.
    - iEval (rewrite wp_unfold /=) in "H".
      iNext. iDestruct "H" as "(H & $)". 
      iApply "IH". done.
    - iIntros (σ)  "HSi".
      destruct e.
      + iEval (rewrite wp_unfold /=) in "H".
        iMod ("H" $! σ with "HSi") as "H". iModIntro.
        iDestruct ("H") as (σ' v) "H".
        iExists σ', v.
        iDestruct "H" as (Hlookup) "(HSi' & Hwp')". 
        iSplit.
        * iPureIntro. done.
        * iFrame. iNext. iApply "IH". done.
      + 
        iEval (rewrite wp_unfold /=) in "H".
        iMod ("H" $! σ with "HSi") as "H". iModIntro.
        iDestruct ("H") as (σ' vtt) "H".
        iExists σ', vtt.
        iDestruct "H" as (Hput) "(HSi' & Hwp')". 
        iSplit.
        * iPureIntro. done.
        * iFrame. iNext.
          iApply "IH". done.
      + iEval (rewrite wp_unfold /=) in "H".
        iMod ("H" $! σ with "HSi") as "H". iModIntro.
        iDestruct ("H") as (σ' vtt) "H".
        iExists σ', vtt.
        iDestruct "H" as (Hput) "(HSi' & Hwp')". 
        iSplit.
        * iPureIntro. done.
        * iFrame. iNext.
          iApply "IH". done.
      + iEval (rewrite wp_unfold /=) in "H".
        iMod ("H" $! σ with "HSi") as "H". iModIntro.
        iDestruct ("H") as (σ' vtt) "H".
        iExists σ', vtt.
        iDestruct "H" as (Hput) "(HSi' & Hwp')". 
        iSplit.
        * iPureIntro. done.
        * iFrame. iNext.
          iApply "IH". done.
  Qed.