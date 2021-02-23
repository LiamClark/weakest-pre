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


Lemma wp_return {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
   (x: R) (Φ: R -> iProp Σ): Φ x -∗ wp SI (mret x) Φ.
Proof.
  iIntros"H".
  by rewrite wp_unfold.
Qed.

Lemma wp_think {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
   (e: expr V R) (Φ: R -> iProp Σ): ▷ wp SI e Φ -∗ wp SI (Think e) Φ.
Proof.
  iIntros "Hwp".
  iEval (rewrite wp_unfold). 
  done.
Qed.

Lemma wp_bind {Σ} {V R B: Type} (SI: gmap nat V -> iProp Σ)
  (f: R -> expr V B) (Φ: B -> iProp Σ) (e: expr V R): 
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
    iEval (rewrite wp_unfold /=) in "H".
    iMod ("H" $! σ with "HSi") as "H". iModIntro.
    iDestruct ("H") as (σ' v) "H".
    iExists σ', v.
    iDestruct "H" as  "($ & $ & Hwp)". 
    iNext. iApply "IH". done.
Qed.

Lemma wp_mono {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
   (e: expr V R) (Φ Ψ: R -> iProp Σ)
   :wp SI e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ wp SI e Ψ.
Proof.
  iLöb as "IH" forall (e).
  rewrite wp_unfold.
  rewrite wp_unfold.
  iIntros "Hwp H".
  destruct e; simpl.
  - iApply ("H" with "Hwp").
  - iNext. iApply ("IH" $! e with "Hwp H"). 
  - iNext. 
    iDestruct "Hwp" as "(Hwpe2 & $)".
    iApply ("IH" $! e2 with "Hwpe2 H"). 
  - iIntros (σ) "HSi".
    iMod ("Hwp" $! σ with "HSi" ) as "Hwp'".
    iDestruct "Hwp'" as (σ' v) "(Hcom & HSi' & Hwp'')".
    iModIntro. iExists σ', v. iFrame. iNext.
    iApply ("IH"  with "Hwp'' H"). 
  Qed.

(* 
  This is currently not provable because there is no update modality
  around every branch of our wp definition. The update is only there for Vis events.
  Do I introduce extra updates or first prove the weaker version of this?
 *)
Lemma wp_strong_mono_delay {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ) (e: expr V R)
  (Φ Ψ: R -> iProp Σ)
  : wp SI e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp SI e Ψ.
Proof.
  iLöb as "IH" forall (e).
  rewrite wp_unfold.
  rewrite wp_unfold.
  iIntros "Hwp H".
  destruct e; simpl.
  - iDestruct ("H" with "Hwp") as "bla".
    admit.
    (* iMod "Hwp" as "Hwp". iApply ("H" with "Hwp"). *)
  - admit.
    (* iMod "Hwp" as "Hwp". iModIntro. *)
    (* iNext. iApply ("IH" $! e with "Hwp H").  *)
Admitted.

Lemma wp_delay_fmap {Σ} {V R B: Type} (SI: gmap nat V -> iProp Σ) 
  (f: R -> B) (Φ: B -> iProp Σ) (e: expr V R)
  : wp SI e (Φ ∘ f ) -∗ wp SI (f <$> e) Φ. 
Proof.
  iIntros "Hwp".
  iApply wp_bind.
  iApply (wp_mono with "Hwp").
  iIntros (x) "Hpost /=".
  iApply (wp_return with "Hpost").
Qed.

Lemma wp_delay_iter {Σ} {V R B: Type} (SI: gmap nat V -> iProp Σ) (Φ: B -> iProp Σ)
  (x: R)
  (f: R -> expr V (R + B)):
  wp SI (f x) (case_ (λ x, ▷ wp SI (iter f x) Φ) Φ) -∗
  wp SI (iter f x) Φ.
Proof.
  iIntros "Hwp".
  rewrite iter_unfold.
  iApply wp_bind.
  iApply (wp_mono with "Hwp").
  iIntros ([a | b]) "H /=".
  - by iApply wp_think.
  - by iApply wp_return.
Qed.