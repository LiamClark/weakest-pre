From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import delaystate.
Set Default Proof Using "Type".

(* 
    What should the definition for wp look like?
    I want to match on the delay type and for answer apply the post condition.
    For the think branch I want to apply the wp recursively.

    Before I can get to the delay type I first need to run the state somehow.
    This is a wishful thinking version of the wp definition.
*)
Definition state_wp {Σ} {ST A} (SI: ST -> iProp Σ)
           (e: state_delay ST A) (Φ: A -> iProp Σ): iProp Σ := ∀ σ,
  SI σ ==∗
  match runState e σ with
       | Answer (Some (σ', x)) => Φ x ∗ SI σ'
       | Answer None => True
       | Think e' => True (*▷ state_wp SI e'Φ*)
  end.

(* The actual definition will need Iris fixpoint for this. Let's try finding that somewhere        
   Wp is here https://gitlab.mpi-sws.org/iris/iris/-/blob/master/theories/program_logic/weakestpre.v#L27
   The fixpoint is here: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/theories/program_logic/weakestpre.v#L47
*)

(* Definition state_wp {Σ} {ST A} (SI: ST -> iProp Σ) *)
           (* (e: state_delay ST A) (Φ: A -> iProp Σ): iProp Σ := ∀ σ, *)
  (* SI σ ==∗ *)
  (* ∃σ', ⌜runState e σ = Some (a, σ') ⌝ ∗ *)
          (* SI σ' ∗ *)
          (* Φ a. *)
(*
  We run into the same problem here as with the evaluator for state_delay: 
  We need the state aspect for our state interpretation and our notion of separation.
  We need to get to the Think constructor to recurse in our wp definition on the sub expression.
  However once we get to the Think node, although it does contain pre_wired stateful operations they are now
  completely opaque to us.

  In the evaluator we work around this by having the (co-)recursion only work for the delay monad
  Then add state on top as an extra layer. Can we write a wp that works just for delay?
*)

Definition wp_delay_pre {Σ} {A} (go: delay A -d> (A -d> iPropO Σ) -d> iPropO Σ):
      delay A -d> (A -d> iPropO Σ) -d> iPropO Σ.
refine(λ e Φ, |==> match e with
              | Answer x => Φ x
              | Think e' => ▷ go e' Φ
              end
              )%I.
Defined.

Instance wp_delay_pre_contractive {Σ A}: Contractive (@wp_delay_pre Σ A ).
Proof.
  rewrite /wp_delay_pre => n wp wp' Hwp e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.
 
Definition wp_delay {Σ} {A}: delay A -> (A -> iProp Σ)-> iProp Σ := fixpoint wp_delay_pre.

Definition wp {Σ} {ST A} (SI: ST -> iProp Σ) (e: state_delay ST A) (Φ: A -> iProp Σ): iProp Σ.
refine(∀ σ, 
    SI σ ==∗
     wp_delay (runState e σ) (λ (res: option (ST * A)), 
       match res with   
       | Some (σ', x) => Φ x ∗ SI σ'
       | None => True
       end)
)%I.
Defined.

Lemma wp_delay_unfold {Σ A} (e: delay A) (Φ: A -> iProp Σ): wp_delay e Φ ≡ wp_delay_pre wp_delay e Φ.
Proof.
  apply (fixpoint_unfold wp_delay_pre).
Qed.

Lemma wp_delay_return {Σ A}(x: A) (Φ: A -> iProp Σ): Φ x -∗ wp_delay (Answer x) Φ.
Proof.
   rewrite wp_delay_unfold.
   iIntros "H".
   iModIntro. done.
Qed.

Lemma wp_delay_bind {Σ A B} (f: A -> delay B) (Φ: B -> iProp Σ) (e: delay A): 
  wp_delay e (λ x, wp_delay (f x) Φ) -∗ wp_delay (e ≫= f) Φ.
Proof.
  unfold mbind, mbind_delay.
  iIntros "H". iLöb as "IH" forall (e).
  iEval (rewrite wp_delay_unfold).
  unfold wp_delay_pre.
  destruct e; simpl.
  - rewrite wp_delay_unfold /=. iMod "H" as "H". rewrite wp_delay_unfold /=.
    unfold wp_delay_pre. done.
  - iEval (rewrite wp_delay_unfold /=) in "H".
    iMod "H" as "H".
    iModIntro.
    iNext. iApply "IH". done.
Qed.

Lemma wp_state_return {Σ A ST } {SI: ST -> iProp Σ} (x: A) (Φ: A -> iProp Σ): Φ x -∗ wp SI (mret x) Φ.
Proof.
  iIntros "H" (σ) "HSi".
  simpl.
  iApply wp_delay_return. by iFrame.
Qed.

(* 
  get load store.
  iter combinators.
  Programs.
*)
Lemma wp_strong_mono_delay {Σ A} (e: delay A) (Φ Ψ: A -> iProp Σ) :
  wp_delay e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp_delay e Ψ.
Proof.
  iLöb as "IH" forall (e).
  rewrite wp_delay_unfold.
  rewrite wp_delay_unfold.
  iIntros "Hwp H".
  unfold wp_delay_pre.
  destruct e; simpl.
  - iMod "Hwp" as "Hwp". iApply ("H" with "Hwp").
  - iMod "Hwp" as "Hwp". iModIntro.
    iNext. iApply ("IH" $! e with "Hwp H"). 
Qed.

Lemma wp_strong_mono {Σ A ST SI} (e: state_delay ST A) (Φ Ψ : A -> iProp Σ):
  wp SI e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp SI e Ψ .
Proof.
  unfold wp.
  iIntros "Hwp H" (σ) "HSi".
  iDestruct ("Hwp" with "HSi") as "Hwp".
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([[s x] | ]). 
  - iIntros "(Hpost & $)".
    by iApply "H".
  - done.
Qed.

Lemma bupd_wp_delay {Σ A} (e: delay A) (Φ : A -> iProp Σ) : (|==> wp_delay e Φ) ⊢ wp_delay e Φ.
Proof.
  iIntros "Hwp".
  rewrite wp_delay_unfold.
  unfold wp_delay_pre.
  by iMod "Hwp" as "Hwp".
Qed.

Lemma wp_bupd_delay {Σ A} (e: delay A) (Φ : A -> iProp Σ) : wp_delay e (λ v, |==> Φ v) ⊢ wp_delay e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono_delay with "Hwp").
  auto.
Qed.

Lemma bupd_wp {Σ A ST SI} (e: state_delay ST A) (Φ : A -> iProp Σ): (|==> wp SI e Φ) ⊢ wp SI e Φ.
Proof.
  iIntros "Hwp".
  unfold wp. iIntros (σ) "Hsi". 
  by iMod ("Hwp" with "Hsi").
Qed.

Lemma wp_bupd {Σ A ST SI} (e: state_delay ST A) (Φ : A -> iProp Σ): wp SI e (λ v, |==> Φ v) ⊢ wp SI e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono with "Hwp").
  auto.
Qed.

Locate "|==>".
Print bupd.
Lemma wp_state_bind {Σ A B ST} {SI: ST -> iProp Σ}
  (f: A -> state_delay ST B)
  (Φ: B -> iProp Σ)
  (e: state_delay ST A)
  : wp SI e (λ x, wp SI (f x) Φ) -∗ wp SI (e ≫= f) Φ.
Proof.
  iIntros "H" (σ) "HSi". rewrite /mbind /mbind_state_delay /=.
  iApply wp_delay_bind.
  iMod ("H" with  "HSi") as "H".
  iModIntro.
  iApply (wp_strong_mono_delay with "H").
  iIntros ([[s x] | ]).
  - iIntros "(Hwp & HSi)".
    unfold wp. iApply ("Hwp" $! (s) with "HSi").
  - iIntros "_ !>".
    by iApply wp_delay_return.
Qed.
About fixpoint.