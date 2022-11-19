From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import heapmodel modal delaystate. 
Set Default Proof Using "Type".

(* wp definition for delay monad *)
Definition wp_delay_pre {Σ} {A} (go: delay A -d> (A -d> iPropO Σ) -d> iPropO Σ):
      delay A -d> (A -d> iPropO Σ) -d> iPropO Σ.
refine(
  λ e Φ, |==> match e with
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
 
Definition wp_delay {Σ} {A}: delay A -> (A -> iProp Σ) -> iProp Σ := fixpoint wp_delay_pre.

(* Definition of a wp connective for state_delay by layering it ontop of our wp definition for just
   the delay monad
*)
Definition wp {Σ} {ST A} (SI: ST -> iProp Σ) (e: state_delay ST A) (Φ: A -> iProp Σ): iProp Σ :=
  ∀ σ, 
    SI σ ==∗
      wp_delay (runState e σ) (λ (res: option (ST * A)), 
        match res with   
        | Some (σ', x) => SI σ' ∗ Φ x 
        | None => True
        end
      )%I.

Lemma wp_delay_unfold {Σ A} (e: delay A) (Φ: A -> iProp Σ): wp_delay e Φ ≡ wp_delay_pre wp_delay e Φ.
Proof.
   apply (fixpoint_unfold wp_delay_pre).
Qed.

Lemma wp_delay_return {Σ A} (x: A) (Φ: A -> iProp Σ): Φ x -∗ wp_delay (Answer x) Φ.
Proof.
   rewrite wp_delay_unfold.
   iIntros "H".
   iModIntro. done.
Qed.

Lemma wp_delay_think {Σ A}(e: delay A) (Φ: A -> iProp Σ): ▷ wp_delay e Φ -∗ wp_delay (Think e) Φ.
Proof.
  iIntros "Hwp".
  iEval(rewrite wp_delay_unfold). unfold wp_delay_pre.
  done.
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

Lemma wp_strong_mono_delay {Σ A} (e: delay A) (Φ Ψ: A -> iProp Σ):
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

Lemma wp_delay_fmap {Σ A B} (f: A -> B) (Φ: B -> iProp Σ) (e: delay A): 
  wp_delay e (Φ ∘ f ) -∗ wp_delay (f <$> e) Φ. 
Proof.
  iIntros "Hwp".
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros (x) "Hpost !> /=".
  by iApply wp_delay_return.
Qed.

Lemma wp_delay_iter {Σ A B} (Φ: B -> iProp Σ)
  (x: A)
  (f: A -> delay (A + B)):
  wp_delay (f x) (case_ (λ x, ▷ wp_delay (iter f x) Φ) Φ) -∗ wp_delay (iter f x) Φ.
Proof.
  iIntros "Hwp".
  rewrite iter_unfold.
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([a | b]) "H !> /=".
  - by iApply wp_delay_think.
  - by iApply wp_delay_return.
Qed.

(* Direct wp rules for loop rather than using those for iter*)
Lemma wp_delay_loop_rec {Σ A B C} (Φ: B -> iProp Σ)
  (x: C + A)
  (f: C + A -> delay (C + B)):
  wp_delay (f x) (λ cb, 
                    match cb with
                    | inl c  => ▷ wp_delay (loop_rec f (inl c)) Φ
                    | inr b  =>  Φ b
                    end
  ) 
  -∗ wp_delay (loop_rec f x) Φ.
Proof.
  iIntros "Hwp".
  rewrite loop_rec_unfold.
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([a | b]) "H !> /=".
  - by iApply wp_delay_think.
  - by iApply wp_delay_return.
Qed.

Lemma wp_delay_loop' {Σ A B C} (Φ: B -> iProp Σ)
  (x: A)
  (f: C + A -> delay (C + B)):
  wp_delay (f (inr x)) (λ cb, 
                    match cb with
                    | inl c  => ▷ wp_delay (loop_rec f (inl c)) Φ
                    | inr b  =>  Φ b
                    end
  ) 
  -∗ wp_delay (loop' f x) Φ.
Proof.
  by iApply wp_delay_loop_rec.
Qed.

Lemma bupd_wp_delay {Σ A} (e: delay A) (Φ : A -> iProp Σ): (|==> wp_delay e Φ) ⊢ wp_delay e Φ.
Proof.
  iIntros "Hwp".
  rewrite wp_delay_unfold.
  unfold wp_delay_pre.
  by iMod "Hwp" as "Hwp".
Qed.

Lemma wp_bupd_delay {Σ A} (e: delay A) (Φ : A -> iProp Σ): wp_delay e (λ v, |==> Φ v) ⊢ wp_delay e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono_delay with "Hwp").
  auto.
Qed.

Lemma adequacy_delay {A} {Σ} (φ: A -> Prop) (n: nat) (x: A) (prog : delay A):
    (⊢ @wp_delay Σ A prog (λ x, ⌜φ x⌝)) 
    -> eval_delay n prog = Some x 
    -> φ x.
Proof.
  intros Hpre Heval.
  apply (@later_bupdN_soundness (iResUR Σ) n).
  revert Hpre.
  apply lift_entails.
  iIntros "Hpre".
  iInduction n as [|n'] "IH" forall (prog Heval).
  - done.
  - simpl in *.
    rewrite wp_delay_unfold.
    unfold wp_delay_pre.
    destruct prog as [a| prog']. simplify_eq/=.
    + iMod "Hpre" as %Hpre.
      iModIntro. iNext.
      by iApply nlaters.
    + iMod "Hpre". iModIntro. iNext.
      by iApply "IH".
Qed.

(* Rules for the state_delay monad*)
Lemma wp_strong_mono {Σ A ST SI} (e: state_delay ST A) (Φ Ψ : A -> iProp Σ):
  wp SI e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp SI e Ψ .
Proof.
  unfold wp.
  iIntros "Hwp H" (σ) "HSi".
  iDestruct ("Hwp" with "HSi") as "Hwp".
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([[s x] | ]). 
  - iIntros "($ & HPost)".
    by iApply "H".
  - done.
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

Lemma wp_return {Σ A ST } {SI: ST -> iProp Σ} (x: A) (Φ: A -> iProp Σ):
   Φ x -∗ wp SI (mret x) Φ.
Proof.
  iIntros "H" (σ) "HSi".
  simpl.
  iApply wp_delay_return. by iFrame.
Qed.

Lemma wp_fmap  {Σ A B ST} {SI: ST -> iProp Σ}
 (f: A -> B)
 (Φ: B -> iProp Σ)
 (e: state_delay ST A):
  wp SI e (Φ ∘ f ) -∗ wp SI (f <$> e) Φ. 
Proof.
  iIntros "Hwp" (σ) "Hsi".
  rewrite /fmap /fmap_state_delay /=.
  iApply wp_delay_fmap.
  iMod ("Hwp" with "Hsi") as "H".
  iModIntro.
  iApply (wp_strong_mono_delay with "H").
  by iIntros ([[st x]| ]) "H !> /=".
Qed.

Lemma wp_bind {Σ A B ST} {SI: ST -> iProp Σ}
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
  - iIntros "(HSi & Hwp)".
    unfold wp. iApply ("Hwp" $! (s) with "HSi").
  - iIntros "_ !>".
    by iApply wp_delay_return.
Qed.

Section state_wp.
  Context {Σ} {ST} (SI: ST -> iProp Σ).

Lemma wp_iter {A B} (Φ: B -> iProp Σ)
  (x: A)
  (f: A -> state_delay ST (A + B)):
  wp SI (f x) (case_ (λ x, ▷ wp SI (iter_state_delay f x) Φ) Φ) -∗
  wp SI (iter_state_delay f x) Φ.
Proof.
  iIntros "Hwp" (σ) "Hsi".
  iApply wp_delay_iter.
  iMod ("Hwp" $! (σ) with "Hsi") as "Hwp /=".
  iModIntro.
  unfold distribute_delay_state.
  iApply wp_delay_fmap.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([[s [a| b]]| ]) "Hpost /="; [ |auto..].
  iDestruct "Hpost" as "(Hsi & Hwp')".
  iIntros "!> !>".
  unfold iter_state_delay.
  unfold distribute_delay_state.
  iApply bupd_wp_delay.
  iMod ("Hwp'" with "Hsi") as "Hwp' /= ".
  iModIntro.
  done.
Qed.

Lemma wp_getS Φ : (∀σ, SI σ ==∗ SI σ ∗ Φ σ) -∗ wp SI (getS) Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost".
  by iApply wp_delay_return.
Qed.

Lemma wp_putS Φ σ' : (∀σ, SI σ ==∗ SI σ' ∗ Φ tt) -∗ wp SI (putS σ') Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost /=".
  by iApply wp_delay_return.
Qed.
End state_wp.

Section delay_wp_heap.
  Context `{! inG Σ (heapR V)}.
  Context (γ: gname).
  
  Lemma wp_get n v (Ψ: V -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ wp (state_interp γ) (get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_get with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_return. by iApply "Hpost".
  Qed.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ wp (state_interp γ) (put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iIntros (σ) "Hsi". 
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_put with "Hsi Hpt") as "(? & Hup)".
    iModIntro. simpl. rewrite Hsome. simpl. iApply wp_delay_return.
    iFrame. by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ wp (state_interp γ) (alloc v) Ψ.
  Proof.
    iIntros "Hpost".
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "(Hsi & Hpt)".
    unfold alloc. iApply wp_delay_return.
    iModIntro. iFrame.
    iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ wp (state_interp γ) (free l) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iIntros (σ) "Hsi".
    iDestruct (si_get with "Hsi Hpt") as %Hsome.
    iMod (si_free with "Hsi Hpt") as "? /=".
    iModIntro. rewrite Hsome. simpl. iApply wp_delay_return.
    iFrame.
  Qed.
End delay_wp_heap.


Section state_delay_adequacy.
  Context `{! inG Σ (heapR V)}.

  (* Transport an evaluation result from the state_delay monad to the delay monad *)
  Lemma eval_state_eval_delay {A} (n: nat) (x: A)
   (prog: state_delay (gmap nat V) A)
   (st st': gmap nat V):  
   eval_state_delay' n prog st = Some (st', x) ->
   eval_delay n (runState prog st) = Some $ Some (st', x).
  Proof.
    intros Hev_state_delay.
    unfold eval_state_delay' in *.
    unfold mjoin in *. unfold option_join in *.
    destruct (eval_delay n (runState prog st)).
    - by simplify_eq /=.
    - done.
  Qed.
  
  (*
    For adequacy we need the post condition wp uses for wp_delay to change to a 
    pure assertion.
  *)
  Definition adapt_post {A} (φ: A -> Prop): option (gmap nat V * A) -> Prop :=
    λ res, match res with
           | Some (_, x) => φ x
           | None => True
           end.

  Lemma adapt_pre {A} {γ} (φ: A -> Prop) (res: option (gmap nat V * A)):
                     match res with
                     | Some (σ', x') => (state_interp γ σ' ∗ ⌜φ x'⌝)%I
                     | None => True%I
                     end -∗ ⌜(adapt_post φ) res ⌝.
  Proof.
    iIntros "Hpre".
    unfold adapt_post.
    destruct res as [[σ' x]| ].
    - by iDestruct "Hpre" as "(Hsi & Hpure)".
    - done.
  Qed.
  
  (*
    Specialisation of adequacy delay that exposes the adapted post conditions and state tuples
    This makes it easier to call in adequacy_state_delay.
  *)
  Lemma adequacy_state_inbetween {A} (φ: A -> Prop) (n: nat) 
    (x: A) 
    (prog : state_delay (gmap nat V) A)
    (st st': gmap nat V):
    (⊢ @wp_delay Σ _(runState prog st) (λ y, ⌜adapt_post φ y⌝)) 
    -> (eval_delay n (runState prog st) = Some (Some (st', x)))
    -> (adapt_post φ (Some (st', x))).
  Proof.
    apply adequacy_delay.
  Qed. 

  (*
    For adequacy_delay_state we need an extra update modality compared to the normal
    adequacy statement for the delay monad. 
    It is required in order to allocate the initial heap and get a gname.
  *) 
  Lemma adequacy_state_delay {A} (φ: A -> Prop) (n: nat) (x: A) 
    (prog : state_delay (gmap nat V) A)
    (st st': gmap nat V)
    : (∀γ, ⊢ wp (state_interp γ) prog (λ x, ⌜φ x⌝)) 
    -> eval_state_delay' n prog st = Some (st', x)
    -> φ x. 
  Proof.
    intros Hpre Heval.
    eapply adequacy_state_inbetween.
    unfold wp in Hpre.
    -
      iApply bupd_wp_delay. 
      iMod (own_alloc (● (lift_excl st))) as (γ) "Hsi".
      + apply auth_auth_valid. intro i. 
        rewrite lookup_fmap. destruct (st !! i); done.
      + 
         iMod (Hpre γ $! st with "Hsi") as "HDelaypre".
         iModIntro.
         iApply (wp_strong_mono_delay with "[$]").
         iIntros (v) "H".
         by iApply adapt_pre. 
    - by apply eval_state_eval_delay.
  Qed. 
End state_delay_adequacy.

(* Formalisation of hoare triples for the delay monad *)
(*{P} e {Q} =  □(P -* wp e {Q}) *)
Definition hoare_delay {Σ} {A} (P: iProp Σ) (e: delay A) (Q: A -> iProp Σ): iProp Σ
:= □ (P -∗ wp_delay e Q).
(*
  persistent hypothesis can be moved between the hoare pre condition and the context
  hoare_ctx
*)

(* 
  rule Equivalent for:
  Lemma wp_delay_think {Σ A}(e: delay A) (Φ: A -> iProp Σ): ▷ wp_delay e Φ -∗ wp_delay (Think e) Φ.
*)
Lemma hoare_delay_think {Σ A} (e: delay A) (P: iProp Σ) (Q: A -> iProp Σ):
   hoare_delay P e Q -∗ hoare_delay (▷ P) (Think e) Q.
Proof.
  iIntros "#Hhoare !>".
  unfold hoare_delay.
  iIntros "Hp".
  iApply wp_delay_think.
  iNext.
  iApply ("Hhoare" with "Hp").
Qed.

Lemma hoare_delay_mret' {Σ A} (x: A) (Q: iProp Σ) (P: A -> iProp Σ):
  □(Q -∗ P x) -∗ hoare_delay Q (Answer x) P.
Proof.
  unfold hoare_delay.
  iIntros "#Hwand !> Hp".
  iApply wp_delay_return. 
  by iApply "Hwand".
Qed.

Lemma hoare_delay_consequence {Σ A} (P P': iProp Σ) (Q Q': A -> iProp Σ)
  (e: delay A)
  : □(P' -∗ P) -∗ □(∀x, Q x -∗ Q' x)
  -∗ hoare_delay P e Q
  -∗ hoare_delay P' e Q'.
Proof.
  iIntros "#Hp #Hq #Hhd".
  iIntros "!> Hp'".
  iDestruct ("Hp" with "Hp'") as "Hp'".
  iDestruct ("Hhd" with "Hp'") as "Hhd'".
  iApply (wp_strong_mono_delay with "Hhd'"). iIntros (v) "Hqv".
  by iApply "Hq".
Qed.

Lemma hoare_delay_consequence_l {Σ A} (P P': iProp Σ) (Q: A -> iProp Σ)
  (e: delay A)
  : □(P' -∗ P)
  -∗ hoare_delay P e Q 
  -∗ hoare_delay P' e Q.
Proof.
  iIntros "#Hp #Hq".
  iIntros "!> Hp'".
  iDestruct ("Hp" with "Hp'") as "Hp'".
  by iApply "Hq".
Qed.

(*
Rule equivalent for:
Lemma wp_delay_iter {Σ A B} (Φ: B -> iProp Σ)
  (x: A)
  (f: A -> delay (A + B)):
  wp_delay (f x) (case_ (λ x, ▷ wp_delay (iter f x) Φ) Φ) -∗
  wp_delay (iter f x) Φ.

  The issue here is that there is no good point to place the later modality,
  making this rule weaker than the wp equivalent.
*)
Lemma hoare_delay_iter {Σ A B} (P: iProp Σ) (Q: A -> iProp Σ)
  (R: B -> iProp Σ)
  (x: A)
  (f: A -> delay (A + B)):
  hoare_delay P (f x) (case_ (λ x, ▷ Q x) R) 
  -∗ ▷ (∀ a, hoare_delay (Q a) (delaystate.iter f a) R ) 
  -∗ hoare_delay P (delaystate.iter f x) R.
Proof.
  iIntros "#Hhf #Hhiter !> HP".
  iApply wp_delay_iter.
  iApply (wp_strong_mono_delay with "(Hhf HP)").
  iIntros (ab) "Hpost".
  iModIntro.
  destruct ab; simpl.
  - iNext. iApply ("Hhiter" with "Hpost").
  - done.
Qed.

Lemma hoare_delay_ctx {Σ A} (P Q: iProp Σ) `{!Persistent Q}
  (R: A -> iProp Σ)
  (e: delay A):
  hoare_delay (P ∗ Q) e R 
  -∗ (Q -∗ hoare_delay P e R).
Proof.
  iIntros "#Hpq #Hq !> Hp".
  iDestruct "Hq" as "-#Hq". 
  iApply ("Hpq" with "[$]"). 
Qed.

Lemma hoare_delay_ctx' {Σ A} (P Q: iProp Σ) 
  (R: A -> iProp Σ)
  (e: delay A):
  □(Q -∗ hoare_delay P e R)
  -∗ hoare_delay (P ∗ Q) e R. 
Proof.
  iIntros "#Hqhd !> (Hp & Hq)".
  iDestruct ("Hqhd" with "Hq") as "#Hphd".
  by iApply "Hphd".
Qed.

Lemma hoare_lob {Σ A B} (P : B -> iProp Σ) (Q : B -> A -> iProp Σ)
  (e: B -> delay A):
  (∀x: B, hoare_delay (P x ∗ ▷ (∀x : B, hoare_delay (P x) (e x) (Q x))) (e x) (Q x))
  -∗ ∀x: B, hoare_delay (P x) (e x) (Q x).
Proof.
  iIntros "#Hpq".
  iLöb as "IH".
  iIntros (x).
  iDestruct ("Hpq" $! x) as "#Hpq'".
  iIntros "!> Hp".
  iApply "Hpq'". 
  iFrame. iNext. iApply "IH".
Qed.
