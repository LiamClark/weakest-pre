From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import modal delaystate. 
Set Default Proof Using "Type".

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
       | Some (σ', x) => SI σ' ∗ Φ x 
       | None => True
       end)
)%I.
Defined.

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
  wp_delay (f x) (case_ (λ x, ▷ wp_delay (iter f x) Φ) Φ) -∗
  wp_delay (iter f x) Φ.
Proof.
  iIntros "Hwp".
  rewrite iter_unfold.
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros ([a | b]) "H !> /=".
  - by iApply wp_delay_think.
  - by iApply wp_delay_return.
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

Lemma adequacy_delay {A} {Σ} (φ: A -> Prop) (n: nat) (x: A) (prog : delay A):
    (⊢ @wp_delay Σ A prog (λ x, ⌜φ x⌝)) ->
    eval_delay n prog = Some x -> φ x.
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


Lemma wp_return {Σ A ST } {SI: ST -> iProp Σ} (x: A) (Φ: A -> iProp Σ): Φ x -∗ wp SI (mret x) Φ.
Proof.
  iIntros "H" (σ) "HSi".
  simpl.
  iApply wp_delay_return. by iFrame.
Qed.


(*
Lemma wp_delay_fmap {Σ A B} (f: A -> B) (Φ: B -> iProp Σ) (e: delay A): 
  wp_delay e (Φ ∘ f ) -∗ wp_delay (f <$> e) Φ. 
Proof.
  iIntros "Hwp".
  iApply wp_delay_bind.
  iApply (wp_strong_mono_delay with "Hwp").
  iIntros (x) "Hpost !> /=".
  by iApply wp_delay_return.
Qed.
*)
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

Lemma wp_modifyS' {A} Φ (f: ST -> ST * A): 
  (∀σ, SI σ ==∗ let '(σ', x) := f σ in SI σ' ∗ Φ x) -∗ wp SI (modifyS' f) Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost /=".
  destruct (f σ) as [x s'].
  by iApply wp_delay_return.
Qed.

Lemma wp_modifyS Φ f: (∀σ, SI σ ==∗ SI (f σ) ∗ Φ tt) -∗ wp SI (modifyS f) Φ.
Proof.
  iIntros "Hpost". 
  iApply wp_modifyS'. done.
Qed.

Lemma wp_putS Φ σ' : (∀σ, SI σ ==∗ SI σ' ∗ Φ tt) -∗ wp SI (putS σ') Φ.
Proof.
  iIntros "Hpost" (σ) "Hsi".
  iMod ("Hpost" with "Hsi") as "Hpost /=".
  by iApply wp_delay_return.
Qed.
End state_wp.

(*Heap rules *)
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
    let l := fresh (dom (gset nat) σ)
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

  Lemma wp_get n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ wp (state_interp γ) (get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_return. by iApply "Hpost".
  Qed.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ wp (state_interp γ) (put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    iApply wp_modifyS.
    iIntros (σ) "Hsi". 
    iMod (points_to_update with "Hsi Hpt") as "($ & Hup)". 
    by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ wp (state_interp γ) (alloc v) Ψ.
  Proof.
    iIntros "Hpost". iApply wp_modifyS'.
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "($ & Hpt)".
    iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ wp (state_interp γ) (free l) Ψ.
  Proof.
    iIntros "Hpt Hpost". iApply wp_modifyS.
    iIntros (σ) "Hsi".
    iMod (si_free with "Hsi Hpt") as "$".
    done.
  Qed.
End state_wp_gp.


Section state_delay_adequacy.
  Context `{! inG Σ (heapR natO)}.

  (* This allows the use of evaluation info from the outer stack,
    for the inner stack *)
  Lemma eval_state_eval_delay {A} (n: nat) (x: A)
   (prog: state_delay (gmap nat nat) A)
   (st st': gmap nat nat):  
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
  
  (* For adequacy we need the post condition wp uses for wp_delay, to change to a 
    pure assertion.*)
  Definition adapt_post {A} (φ: A -> Prop):
    option (gmap nat nat * A) -> Prop :=
     λ res, match res with
                | Some (_, x) => φ x
                | None => True
                end.

  Lemma adapt_pre {A} {γ} (φ: A -> Prop) (res: option (gmap nat nat * A)):
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
  
  (*For adequacy_delay_state we need an extra update modality compared to the normal
    adequacy statement for the delay monad. 
    It is required in order to allocate the initial heap and get a gname.
  *) 
  Lemma adequacy_state_inbetween {A} (φ: A -> Prop) (n: nat) 
    (x: A) 
    (prog : state_delay (gmap nat nat) A)
    (st st': gmap nat nat):
    (⊢ @wp_delay Σ _(runState prog st) (λ y, ⌜adapt_post φ y⌝)) ->
    (eval_delay n (runState prog st) = Some (Some (st', x)))
    -> (adapt_post φ (Some (st', x))).
  Proof.
    apply adequacy_delay.
  Qed. 
 
  Lemma adequacy_state_delay {A} (φ: A -> Prop) (n: nat) (x: A) 
    (prog : state_delay (gmap nat nat) A)
    (st st': gmap nat nat)
    : (∀γ, ⊢ wp (state_interp γ) prog (λ x, ⌜φ x⌝)) ->
    eval_state_delay' n prog st = Some (st', x) ->
    φ x. 
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

Definition hoare_delay {Σ} {A} (P: iProp Σ) (e: delay A) (Q: A -> iProp Σ): iProp Σ
:= □ (P -∗ wp_delay e Q).

(*{P} e {Q} =  □(P -* wp e {Q}) *)

(*
Lemma wp_delay_think {Σ A}(e: delay A) (Φ: A -> iProp Σ): ▷ wp_delay e Φ -∗ wp_delay (Think e) Φ.
*)
(*
  persistent hypothesis can be moved between the hoare pre condition and the context
  hoare_ctx
*)
Lemma hoare_delay_think {Σ A} (e: delay A) (P: iProp Σ) (Q: A -> iProp Σ):
   hoare_delay P e Q -∗
   hoare_delay (▷ P) (Think e) Q.
Proof.
  iIntros "#Hhoare !>".
  unfold hoare_delay.
  iIntros "Hp".
  iApply wp_delay_think.
  iNext.
  iApply ("Hhoare" with "Hp").
Qed.

(* 
  So this one is true, but is it usable?
*)
Lemma hoare_delay_mret {Σ A} (x: A) (P: iProp Σ) (Q: A -> iProp Σ):
  ⊢ @hoare_delay Σ A True (Answer x) (λ w, ⌜w = x⌝).
Proof.
  unfold hoare_delay.
  iIntros "!> _".
  by iApply wp_delay_return.
Qed.

Lemma hoare_delay_mret' {Σ A} (x: A) (Q: iProp Σ) (P: A -> iProp Σ):
  □(Q -∗ P x) -∗
  hoare_delay Q (Answer x) P.
Proof.
  unfold hoare_delay.
  iIntros "#Hwand !> Hp".
  iApply wp_delay_return. 
  by iApply "Hwand".
Qed.

Lemma hoare_delay_consequence {Σ A} (P P': iProp Σ) (Q Q': A -> iProp Σ)
  (e: delay A)
  : □(P' -∗ P) -∗ □(∀x, Q x -∗ Q' x) -∗
  hoare_delay P e Q -∗
  hoare_delay P' e Q'.
Proof.
  iIntros "#Hp #Hq #Hhd".
  iIntros "!> HP'".
  iDestruct "Hhd"


Qed.


(* not provable due to the persistence modality?*)
(* Lemma hoare_delay_mret'' {Σ A} (x: A) (P: A -> iProp Σ):
  P x -∗ @hoare_delay Σ A (True) (Answer x) P.
Proof.
  unfold hoare_delay.
  iIntros "Hp !>".
  by iApply wp_delay_return.
Qed. *)


(*
Lemma wp_delay_iter {Σ A B} (Φ: B -> iProp Σ)
  (x: A)
  (f: A -> delay (A + B)):
  wp_delay (f x) (case_ (λ x, ▷ wp_delay (iter f x) Φ) Φ) -∗
  wp_delay (iter f x) Φ.
*)

Lemma hoare_delay_iter {Σ A B} (P: iProp Σ) (Q: A -> iProp Σ)
  (R: B -> iProp Σ)
  (x: A)
  (f: A -> delay (A + B)):
  hoare_delay P (f x) (case_ (λ x, ▷ Q x) R) -∗
  (∀ a, hoare_delay (Q a) (delaystate.iter f a) R ) -∗
  hoare_delay P (delaystate.iter f x) R.
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
  hoare_delay (P ∗ Q) e R -∗
  (Q -∗ hoare_delay P e R).
Proof.
  iIntros "#Hpq #Hq !> Hp".
  iDestruct "Hq" as "-#Hq". 
  iApply ("Hpq" with "[$]"). 
Qed.

Lemma hoare_lob {Σ A B} (P : B -> iProp Σ) (Q : B -> A -> iProp Σ)
  (e: B -> delay A):
  (∀x: B, hoare_delay (P x ∗ ▷ (∀x : B, hoare_delay (P x) (e x) (Q x))) (e x) (Q x)) -∗
  ∀x: B, hoare_delay (P x) (e x) (Q x).
Proof.
  iIntros "#Hpq".
  iLöb as "IH".
  iIntros (x).
  iDestruct ("Hpq" $! x) as "#Hpq'".
  iIntros "!> Hp".
  iApply "Hpq'". 
  iFrame. iNext. iApply "IH".
Qed.
