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
       | Some (σ', x) => SI σ' ∗ Φ x 
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

(* Lemma wp_delay_iter {Σ A B} (Φ: B -> iProp Σ)
  (x: A)
  (inv: A -> iProp Σ)
  (f: A -> delay (A + B))
  : inv x -∗
    (*if we loop again we need to re-establish the wp *)
   (∀y, ⌜f x = Answer (inl y)⌝ -∗ inv x -∗ wp_delay (iter f y) Φ) -∗ 
   (∀z, ⌜f x = Answer (inr z)⌝ -∗ inv x -∗ Φ z) -∗
   wp_delay (iter f x) Φ.
Proof.
  iIntros "Hinv Hinvest HPost".
  rewrite wp_delay_unfold /=. 
  destruct (f x) as [a | t] eqn: E.
  - admit.
  -  iEval (unfold wp_delay_pre).
iEval (unfold iter).
    (*  *) 
   iModIntro. iNext.
   (* iDestruct ("IH" with "Hinv Hinvest HPost") as "IH'". *)

Qed. *)

 CoFixpoint f (n: nat) : delay (nat + nat) :=
   Think $ f n.

(*So how does this baby work? The idea is to adapt the 
  wp rules for while loops to iter.
  from: https://en.wikipedia.org/wiki/Predicate_transformer_semantics#While_loop
  Normally for a loops a loop invariant is established
  (here we can have that be supplied hopefully?)
  The loop invariant should establish the weakestpre for the loop,
  again for the next iteration if f terminates in an inl

  The loop invariant given the fact that f terminates in an inr
  should establish the post condition.

  The problem is that I can't properly establish whether f x gives
  an inl or an inr. The way I have it set up now requires it to
  be an answer immeadieately, but that's not the only way.
  For example:

  Definition f (n: nat) : delay (nat + nat) :=
    Think $ Answer $ inr n.
  
  This clearly terminates to a inr but that's not usable with our loop invariant.
  So I need to account for stacks of thinks that evantually give an inl or an inr
  in those lemmas.
  That together with this example:

  CoFixpoint diverge (n: nat) : delay (nat + nat) :=
    Think $ f n.

  Means that the condition could just diverge. It seems like I need a big step
  evaluation of the condition and it's simply not available to me?
 *)
Lemma wp_delay_iter {Σ A B} (Φ: B -> iProp Σ)
  (x: A)
  (inv: A -> iProp Σ)
  (f: A -> delay (A + B))
  : inv x -∗
    (*if we loop again we need to re-establish the wp *)
   (∀y, ⌜f x = Answer (inl y)⌝ -∗ inv x -∗ wp_delay (iter f y) Φ) -∗ 
   (∀z, ⌜f x = Answer (inr z)⌝ -∗ inv x -∗ Φ z) -∗
   wp_delay (iter f x) Φ.
Proof.
  iIntros "Hinv Hinvest HPost".
  iLöb as "IH". (* forall() *)
  rewrite wp_delay_unfold /=. 
  iEval (unfold iter). iEval (unfold wp_delay_pre).
  destruct (f x) as [a | t] eqn: E.
  - simpl. destruct a.
    +
     iAssert (⌜Answer (inl a) = Answer (inl a)⌝%I) as "Hl". done.
     iApply ("Hinvest" $! a with "Hl Hinv"). 
    +
     iAssert (⌜Answer (inr b) = Answer (inr b)⌝%I) as "Hd". done.
     iApply ("HPost" $! b with "Hd Hinv").
  -  
   (*  *) 
   iModIntro. iNext.
   (* iDestruct ("IH" with "Hinv Hinvest HPost") as "IH'". *)

Qed.


Lemma wp_state_return {Σ A ST } {SI: ST -> iProp Σ} (x: A) (Φ: A -> iProp Σ): Φ x -∗ wp SI (mret x) Φ.
Proof.
  iIntros "H" (σ) "HSi".
  simpl.
  iApply wp_delay_return. by iFrame.
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
  - iIntros "(HSi & Hwp)".
    unfold wp. iApply ("Hwp" $! (s) with "HSi").
  - iIntros "_ !>".
    by iApply wp_delay_return.
Qed.

Section state_wp.
  Context  {Σ} {ST} (SI: ST -> iProp Σ).

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
Definition heapR (A: ofeT): cmraT := authR (gmapUR nat (exclR A)).

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
    pose (proj1 (@auth_both_valid cmr _ (lift_excl σ) ({[n := Excl v]}))).
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
    iApply wp_state_bind. iApply wp_getS.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %->.
    iIntros "{$Hsi} !>".
    iApply wp_state_return. by iApply "Hpost".
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


  
  (*
    iter: (A -> delay_state (A + B))  -> A -> delay_state B
   *)
  Lemma wp_state_delay_iter A B Φ 
    (x: A)
    (f: A -> state_delay (gmap nat nat) (A + B))
    : True -∗ wp (state_interp γ) (iter_state_delay f x) Φ.
End state_wp_gp.

(* 
  iter combinators. ask robbert for the rules for the looping combinators in Iris.
  Programs.
*)

