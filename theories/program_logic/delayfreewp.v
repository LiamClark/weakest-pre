From stdpp Require Import base gmap.
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From shiris.program_logic Require Import delayfree evaluation.
Set Default Proof Using "Type".

(* Curry the value R so it can be changed by the dependent pattern match on c *)
Definition command_predicate {V R} (c: envE V R) (σ σ': gmap loc V): R -> Prop.
refine (match c with
        |GetE l  => λ v, σ !! l = Some v /\ σ' = σ 
        |PutE l v' => λ _, is_Some (σ !! l) /\ σ' = <[l := v']> σ
        |AllocE v' => λ l, l = fresh_loc σ /\ σ' = <[l := v']> σ
        |FreeE l => λ _, is_Some (σ !! l) /\ σ' = delete l σ
        end
).
Defined.

Definition wp_pre {Σ} {V} (SI: gmap loc V -> iProp Σ)
     (go: discrete_funO (λ R, expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ)):
     discrete_funO (λ R, expr V R -d> (R -d> iPropO Σ) -d> iPropO Σ).
refine(λ R e Φ,
        match e with
        |Answer x  => |==> Φ x 
        |Think e'  => |==> ▷ go R e' Φ
        |Fork e' k => |==> ▷ (go R k Φ ∗ go unit e' (λ _, True))
        (* make wp less determinstic  *)
        (* |Vis c k   => ∀σ, SI σ ==∗ ▷ |==> (∃σ' v, ⌜command_predicate c σ σ' v⌝) ∗
            ∀ σ' v, ⌜command_predicate c σ σ' v⌝ -∗ SI σ' ∗ (go R (k v)) Φ *)
        |Vis c k   => ∀σ, SI σ ==∗ ▷ |==> ∃σ' v, ⌜command_predicate c σ σ' v⌝ ∗ SI σ' ∗ (go R (k v)) Φ
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

Definition wp_thread {Σ} {V R} (SI: gmap nat V -> iProp Σ) (t: thread V R) 
: (R -> iProp Σ) -> iProp Σ.
refine (
  match t with
  | Main e => wp SI e
  | Forked e => λ _,  wp SI e (λ _, True)
  end
)%I.
Defined.

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
  unfold wp_pre. iModIntro.
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
    by destruct (f r); iMod "H".
  - iEval (rewrite wp_unfold /=) in "H".
    iMod "H". iIntros "!> !>". iApply "IH". done.
  - iEval (rewrite wp_unfold /=) in "H".
     iMod "H" as "(H & $)". iIntros "!> !>". 
    iApply "IH". done.
  - iIntros (σ)  "HSi".
    iEval (rewrite wp_unfold /=) in "H".
    iMod ("H" $! σ with "HSi") as "H". iModIntro.
    iNext.
    iMod ("H") as (σ' v) "H". iModIntro.
    iExists σ', v.
    iDestruct "H" as  "($ & $ & Hwp)". 
    iApply "IH". done.
Qed.

Lemma wp_strong_mono {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ) (e: expr V R)
  (Φ Ψ: R -> iProp Σ)
  : wp SI e Φ -∗ (∀ v, Φ v ==∗ Ψ v) -∗ wp SI e Ψ.
Proof.
  iLöb as "IH" forall (e).
  rewrite wp_unfold.
  rewrite wp_unfold.
  iIntros "Hwp H".
  destruct e; simpl.
  - iMod ("H" with "Hwp").
    done.
  - iMod "Hwp". iIntros "!> !>". 
    iApply ("IH" $! e with "Hwp H").
  - iMod "Hwp". iIntros "!> !>". 
    iDestruct "Hwp" as "(Hwpe2 & $)".
    iApply ("IH" $! e2 with "Hwpe2 H").
  - iIntros (σ) "HSi".
    iMod ("Hwp" with "HSi") as "Hwp".
    iIntros "!> !>".
    iMod "Hwp". iModIntro.
    iDestruct "Hwp" as (σ' v) "(Hcom & HSi & Hwp)".
    iExists σ', v. iFrame. 
    iApply ("IH"  with "Hwp H"). 
Qed.

Lemma wp_mono {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
   (e: expr V R) (Φ Ψ: R -> iProp Σ)
   :wp SI e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ wp SI e Ψ.
Proof.
  iIntros "Hwp H".
  iApply (wp_strong_mono with "Hwp").
  - iIntros (v) "Hphi". 
    iModIntro.
    iApply ("H" with "Hphi").
Qed.

Lemma wp_fmap {Σ} {V R B: Type} (SI: gmap nat V -> iProp Σ) 
  (f: R -> B) (Φ: B -> iProp Σ) (e: expr V R)
  : wp SI e (Φ ∘ f ) -∗ wp SI (f <$> e) Φ. 
Proof.
  iIntros "Hwp".
  iApply wp_bind.
  iApply (wp_mono with "Hwp").
  iIntros (x) "Hpost /=".
  iApply (wp_return with "Hpost").
Qed.

Lemma wp_iter {Σ} {V R B: Type} (SI: gmap nat V -> iProp Σ) (Φ: B -> iProp Σ)
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

Lemma bupd_wp {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
 (e: expr V R) (Φ : R -> iProp Σ)
 : (|==> wp SI e Φ) ⊢ wp SI e Φ.
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

Lemma wp_bupd {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
 (e: expr V R) (Φ : R -> iProp Σ) 
 : wp SI e (λ v, |==> Φ v) ⊢ wp SI e Φ.
Proof.
  iIntros "Hwp".
  iApply (wp_strong_mono with "Hwp").
  auto.
Qed.

Lemma wp_think' {Σ} {V R: Type} (SI: gmap nat V -> iProp Σ)
   (e: expr V R) (Φ: R -> iProp Σ): wp SI (Think e) Φ ==∗ ▷ wp SI e Φ .
Proof.
  iIntros "Hwp".
  rewrite wp_unfold. 
  unfold wp_pre.
  iMod "Hwp". 
  done.
Qed.

(* Lemma adequacy_state_delay {A} (φ: A -> Prop) (n: nat) (x: A)  *)
  (* (prog : state_delay (gmap nat nat) A) *)
  (* (st st': gmap nat nat) *)
  (* : (∀γ, ⊢ wp (state_interp γ) prog (λ x, ⌜φ x⌝)) -> *)
  (* eval_state_delay' n prog st = Some (st', x) -> *)
  (* φ x.  *)
(* maak thread indexing een progerr zodat adequacy dat uitsluit *)
(*Heap rules *)
Definition heapR (A: ofeT): cmraT := authR (gmapUR nat (exclR A)).

Lemma fresh_none (σ: gmap nat nat): 
 σ !! fresh_loc σ = None.
Proof.
  apply (not_elem_of_dom (D := gset nat)).
  unfold fresh_loc.
  apply is_fresh.
Qed.

Section heap_wp.
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

  Lemma wp_get n v (Ψ: nat -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v -∗ Ψ v) -∗ wp (state_interp γ) (delayfree.get n) Ψ.
  Proof.
    iIntros "Hpt Hpost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iIntros "!> !> !>". iExists σ, v. simpl.
    iDestruct (si_points_to_agree with "Hsi Hpt") as %H. 
    iSplit; try done.
    iFrame. 
    iApply wp_return. by iApply "Hpost".
  Qed.

  Lemma wp_put n v v' (Ψ: unit -> iProp Σ) :
    points_to γ n v -∗ (points_to γ n v' -∗ Ψ tt) -∗ wp (state_interp γ) (delayfree.put n v') Ψ.
  Proof.
    iIntros "Hpt Hpost".
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi". 
    iDestruct (si_points_to_agree with "Hsi Hpt") as %Hsome.
    (* one update here*)
    iMod (points_to_update with "Hsi Hpt") as "(Hsi & Hpt)". 
    iIntros "!> !> !>". iExists (<[n := v']> σ), tt. simpl.
    iSplit.
    - iPureIntro. split.
      + apply (mk_is_Some _ _ Hsome).
      + done.
    - iFrame. iApply wp_return.
      by iApply "Hpost".
  Qed. 

  Lemma wp_alloc v (Ψ: nat -> iProp Σ):
    (∀l, points_to γ l v -∗ Ψ l) -∗ wp (state_interp γ) (delayfree.alloc v) Ψ.
  Proof.
    iIntros "Hpost". 
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iMod (si_alloc with "Hsi") as "(Hsi & Hpt)".
    iIntros "!> !> !>". iExists (<[fresh_loc σ := v]> σ), (fresh_loc σ). simpl.
    iSplit.
    - iPureIntro. split.
      + done.
      + done.
    - iFrame. iApply wp_return.
      iApply ("Hpost" with "Hpt").
  Qed.

  Lemma wp_free v l (Ψ: unit -> iProp Σ):
    points_to γ l v -∗ Ψ tt -∗ wp (state_interp γ) (delayfree.free l) Ψ.
  Proof.
    iIntros "Hpt Hpost". 
    rewrite wp_unfold. unfold wp_pre.
    iIntros (σ) "Hsi".
    iDestruct (si_points_to_agree with "Hsi Hpt") as %Hsome.
    iMod (si_free with "Hsi Hpt") as "Hsi".
    iIntros "!> !> !>". iExists (delete l σ), tt. simpl.
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
 Context (γ: gname).

(* Now come the rule that needs the points to connective in their weakest pre definition.
    We therefore first define this in terms of the Authorative camera.
  *)



(*


Definition step_expr {V R A} (e: expr V A): state V R (expr V A) :=
Definition step_thread {V R} (t: thread V R) : state V R (thread V R) :=
Definition single_step_thread {V R} (s: scheduler V R): state V R (scheduler V R ) :=
Fixpoint eval_threaded {V R} (n: nat) (s : scheduler V R) {struct n}: state V R R :=
*)

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
Lemma step_expr_adequacy {R A} (Φ: R -> iProp Σ) (Ψ: A -> iProp Σ) 
  (h: heap nat)
  (ts: list (thread nat R))
  (e: expr nat A)
  : wp (state_interp γ) e Ψ 
  -∗ state_interp γ h
  ==∗ 
   ▷ |==> match runState (step_expr e) h ts with
     | Here (e', h', ts') => ∃ts'', ⌜ts' = ts ++ ts''⌝ 
                             ∗ wp (state_interp γ) e' Ψ ∗ state_interp γ h'
                             ∗ [∗ list] t ∈ ts'', wp_thread (state_interp γ) t Φ
     | ProgErr => False
     | EvalErr => True
     end.
Proof.
  iIntros "Hwp Hsi".
  destruct e; simpl.
  - iIntros "!> !> !>".
    iExists []. rewrite right_id_L.
    iFrame. auto.
  - 
    iMod (wp_think' with "Hwp") as "Hwp". iIntros "!> !> !>".
    iExists []. rewrite right_id_L.
    iFrame. auto.
  -
   rewrite wp_unfold. unfold wp_pre.
   simpl.
   iMod "Hwp" as "(Hwpe2 & Hwpe1)".
   iModIntro. iNext. iFrame. simpl.
   iModIntro. 
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
 ok next up second dude. What up here?
 we still have two post conditions, but they operate on the same type now.
 Ψ is for the thread we are stepping. Ah so this is the above lifted to a thread.
 Φ is still the post condition for the main thread.
*)
Lemma step_thread_adequacy {R} (Φ Ψ: R -> iProp Σ) 
  (h: heap nat)
  (ts: list (thread nat R))
  (ct: thread nat R)
  : wp_thread (state_interp γ) ct Ψ 
  -∗ state_interp γ h 
  ==∗ 
  ▷ |==> 
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
    iMod (step_expr_adequacy _ _ _ ts  with "Hwp Hsi") as "Hexpr".
    iIntros "!> !>". iMod "Hexpr". iModIntro.
    simpl. 
    by destruct (runState (step_expr e) h ts) as [[[e' σ'] ts'] | ? | baz].
  -
    iMod (step_expr_adequacy _ _ _ ts with "Hwp Hsi") as "Hexpr".
    iIntros "!> !>". iMod "Hexpr". iModIntro.
    simpl. 
    by destruct (runState (step_expr e) h ts) as [[[e' σ'] ts'] | ? | ?].
Qed.

Lemma mod_lookup_some {A} (l: list A) (i: nat):
 l ≠ [] -> is_Some (l !! (i mod (length l))).
Proof.
  intro Hnil.
  apply lookup_lt_is_Some_2. 
  apply Nat.mod_upper_bound.
  by destruct l.
Qed.

(* OK third one up, now there is just one post condiiton left.
    Φ for the main thread. All the other threads namely have the trivial
    post condition
*)
Lemma scheduled_adequacy {R} (Φ: R -> iProp Σ) 
  (h: heap nat)
  (s: scheduler nat R)
  (ts: list (thread nat R))
  : ts ≠ [] -> 
  state_interp γ h 
  -∗ ([∗ list] t ∈ ts, wp_thread (state_interp γ) t Φ) 
  ==∗ 
  ▷ |==>
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
  iMod (step_thread_adequacy _ _ _ ts with "Hwpct HSi" ) as "H".
  iIntros "!> !>".
  iMod "H". iModIntro.
  rewrite Hsome /=.  
  destruct (runState _ h ts) as [[[t' σ'] ts'] | ? | baz]; try done; simpl.
  iDestruct "H" as (ts'' ->) "(Hwpt' & $ & Hbigop)".
  iSplit. 
  - iPureIntro. rewrite insert_length app_length. lia. 
  - rewrite insert_app_l; last first. 
    { apply Nat.mod_upper_bound. destruct ts; done. }
   iFrame.
   by iApply "Hrestore".
Qed.

Lemma fuel_adequacy {R} (Φ: R -> iProp Σ) (n: nat)
  (h: heap nat)
  (s: scheduler nat R)
  (ts: list (thread nat R))
  : ts ≠ [] -> 
  state_interp γ h
  -∗ ([∗ list] t ∈ ts, wp_thread (state_interp γ) t Φ) 
  -∗ Nat.iter n (λ P : iPropI Σ, |==> ▷ P) $ |==>
  match runState (eval_threaded n s) h ts with
  | Here (x, h', ts') => ⌜length ts <= length ts'⌝ ∗ Φ x ∗ state_interp γ h'
                          ∗ [∗ list] t ∈ ts', wp_thread (state_interp γ) t Φ
  | ProgErr => False
  | EvalErr => True
  end.
Proof.
  iIntros (Hnil) "Hsi Hbigop".
  iInduction n as [|n'] "IH" forall (s).
  - done.
  - iPoseProof (scheduled_adequacy with "Hsi Hbigop" ) as "H"; try done.
    iEval (unfold eval_threaded).
    rewrite run_bind_dist.
    (* destruct (runState _  h ts) as [[[s' σ'] ts'] | ? | ?]; try done. *)
    destruct (runState (single_step_thread s)  h ts) as [[[s' σ'] ts'] | ? | ?]; try done.
    rewrite run_bind_dist. 
    simpl runState at 3. (* a less fragile way to do this?*)
    iEval (cbn). iEval (fold (eval_threaded (V := nat) (R := R))).
    +
Admitted.


Lemma adequacy {R} (φ: R -> Prop) (n: nat) 
  (SI: gmap nat nat -> iProp Σ)
  (s: scheduler nat R)
  (e: expr nat R)
  (st st': heap nat)
  : (∀ γ, ⊢ wp (state_interp γ) e (λ x, ⌜φ x⌝)) ->
  match run_program n s e with
  | Here x => φ x
  | ProgErr => False
  | EvalErr => True
  end.
  Proof.
  Admitted.

(* 




  adequacy statement : voor alle schedelures alle initieele heaps.
  - Als het interpret naar een value in een aantal stappen
  - En er is een wp voor die expressie
  - Dan krijgen we die pure post conditie er uit.
  - En het programma loopt af.
  - 
*)