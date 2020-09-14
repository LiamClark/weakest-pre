From stdpp Require Import base gmap fin_sets fin_map_dom.

Record state (ST A: Type): Type := State {
                                      runState: ST -> option (A * ST)
                                     }.


Arguments State {_ _} _.
Arguments runState {_ _} _.
Instance mret_state ST : MRet (state ST) := λ A a, State $ λ s, Some (a, s).

Instance mbind_state ST: MBind (state ST) :=
  λ _ _ f ma, State $
                    λ st, match (runState ma) st with
                          | Some (x, st') => runState (f x) st'
                          | None => None
                          end.

Section gmap_state.
  Variable ST A: Type.


  Print base.lookup.
  Definition get (n: nat): state (gmap nat A) A :=
    State $ λ (st: gmap nat A), (λ x, (x, st)) <$> lookup n st.

  Definition put (n: nat) (x : ST) : state (gmap nat ST) unit := State $ λ st, Some (tt, <[n:= x]> st).

  Definition alloc (v: ST) : state (gmap nat ST) nat :=
    State $ λ st, let fresh := fresh $ dom (gset nat) st in
                  Some (fresh, <[fresh:=v]> st).

  Definition free (n: nat): state (gmap nat ST) unit :=
    State $ λ st, Some (tt, delete n st).

End gmap_state.


  Lemma fresh_none (σ: gmap nat nat): 
    let l := fresh (dom (gset nat) σ)
    in σ !! l = None.
  Proof.
    apply (not_elem_of_dom _ _).
    apply is_fresh.
    Grab Existential Variables.
  Qed.