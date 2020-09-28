From stdpp Require Import base gmap fin_sets fin_map_dom.

Record state (ST A: Type): Type := State {
                                      runState: ST -> option (A * ST)
                                     }.


Arguments State {_ _} _.
Arguments runState {_ _} _.

Instance fmap_state: FMap (state ST)  :=
  λ ST A B f fa, State $ λ st, (λ '(a, b), (f a , b)) <$> (runState fa st).

Instance mret_state ST : MRet (state ST) := λ A a, State $ λ s, Some (a, s).

Instance mbind_state ST: MBind (state ST) :=
  λ _ _ f ma, State $
                    λ st, match (runState ma) st with
                          | Some (x, st') => runState (f x) st'
                          | None => None
                          end.

Section state_op.
   Context {ST A: Type}.

   Definition getS: state ST ST :=
     State $ λ st, Some (st, st).
  
   Definition putS (x: ST): state ST unit :=
     State $ λ st, Some (tt, x).

   Definition fail: state ST A :=
     State $ λ st, None.
End state_op.


Section gmap_state.
  Definition get {A} (n: nat): state (gmap nat A) A :=
    State $ λ (st: gmap nat A), (λ x, (x, st)) <$> lookup n st.

  Definition ret_fail {S A} (m: option A): state S A := 
    match m with
    | Some x => mret x
    | None => fail
    end.

  Definition get' {A} (n: nat): state (gmap nat A) A :=
    getS ≫= λ st, ret_fail $ lookup n st.

  Definition put {A} (n: nat) (x : A) : state (gmap nat A) unit :=
    State $ λ st, Some (tt, <[n := x]> st).

  Definition put' {A} (n: nat) (x : A) : state (gmap nat A) unit :=
    getS ≫= λ st, putS $ <[n := x]> st.

  Definition alloc {A} (v: A) : state (gmap nat A) nat :=
    getS ≫= λ st, 
                let fresh := fresh $ dom (gset nat) st
                in putS $ <[fresh := v]> st ;; mret fresh.

  Definition free {A} (n: nat): state (gmap nat A) unit :=
    getS ≫= λ st, putS $ delete n st.

End gmap_state.