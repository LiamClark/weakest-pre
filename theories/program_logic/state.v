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


Definition modifyS' {A ST} (f: ST -> A * ST): state ST A :=
  State $ λ st, Some $ f st.

Section state_op.
   Context {ST A: Type}.

   Definition getS: state ST ST :=
     State $ λ st, Some (st, st).
  
   Definition putS (x: ST): state ST unit :=
     State $ λ st, Some (tt, x).

   Definition modifyS (f: ST -> ST): state ST () :=
     modifyS' $ λ st, (tt, f st).

   Definition fail: state ST A :=
     State $ λ st, None.

    Definition ret_fail (m: option A): state ST A := 
     match m with
     | Some x => mret x
     | None => fail
     end.
End state_op.


Section gmap_state.
  Definition get {A} (n: nat): state (gmap nat A) A :=
    getS ≫= λ st, ret_fail $ lookup n st.

  Definition put {A} (n: nat) (x : A) : state (gmap nat A) unit :=
    modifyS <[n := x]>.

  Definition alloc {A} (v: A) : state (gmap nat A) nat :=
    modifyS'$ λ st, 
                let fresh := fresh $ dom (gset nat) st
                in (fresh, <[fresh := v]> st). 

  Definition free {A} (n: nat): state (gmap nat A) unit :=
    modifyS $ delete n.
End gmap_state.