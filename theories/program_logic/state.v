From stdpp Require Import base gmap fin_sets fin_map_dom.

Record state (ST A: Type): Type := 
    State {
       runState: ST -> option (A * ST)
    }.

Arguments State {_ _} _.
Arguments runState {_ _} _.

Instance fmap_state ST: FMap (state ST) :=
  λ A B f fa, State $ λ st, (λ '(a, b), (f a , b)) <$> (runState fa st).

Instance mret_state ST: MRet (state ST) := λ A a, State $ λ s, Some (a, s).

Instance mbind_state ST: MBind (state ST) :=
  λ (A: Type) (B: Type) (f: A -> state ST B)
    (ma: state ST A), State $
                    λ st, match runState ma st with
                          | Some (x, st') => runState (f x) st'
                          | None => None
                          end.


Definition getS {ST} : state ST ST :=
  State $ λ st, Some (st, st).

Definition putS {ST} (x: ST): state ST () :=
  State $ λ st, Some (tt, x).

Definition fail {ST A}: state ST A :=
  State $ λ st, None.

Definition ret_fail {ST A} (m: option A): state ST A := 
  match m with
  | Some x => mret x
  | None => fail
  end.

Section gmap_state.
  Definition modifyS' {A} (n: nat) 
    (f: gmap nat A -> gmap nat A): state (gmap nat A) () :=
    State $ λ st, if decide (is_Some (st !! n)) then Some (tt, f st) else None.

  Definition get {A} (n: nat): state (gmap nat A) A :=
    getS ≫= λ st, ret_fail $ lookup n st.

  Definition put {A} (n: nat) (x : A) : state (gmap nat A) unit :=
    modifyS' n  <[n := x]>.

  Definition fresh_adress {A} (σ: gmap nat A): nat := fresh $ dom (gset nat) σ.

  Definition alloc {A} (v: A) : state (gmap nat A) nat :=
    State $ λ st, let freshn := fresh_adress st
                  in Some (freshn, <[freshn := v]> st).

  Definition free {A} (n: nat): state (gmap nat A) unit :=
   modifyS' n (delete n).
End gmap_state.