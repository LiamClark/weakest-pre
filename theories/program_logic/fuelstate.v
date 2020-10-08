From stdpp Require Import base option gmap.

Record fuelstate (ST A: Type): Type := FuelState {
        runFuelState :  ST -> nat -> option (A * ST)
}.

Arguments FuelState {_ _} _.
Arguments runFuelState {_ _} _.

Instance mret_fuel_state ST: MRet (fuelstate ST) :=
    λ A a, FuelState $ λ s n, Some (a, s).

Instance fmap_fuel_state ST : FMap (fuelstate ST) :=
    λ A B f fa, FuelState $ λ s n, (λ '(x, s), (f x, s)) <$> (runFuelState fa s n).

Instance mbind_fuel_state ST : MBind (fuelstate ST) :=
    λ A B f ma, FuelState $ λ s n, 
        match runFuelState ma s n with 
        | Some (x, s') => runFuelState (f x) s' n 
        | None => None
        end.

Definition get {ST}: fuelstate ST ST :=
    FuelState $ λ s _, Some (s, s).

Definition put {ST} (x: ST): fuelstate ST unit :=
    FuelState $ λ s _, Some (tt, x).

Definition fail {ST A}: fuelstate ST A :=
    FuelState $ λ st n, None.

Definition ret_fail {ST A} (m: option A): fuelstate ST A :=
    match m with
    | Some x => mret x
    | None => fail
    end.

Definition get' {A} (n: nat): fuelstate (gmap nat A) A :=
  get ≫= λ st, ret_fail $ lookup n st.

Definition put' {A} (n: nat) (x : A) : fuelstate (gmap nat A) unit :=
  get ≫= λ st, put $ <[n := x]> st.

Definition alloc {A} (v: A) : fuelstate (gmap nat A) nat :=
  get ≫= λ st, 
              let fresh := fresh $ dom (gset nat) st
              in put $ <[fresh := v]> st ;; mret fresh.

Definition free {A} (n: nat): fuelstate (gmap nat A) unit :=
  get ≫= λ st, put $ delete n st.

Fixpoint Fix' {A B ST} (f: (A -> fuelstate ST B) -> (A -> fuelstate ST B)) (n: nat) (x: A) {struct n}: fuelstate ST B :=
  match n with
  | O => fail
  | S n' => f (Fix' f n') x
  end.

Definition Fix {A B ST} (f: (A -> fuelstate ST B) -> (A -> fuelstate ST B)): A -> fuelstate ST B :=
    λ x, FuelState $ λ s n, runFuelState (Fix' f n x) s n.

Definition looper: bool -> fuelstate unit unit :=
    Fix (λ looper (b: bool), if b then mret tt else looper b).

Definition setupGumball: fuelstate (gmap nat nat) (nat * nat) :=
    p ← alloc 3 ;
    y ← alloc 0 ;
    mret (p, y).

Definition inc (loc: nat): fuelstate (gmap nat nat) nat :=
    p ← get' loc ;
    put' loc (S p) ;; mret (S p).


(* Shit this is actually structurally recursive *)
Definition gumball_rec (ploc: nat) (gloc: nat): nat -> fuelstate (gmap nat nat) nat :=
    Fix $ λ rec (money: nat),
                match money with
                | S n => p ← inc ploc ;
                          if Nat.eqb p 3 then inc gloc ;; put' ploc 0 ;; rec n 
                          else rec n 
                | O => get' gloc
                end. 

Definition gumball (money: nat): fuelstate (gmap nat nat) nat :=
    '(ploc, gloc) ← setupGumball ;
    gumball_rec ploc gloc money.


(* this baby broken*)
Lemma test_gumball s: exists n, (runFuelState (gumball 13) ∅ n) = Some (4, s).
Proof.
    exists 200. unfold gumball. simpl.
    reflexivity.
Qed.       

Lemma test_looper: exists n, (runFuelState (looper true) tt n) = Some (tt, tt).
Proof.
    exists 1.
    reflexivity.
Qed.
    
    