From stdpp Require Import base option.

Record fuel (A: Type): Type := Fuel {
        runFuel : nat -> option A
}.

Arguments Fuel {_}.
Arguments runFuel {_}.

Instance mret_fuel: MRet (fuel) := λ _ x, Fuel $ λ n, Some x.

Instance fmap_fuel : FMap (fuel) :=
    λ A B f fa, Fuel $ λ n, f <$> runFuel fa n.

Definition fail {A} : fuel A := Fuel $ λ _, None.

Instance mbind_fuel: MBind (fuel) :=
    λ A B f ma, Fuel $ λ n, 
        match runFuel ma n with
        | Some x => runFuel (f x) n
        | None => None
        end.

(*A kleisli arrow from a -> fuel B that should be fixed according to f*)
Fixpoint Fix' {A B} (f: (A -> fuel B) -> (A -> fuel B)) (n: nat) (x: A) {struct n}: fuel B :=
    match n with
    | O => fail
    | S n' => f (Fix' f n') x
    end.

Definition Fix {A B} (f: (A -> fuel B) -> (A -> fuel B)): A -> fuel B :=
    λ x, Fuel $ λ n, runFuel (Fix' f n x) n.

Definition looper: bool -> fuel unit :=
    Fix (λ looper (b: bool ), if b then mret tt else looper b).

Lemma test_looper: exists n, (runFuel (looper true) n) = Some tt.
Proof.
    exists 1.
    reflexivity.
Qed.
