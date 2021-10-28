From shiris.program_logic Require Import delaystate.
From stdpp Require Import base list.

Definition pool (A: Type) := list $ delay A.

Definition step {A} (ma: delay A): delay A :=
    match ma with
    | Answer x => Answer x
    | Think m' => m'
    end.

Definition final {A} (m: delay A): option A :=
    match m with
    | Answer x => Some x
    | Think m' => None 
    end.

(* Use step on a thread here and put the list back together
   Won't be bothered to shuffle the list around, needs a non empty list
   or more option monad operations.
*)
Definition step_on {A} (threads: pool A): pool A.
Admitted.


Fixpoint eval {A} (threads: pool A) (n: nat) {struct n}: option A :=
  match n with
          |O => head threads ≫= final
          |S n' => eval (step_on threads) n'
  end.