From stdpp Require Import base gmap list.
From shiris.program_logic Require Import delayfree.

(* Ask casper how to credit his blog post*)

Definition heap V := gmap nat V.

(* How am I going to differentiate between the main thread that returns a value,
   And the spawned threads that do not. 
 *)
Variant thread (V A: Type): Type :=
| Main (e: expr V A)
| Forked (e: expr V ()).

Arguments Main {_ _}.
Arguments Forked {_ _}.

Instance fmap_thread {V}: FMap (thread V) :=
  λ A B f fa, match fa with
              | Main e' => Main $ f <$> e'
              | Forked e => Forked e
  end.

Definition is_main {V A} (t: thread V A): option (expr V A) :=
  match t with
  | Main e => Some e
  | Forked _ => None
  end.

Variant error (A: Type): Type :=
| Here (a: A)
| ProgErr 
| EvalErr.

Arguments Here {_}.
Arguments ProgErr {_}.
Arguments EvalErr {_}.

Instance error_fmap: FMap error := 
  λ A B f fa,
    match fa with
    | Here a  => Here $ f a
    | ProgErr => ProgErr
    | EvalErr => EvalErr
    end.

Instance error_mret: MRet error :=
  λ A x, Here x.

Instance error_mbind: MBind error :=
  λ A B f ma, 
    match ma with
    | Here a  => f a
    | ProgErr => ProgErr
    | EvalErr => EvalErr
    end.

Definition fail_prog {A}: error A := ProgErr.
Definition fail_eval {A}: error A := EvalErr.

Definition into_eval {A} (x: option A) :=
  match x with
  | Some x => Here x
  | None   => EvalErr
  end.

Definition into_prog {A} (x: option A) :=
  match x with
  | Some x => Here x
  | None   => ProgErr
  end.

Record state (V A B: Type): Type := State {
                                      runState: heap V -> list (thread V A) -> error (B * heap V * list (thread V A))
                                     }.

Arguments State {_ _ _} .
Arguments runState {_ _ _} .

Definition map_1 {A B C D} (f: A -> D) (x: A * B * C): D * B * C :=
  let '(x, y, z) := x in (f x, y, z).


Instance fmap_state {V A}: FMap (state V A) :=
  λ B C f fa, 
         State $ λ h threads,
                  map_1 f <$> (runState fa) h threads.

Instance mret_state {V A} : MRet (state V A) := λ A a, State $ λ h threads, Here (a, h, threads).

Instance mbind_state {V A}: MBind (state V A) :=
  λ _ _ f ma,
     State $
        λ h threads,
           match (runState ma) h threads with
           | Here (x, h', threads) => runState (f x) h' threads
           | ProgErr => ProgErr 
           | EvalErr => EvalErr
           end.

Definition lift_error {V A B} (x: error B): state V A B :=
  State $ λ h ts, 
        match x with
        | Here a  => Here (a, h , ts)
        | ProgErr => ProgErr
        | EvalErr => EvalErr
        end.

Definition modifyS' {V A B} (f: heap V -> B * heap V): state V A B :=
  State $ λ h t, mret $ (f h, t).

Section state_op.
   Context {V A B: Type}.

   Definition getS: state V A (heap V) :=
     State $ λ h t, mret (h, h, t).
  
   Definition putS (x: heap V): state V A unit :=
     State $ λ h t, mret (tt, x, t).

   Definition modifyS (f: heap V -> heap V): state V A () :=
     modifyS' $ λ h, (tt, f h).

   Definition fail: state V A B :=
     State $ λ h t, fail_prog.

   Definition fork (e: state V A B) (t: thread V A): state V A B :=
     State $ λ h ts, (runState e) h (t :: ts).

   Definition get_threads: state V A (list (thread V A)) :=
    State $ λ h ts, Here (ts, h , ts).

   Definition get_thread (n: nat): state V A (thread V A) :=
     State $ λ h ts, (λ t, (t, h, ts)) <$> into_eval (ts !! n).
End state_op.


Section heap_op.
  Context {V A B: Type}.

  Definition get (n: nat): state V A V :=
    getS ≫= λ h, lift_error $ into_prog $ lookup n h.

  Definition put (n: nat) (x : V) : state V A unit :=
    modifyS <[n := x]>.

  Definition alloc (v: V) : state V A nat :=
    modifyS'$ λ st, 
                let fresh := fresh $ dom (gset nat) st
                in (fresh, <[fresh := v]> st).

  Definition free (n: nat): state V A unit :=
    modifyS $ delete n.
End heap_op.


Definition step_vis {V R T A}
 (c: envE V T)
 : (T -> expr V A) -> state V R (expr V A) :=
    match c with
    |GetE l   => λ k, k <$> (get l)
    |PutE l v => λ k, k <$> (put l v)
    |AllocE v => λ k, k <$> (alloc v)
    |FreeE l  => λ k, k <$> (free l)
    end.

Definition step_expr {V R A} (e: expr V A): state V R (expr V A) :=
    match e with
    | Answer x  => mret $ Answer x 
    | Vis stateE k => step_vis stateE k 
    | Fork e' k => fork (mret k) (Forked e')
    | Think e'  =>  mret e'
    end.


Fixpoint eval_single {V R} (n: nat) (e: expr V R) {struct n}: state V R R :=
  match n with
  | O => fail
  | S n' => (step_expr e) ≫= (eval_single n') 
  end. 

Definition step_thread {V R} (t: thread V R) : state V R (thread V R) :=
    match t with 
    | Main e => Main <$> (step_expr e)
    | Forked e => Forked <$> (step_expr e) 
    end.

(* get main expr from pool 
   fix order indexing by modulo.
*)
Inductive scheduler V R := {
  schedule: list (thread V R) * heap V -> nat * scheduler V R
}.

Fixpoint check_main {V R} (ts: list (thread V R)): option R :=
         match ts with
         | [] => None
         | t :: ts' => is_main t ≫= is_done
         end.

Arguments schedule {_ _}.
Fixpoint eval_threaded {V R} (n: nat) (s : scheduler V R) {struct n}: state V R R.
refine (match n with
        | O    => lift_error fail_eval
        | S n' =>  
                  ts ← get_threads ;  
                  h  ← getS ; 
                  let '(nt, s') := (schedule s) (ts, h) in
                  curThread ← get_thread nt ; 
                  updatedThread ← step_thread curThread ;
                  _
                  
                  (* lift_error fail_prog *)
end).





Fixpoint split_and_circulate {A} (xs: list A) (f: A -> A) {struct xs}: (list A) :=
    match xs with
    | nil => nil
    | cons x xs' => xs' ++ [f x]
    end.

Definition step_delay_st_threads {V A} 
    (threads: list (Thread V A)) (s: heap V)
    :(heap V * (list (Thread V A))) :=
        match threads with 
        | nil => (s, nil)
        | cons e es' => match (runState (step_expr e) s) with
                        | None => (s, nil)
                        | Some (e', s') => (s', es' ++ [e'])
                        end
        end.

Definition check_delay_st {ST A} (e: delay_st ST A): A + delay_st ST A :=
    match e with
    | Answer x  => inl x
    | Get n k     => inr $ e
    | Put n s' k  => inr $ e
    | Think e'  => inr $ e
    end.

(* Todo check the order of effects with list and state here
   and remove all these nested pattern matches
*)
Fixpoint eval_threaded_delay_st {ST A} 
    (n: nat) 
    (threads: list (delay_st ST A))
    (s: ST) {struct n}: option A :=

    match n with
    | O => None
    | S n' => let (s', threads') := (step_delay_st_threads threads s)
              in match threads' with
                 | nil => None
                 | cons e' _ => match check_delay_st e' with
                                | inl x => Some x
                                | inr e'' => eval_threaded_delay_st n' threads' s'
                                end
                 end
    end.



