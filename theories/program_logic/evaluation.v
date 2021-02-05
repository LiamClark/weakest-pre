From stdpp Require Import base gmap list streams.
From shiris.program_logic Require Import delayfree.

(* Ask casper how to credit his blog post*)

Definition heap V := gmap nat V.

(* How am I going to differentiate between the main thread that returns a value,
   And the spawned threads that do not. 
 *)
Variant thread (V: Type): Type :=
| Main: ∀(A :Type ), expr V A -> thread V
| Forked (e: expr V ()).

Arguments Main {_ _}.
Arguments Forked {_}.

Record state (V A: Type): Type := State {
                                      runState: heap V -> list (thread V) -> option (A * heap V * list (thread V))
                                     }.

Arguments State {_ _} .
Arguments runState {_ _} .

Instance fmap_state {V}: FMap (state V) :=
  λ A B f fa, 
         State $ λ h threads, 
                  match (runState fa) h threads with
                  | Some (x, heap, threads) => Some (f x, heap , threads)
                  | None => None
                  end.

Instance mret_state {V} : MRet (state V) := λ A a, State $ λ h threads, Some (a, h, threads).

Instance mbind_state {V}: MBind (state V) :=
  λ _ _ f ma, State $
                    λ h threads, match (runState ma) h threads with
                          | Some (x, h', threads) => runState (f x) h' threads
                          | None => None
                          end.


Definition modifyS' {V A} (f: heap V -> A * heap V): state V A :=
  State $ λ h t, Some $ (f h, t).

Section state_op.
   Context {V A: Type}.

   Definition getS: state V (heap V) :=
     State $ λ h t, Some (h, h, t).
  
   Definition putS (x: heap V): state V unit :=
     State $ λ h t, Some (tt, x, t).

   Definition modifyS (f: heap V -> heap V): state V () :=
     modifyS' $ λ h, (tt, f h).

   Definition fail: state V A :=
     State $ λ h t, None.

   Definition ret_fail (m: option A): state V A := 
    match m with
    | Some x => mret x
    | None => fail
    end.

    Definition fork (e: state V A) (t: thread V): state V A :=
      State $ λ h ts, (runState e) h (t :: ts).
    
    Definition get_thread (n: nat): state V (thread V) :=
      State $ λ h ts, (λ t,( t, h, ts)) <$> ( ts !! n).
End state_op.


Section heap_op.
  Context {V: Type}.

  Definition get (n: nat): state V V :=
    getS ≫= λ h, ret_fail $ lookup n h.

  Definition put (n: nat) (x : V) : state V unit :=
    modifyS <[n := x]>.

  Definition alloc (v: V) : state V nat :=
    modifyS'$ λ st, 
                let fresh := fresh $ dom (gset nat) st
                in (fresh, <[fresh := v]> st).

  Definition free (n: nat): state V unit :=
    modifyS $ delete n.
End heap_op.


Definition step_vis {V R T}
 (c: envE V T)
 : (T -> expr V R) -> state V (expr V R) :=
    match c with
    |GetE l   => λ k, k <$> (get l)
    |PutE l v => λ k, k <$> (put l v)
    |AllocE v => λ k, k <$> (alloc v)
    |FreeE l  => λ k, k <$> (free l)
    end.

Definition step_expr {V R} (e: expr V R): state V (expr V R) :=
    match e with
    | Answer x  => mret $ Answer x 
    | Vis stateE k => step_vis stateE k 
    | Fork e' k => fork (mret k) (Forked e') 
    | Think e'  =>  mret e'
    end.


Fixpoint eval_single {V R} (n: nat) (e: expr V R) {struct n}: state V (option R) :=
  match n with
  | O => mret $ None
  | S n' => (step_expr e) ≫= (eval_single n') 
  end. 

Definition step_thread {V} (t: thread V) : state V (thread V) :=
    match t with 
    | Main e => Main <$> (step_expr e)
    | Forked e => Forked <$> (step_expr e) 
    end.

Fixpoint split_and_circulate {A} (xs: list A) (f: A -> A) {struct xs}: (list A) :=
    match xs with
    | nil => nil
    | cons x xs' => xs' ++ [f x]
    end.

(* Definition step_delay_st_threads {V A} 
    (threads: list (Thread V A)) (s: heap V)
    :(heap V * (list (Thread V A))) :=
        match threads with 
        | nil => (s, nil)
        | cons e es' => match (runState (step_expr e) s) with
                        | None => (s, nil)
                        | Some (e', s') => (s', es' ++ [e'])
                        end
        end.
 *)
Definition check_exp {V A} (e: expr V A): A + expr V A :=
    match e with
    | Answer x  => inl x
    | Think e'  => inr $ e
    | Fork e' k => inr $ Fork e' k
    | Vis env k => inr $ Vis env k
    end.

(* Complete this definition using the evaluation order given by the stream of natural numbers *)
Fixpoint eval_threaded_delay_st {ST A} 
    (n: nat) 
    (order: stream nat)
    {struct n}: option A :=

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



