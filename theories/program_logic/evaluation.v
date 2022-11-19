From stdpp Require Import base gmap list streams.
From shiris.program_logic Require Import itree.

Definition heap V := gmap nat V.

(* 
  We need to store threads in a thread pool.
  A thread can either be a main thread (returns a value),
  or a Forked thread (always returns unit)
*)
Variant thread (V A: Type): Type :=
| Main (e: expr V A)
| Forked (e: expr V ()).

Arguments Main {_ _}.
Arguments Forked {_ _}.

Instance fmap_thread {V}: FMap (thread V) :=
  λ A B f fa,
    match fa with
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

(* 
  V: the type of values on the heap
  A: The type the main thread of the computation yields
  B: the value computed by the computation
*)
Record state (V A B: Type): Type := 
  State {
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
           '(x, h', threads) ← (runState ma) h threads ;
            runState (f x) h' threads.

(*
  Helper lemma that is required for adequacy.
  Running a program that conists of a bind, is the same as running the initial computation
  and then running the continuation with the results from the first computation.
*)
Lemma run_bind_dist {V A B C} h ts
  (m: state V A B) (f: B -> state V A C):
  runState (m ≫= f) h ts =  match runState m h ts with
                             | Here (x, h', ts') => runState (f x) h' ts'
                             | ProgErr => ProgErr
                             | EvalErr => EvalErr
                             end.
Proof.
  unfold mbind. unfold mbind_state.
  done.
Qed.
           
Definition lift_error {V A B} (x: error B): state V A B :=
  State $ λ h ts, 
        a ← x ;
        Here (a, h, ts).

Definition modifyS {V A B} (f: heap V -> B * heap V): state V A B :=
  State $ λ h ts, mret $ (f h, ts).

Section state_op.
   Context {V A B: Type}.

   Definition get_heap: state V A (heap V) :=
     State $ λ h t, mret (h, h, t).
  
   Definition put_heap (x: heap V): state V A unit :=
     State $ λ h t, mret (tt, x, t).

   Definition fail: state V A B :=
     State $ λ h t, fail_prog.

  (*
    Add forked threads at the end to keep thread indices stable.
  *)
   Definition fork (e: state V A B) (t: thread V A): state V A B :=
     State $ λ h ts, (runState e) h (ts ++ [t]).

   Definition get_threads: state V A (list (thread V A)) :=
    State $ λ h ts, Here (ts, h , ts).

   Definition get_thread (n: nat): state V A (thread V A) :=
     State $ λ h ts, (λ t, (t, h, ts)) <$> into_eval (ts !! n).

   Definition set_thread (n: nat) (t: thread V A): state V A () :=
     State $ λ h ts, Here $ (tt, h,  <[n:=t]> ts).
End state_op.


Section heap_op.
  Context {V A B: Type}.

  Definition modifyS' (n: nat) (f: heap V -> heap V): state V A () :=
    State $ λ h ts, if decide (is_Some (h !! n)) then Here (tt, f h, ts) else ProgErr.

  Definition get (n: nat): state V A V :=
    get_heap ≫= λ h, lift_error $ into_prog $ lookup n h.

  Definition put (n: nat) (x : V) : state V A unit :=
    modifyS' n  <[n := x]>.

  Definition alloc (v: V) : state V A nat :=
    modifyS $ λ st, 
                let l := fresh_loc st
                in (l, <[l:= v]> st).

  Definition free (n: nat): state V A unit :=
   modifyS' n (delete n).

  Definition cmpXchg {cmp: EqDecision V} (l: nat) (v1 v2: V): state V A (V * bool) :=
    get l ≫= λ vl, if decide (vl = v1) then put l v2 ;; mret (vl, true) else mret (vl, false).
End heap_op.

Definition step_vis {V R T A} {cmp: EqDecision V} (c: envE V T):
  (T -> expr V A) -> state V R (expr V A) :=
    match c with
    | GetE l          => λ k, k <$> get l
    | PutE l v        => λ k, k <$> put l v
    | AllocE v        => λ k, k <$> alloc v
    | FreeE l         => λ k, k <$> free l
    | CmpXchgE l v v' => λ k, k <$> cmpXchg l v v'
    | FailE           => λ k, lift_error fail_prog
    end.
  
Definition step_expr {V R A} {cmp: EqDecision V} (e: expr V A): state V R (expr V A) :=
  match e with
  | Answer x  => mret $ Answer x 
  | Vis stateE k => step_vis stateE k 
  | Fork e' k => fork (mret k) (Forked e')
  | Think e'  =>  mret e'
  end.

Fixpoint eval_single {V R} {cmp: EqDecision V} (n: nat) (e: expr V R) {struct n}: state V R R :=
  match n with
  | O => fail
  | S n' => step_expr e ≫= eval_single n' 
  end. 

Definition step_thread {V R} {cmp: EqDecision V} (t: thread V R) : state V R (thread V R) :=
  match t with 
  | Main e => Main <$> step_expr e
  | Forked e => Forked <$> step_expr e 
  end.

CoInductive scheduler V R := Scheduler {
  schedule: list (thread V R) * heap V -> nat * scheduler V R
}.

Arguments schedule {_ _}.
Arguments Scheduler {_ _}.

CoFixpoint const_scheduler {V R} (n: nat): scheduler V R :=
  Scheduler $  λ '(ts, h), (n, const_scheduler n).

Fixpoint list_scheduler {V R} (s: list nat) (n: nat): scheduler V R :=
  Scheduler $ λ '(ts, h),
    match s with
     | []      => (n, const_scheduler n)
     | n' :: ns => (n', list_scheduler ns n)
     end.

CoFixpoint stream_scheduler {V R} (s: stream nat): scheduler V R :=
  Scheduler $ λ '(ts, h),
    let '(scons x xs) := s in (x, stream_scheduler xs).

(* Main thread is always at position zero*)
Definition check_main {V R} (ts: list (thread V R)): option R :=
         match ts with
         | [] => None
         | t :: ts' => is_main t ≫= is_done
         end.

(*
  First we retrieve a thread_index from the scheduler.
  Modulo it to ensure its in bound of the thread pool.
  Then have that thread perform a step and update it in the pool.
*)
Definition single_step_thread {V R} {cmp: EqDecision V} (s: scheduler V R)
  : state V R (scheduler V R ) :=
      ts ← get_threads ;  
      h  ← get_heap ; 
      let '(nt, s')    := (schedule s) (ts, h) in
      let thread_count := length ts in
      let thread_index := nt mod thread_count in
      curThread ← get_thread thread_index ; 
      updatedThread ← step_thread curThread ;
      set_thread thread_index updatedThread ;; 
      mret s'.

(* lift single_step_thread to a recursive fuel evaluator *)
Fixpoint eval_threaded {V R} {cmp: EqDecision V} (n: nat) (s : scheduler V R) {struct n}: state V R R :=
  match n with
    | O    => lift_error fail_eval
    | S n' => s' ← single_step_thread s;
              ts' ← get_threads ;
              match check_main ts' with
              | Some r => mret r
              | None => eval_threaded n' s' 
              end
  end.

Definition fstt {A B C} (x: A * B * C): A := x.1.1.

(* 
  cmp: The EqDecision type class is there to be able to compare values on the heap for CasE.
  n  : The fuel to ensure termination.
  s  : The co-inductive scheduler to allow for interleaving of threads.
  e  : The program to run.
*)
Definition run_program {V R} {cmp: EqDecision V} (n: nat)
  (s: scheduler V R) (e: expr V R): error R :=
    fst ∘ fst <$> runState (eval_threaded n s) ∅ [Main e].

Definition incr (l: loc): expr nat nat :=
  itree.get l ≫= λ n, itree.put l (S n) ;; mret n.

Definition decr (l: loc): expr nat nat :=
  itree.get l ≫= λ n, itree.put l (n - 1) ;; mret n.

(* test program*)
Definition prog: expr nat nat.
refine (
  l ← itree.alloc 5;
  itree.fork (iter (λ t, incr l ;; mret (inl tt)) tt ;; mret tt) ;;
  (decr l ;; decr l ;; itree.get l)
  ).
  exact nat.
Defined.

Definition prog_scheduler {V R: Type} := (@list_scheduler V R [0; 0; 5 ] 0).

Definition dump_heap {A B C} (x: A * B * C): (A * C) :=
  (x.1.1, x.2).

(*
 index 0 is the main thread
 because it will exit with 3 if we just evaluate it.
 now if we add evaluations in thread 1 it needs more then one step to actually update
 because decr is atleast 2 steps
*)
Lemma test_5: run_program 50 (list_scheduler [0;0;0;0;1;1;1;1;1] 0) prog = Here 5.
Proof.
  vm_compute.
  done.
Qed.

Lemma test_3: run_program 50 (list_scheduler [] 0) prog = Here 3.
Proof.
  vm_compute.
  done.
Qed.
