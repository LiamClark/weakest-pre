* adequacy State delay *
Het adequacy lemma voor state delay is het volgende: 

```coq 
Lemma adequacy_state_delay {A} (φ: A -> Prop) (n: nat) (x: A) 
  (prog : state_delay (gmap nat nat) A)
  (st: gmap nat nat)
  : (∀γ, ⊢ wp (state_interp γ) prog (λ x, ⌜φ x⌝)) ->
  ∃ st', eval_state_delay' n prog st = Some (st', x) ->
  φ x.
```

Gegeven dat het programma een bewezen wp heeft, dan bestaat er een eind state.
Dat als het programma evalueert hij in die eindstate eindigt en een resultaat `x` geeft.
Waarvoor `φ` geld.

1. De eerste stap is dan om st te kunnen alloceren op de heap:
```coq
  intros Hpre.
  apply (uPred.pure_soundness (M := iResUR Σ)).
  iMod (own_alloc (● (lift_excl st))) as (γ) "Hγ".
  - apply auth_auth_valid. intro i. 
    rewrite lookup_fmap. destruct (st !! i); done.
```
2. Nu is er een gname `γ` en een `state_interp γ st`, hiermee kunnen we
 door het eerste niveau van
 `Hpre: (∀ γ : gname, ⊢ wp (state_interp γ) prog (λ x : A, ⌜φ x⌝)) `

 want de definitie van `wp` is: 
 ```coq
Definition wp {Σ} {ST A} (SI: ST -> iProp Σ) (e: state_delay ST A) (Φ: A -> iProp Σ): iProp Σ.
refine(∀ σ, 
    SI σ ==∗
     wp_delay (runState e σ) (λ (res: option (ST * A)), 
       match res with   
       | Some (σ', x) => SI σ' ∗ Φ x 
       | None => True
       end)
)%I.
Defined.
 ```
 oftewel `iMod (Hpre γ $! st with "Hsi") as "HDelaypre".` geeft ons
```coq 
"HDelaypre" : wp_delay (runState prog st)
                (λ res : option (gmap nat nat * A),
                   match res with
                   | Some p =>
                       let (σ', x0) := p in state_interp γ σ' ∗ ⌜φ x0⌝
                   | None => True
                   end)
"Goal": ⌜∃ st' : gmap nat nat, eval_state_delay' n prog st = Some (st', x) → φ x⌝
```
