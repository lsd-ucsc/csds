```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```

```agda
module Clock.Monotonicity where
  open import Data.Nat
    using (ℕ)
  import Relation.Binary.PropositionalEquality
    as Eq
  open import Function
    using (_∘_)
  open import Data.Product
    using (_,_; -,_)
  open import Data.Sum
    using (inj₁; inj₂)

  open import Execution.Sites
    as Tree
    using (Tree; Site)
  open import Execution.Core
    using (_⇶_; _⇶₁_)
    using (Event; Tick; Cut)
    using (_⇶[_]_; id; _⟫_; _∥_; perm; tick; fork; join)
  open import Execution.Causality
    as HB
    using (_↝_; init; go)
    using (↝ₙ-syntax)
    using (before[_]; after[_]; during[_])
  open import Clock.Interpret
    as Interpret
    using (Step; _↦_)
  open Event
    using (cut[_]; site[_])

  variable
    T : Type
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)

  record Clock {Action State : Type}
               (alg : Step Action State → State)
               (_≤_ : State → State → Type)
             : Type where
    open Step using (act; merge)

    field ≤-refl      : ∀ s → s ≤ s
    field ≤-trans     : ∀ s₁ s₂ s₃ → (s₁ ≤ s₂) → (s₂ ≤ s₃) → (s₁ ≤ s₃)
    field act-mono    : ∀ p s → s ≤ alg (act p s)
    field merge-mono¹ : ∀ s₁ s₂ → s₁ ≤ alg (merge s₁ s₂)
    field merge-mono² : ∀ s₁ s₂ → s₂ ≤ alg (merge s₁ s₂)

  module _ {Action State : Type} {alg : Step Action State → State}
           {_≤_ : State → State → Type} (clock : Clock alg _≤_)
           where
    open Clock clock
      using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

    ≤-reflexive : ∀{s₁ s₂} → (s₁ Eq.≡ s₂) → (s₁ ≤ s₂)
    ≤-reflexive Eq.refl = ≤-refl _

    ⊑ₙ-syntax : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) → (Site Γ₁ → Site Γ₂ → Type)
    ⊑ₙ-syntax {Γ₁ = Γ₁} exec s₁ s₂
      = ∀ actions (input : Γ₁ ↦ State) →
        let C[_] = (Interpret.apply alg exec actions) input
        in input s₁ ≤ C[ s₂ ]
    syntax ⊑ₙ-syntax exec s₁ s₂ = s₁ ⊑ₙ[ exec ] s₂

    _⊑_ : {exec : Γ₁ ⇶ Γ₂} → Event exec → Event exec → Type
    _⊑_ {Γ₁ = Γ₁} t₁ t₂
      = ∀ actions (input : Γ₁ ↦ State) →
        let C[_] = (Interpret.timestamp alg actions) input
        in C[ t₁ ] ≤ C[ t₂ ]

    ⊑ₙ-refl : ∀{t} → t ⊑ₙ[ id {_} {Γ} ] t
    ⊑ₙ-refl = λ _ _ → ≤-refl _

    liftˡ : {left  : Γ₁ ⇶₁ Γ₂}
          → {right : Γ₃ ⇶₁ Γ₄}
          → ∀{a} {t₃ : a Tree.∈ Γ₃}
          → ∀{b} {t₄ : b Tree.∈ Γ₄}
          → (-, t₃) ⊑ₙ[ right ] (-, t₄)
          → (-, Tree.thereʳ _ t₃) ⊑ₙ[ left ∥ right ] (-, Tree.thereʳ _ t₄)
    liftˡ f actions input = f (actions ∘ inj₂) λ(_ , s) → input (-, Tree.thereʳ _ s)

    liftʳ : {left  : Γ₁ ⇶₁ Γ₂}
          → {right : Γ₃ ⇶₁ Γ₄}
          → ∀{a} {t₁ : a Tree.∈ Γ₁}
          → ∀{b} {t₂ : b Tree.∈ Γ₂}
          → (-, t₁) ⊑ₙ[ left ] (-, t₂)
          → (-, Tree.thereˡ _ t₁) ⊑ₙ[ left ∥ right ] (-, Tree.thereˡ _ t₂)
    liftʳ f events input = f (events ∘ inj₁) (λ(_ , s) → input (-, Tree.thereˡ _ s))

    _;_ : {exec : Γ₁ ⇶ Γ₂} {step : Γ₂ ⇶₁ Γ₃}
        → {t₁ : Site Γ₁}
        → {t₂ : Site Γ₂}
        → {t₃ : Site Γ₃}
        → t₁ ⊑ₙ[ exec ] t₂
        → t₂ ⊑ₙ[ step ] t₃
        → t₁ ⊑ₙ[ exec ⟫ step ] t₃
    (f ; g) actions input =
      ≤-trans _ _ _
        (f (actions ∘ inj₁) input)
        (g (actions ∘ inj₂) (Interpret.apply alg _ (actions ∘ inj₁) input))

{-
→ (σ : Γ₁ ≅ Γ₂)
→ ∀{a} {s₁ : a ∈ Γ₁}
→ ∀{b} {s₂ : b ∈ Γ₂}
→ Tree.Match[ σ ] (a , s₁) (b , s₂)
→ (a , Tree.‵index (Tree.‵sym σ)) ≡ (b , s₂)
-}

    xxx : ∀{a b : Tree T} {Γ₁ Γ₂ : Tree (Tree T)} {σ : Γ₁ Tree.≅ Γ₂}
        → {t₁ : a Tree.∈ Γ₁}
        → {t₂ : b Tree.∈ Γ₂}
        → Tree.Match[ σ ] (a , t₁) (b , t₂)
        → (f : ∀{a} → (a Tree.∈ Γ₁) → State)
        → f t₁ Eq.≡ f (Tree.‵index (Tree.‵sym σ) t₂)
    xxx (Tree.Match-refl (_ , _)) f = Eq.refl
    xxx (Tree.Match-swapₗ Γ₂ s₁) f = Eq.refl
    xxx (Tree.Match-swapᵣ Γ₁ s₂) f = Eq.refl
    xxx (Tree.Match-assoc₁ Γ₁ s₁) f = Eq.refl
    xxx (Tree.Match-assoc₂ Γ₂ s₂) f = Eq.refl
    xxx (Tree.Match-assoc₃ Γ₃ s₃) f = Eq.refl
    xxx (Tree.Match-trans σ' σ'') f = Eq.trans (xxx σ' f) {!xxx σ''!}
    xxx (Tree.Match-congₗ σ₂ s₁ s₁' σ') f = {!!}
    xxx (Tree.Match-congᵣ σ₁ s₂ s₂' σ') f = {!!}

    apply-mono : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂)
               → {t₁ : Site Γ₁}
               → {t₂ : Site Γ₂}
               → t₁ ↝ₙ[ exec ] t₂
               → t₁ ⊑ₙ[ exec ] t₂
    apply-mono tick {t₁ = (_ , Tree.here)} _ actions input
      = act-mono (actions _) (input (-, Tree.here))
    apply-mono fork {t₁ = (_ , Tree.here)} _ actions input
      = ≤-refl _
    apply-mono join {t₁ = (_ , Tree.thereˡ _ Tree.here)} _ actions input
      = merge-mono¹ (input ((-, Tree.thereˡ _ Tree.here)))
                    (input ((-, Tree.thereʳ _ Tree.here)))
    apply-mono join {t₁ = (_ , Tree.thereʳ _ Tree.here)} _ actions input
      = merge-mono² (input ((-, Tree.thereˡ _ Tree.here)))
                    (input ((-, Tree.thereʳ _ Tree.here)))
    apply-mono (perm σ) {t₂ = (a , b)} ‵σ events input
      = {!!}
      -- ≤-reflexive (Eq.sym (Eq.cong input {!Tree.‶index σ!}))
      -- Eq.cong input (Tree.‶index σ _)
    apply-mono id (Tree.Match-refl _)
      = ⊑ₙ-refl
    apply-mono (left ∥ _    ) (Tree.thereˡ _ _ t₁↝t₂)
      = liftʳ (apply-mono left t₁↝t₂)
    apply-mono (_    ∥ right) (Tree.thereʳ _ _ t₁↝t₂)
      = liftˡ (apply-mono right t₁↝t₂)
    apply-mono (exec ⟫ step) (_ , t₁↝tᵢ , tᵢ↝t₂)
      = apply-mono exec t₁↝tᵢ ; apply-mono step tᵢ↝t₂
{-
    -- TODO: Factor this into a proof that `Interpret.apply` respects `Core._;_`
    -- and a proof that `HB.after[ t ] ; HB.before[ t ] ≡ exec`.
    foo : {exec : Γ₁ ⇶ Γ₂}
        → (t : Cut exec)
        → ∀ actions (inputs : ∀{a} → (a Tree.∈ Γ₁) → State)
        → (   Interpret.apply alg _ (actions ∘ HB.tliftʳ t)
            ∘ Interpret.apply alg _ (actions ∘ HB.tliftˡ t) )
          inputs
        Eq.≡ Interpret.apply alg _ actions
          inputs
    foo (Cut.now  _     ) actions inputs
      = Eq.refl
    foo (Cut.back step t) actions inputs
      = Eq.cong (Interpret.apply alg step _)
          (foo t (actions ∘ inj₁) inputs)

    -- TODO: Factor this into a proof that `Interpret.apply` respects `Core._;_`
    -- and a proof that `HB.before[ t₁ ] ; HB.during[ t₁≤t₂ ] ≡ HB.before[ t₂ ]`.
    bar : {exec : Γ₁ ⇶ Γ₂}
        → {t₁ t₂ : Cut exec}
        → (t₁≤t₂ : t₁ HB.⋯ t₂)
        → ∀ events inputs
        → (   Interpret.apply alg _ (events ∘ HB.tlift  t₁≤t₂)
            ∘ Interpret.apply alg _ (events ∘ HB.tliftˡ t₁   ) )
          inputs
        Eq.≡  Interpret.apply alg _ (events ∘ HB.tliftˡ    t₂)
          inputs
    bar (go st t₁≤t₂)  events inputs
      = bar t₁≤t₂ (events ∘ inj₁) inputs
    bar (init _ t₁) events inputs
      = foo t₁ events inputs

    timestamp-mono : {exec : Γ₁ ⇶ Γ₂}
                   → {e₁ e₂ : Event exec}
                   → e₁ ↝ e₂
                   → e₁ ⊑ e₂
    timestamp-mono {e₁ = e₁} {e₂ = e₂} (t₁₂ , p₁₂) events input =
      let ins = Interpret.apply alg _ (events ∘ HB.tliftˡ cut[ e₁ ]) input
      in ≤-trans _ _ _
        (apply-mono during[ t₁₂ ] p₁₂ (events ∘ HB.tlift t₁₂) ins)
        (≤-reflexive (Eq.cong (λ ▢ → ▢ site[ e₂ ]) (bar t₁₂ events input)))
-}
```
