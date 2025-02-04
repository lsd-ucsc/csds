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
    using (_,_)
  open import Data.Sum
    using (inj₁; inj₂)

  open import Execution.Sites
    as Tree
    using (Tree; Site)
  open import Execution.Core
    using (_⇶_; _⟫_; _∥_; perm; tick; fork; join; init; term; id)
    using (Event; Tick; Cut)
  open import Execution.Causality
    as HB
    using (_↝_; TrailingEvent[_,_]; LeadingEvent[_,_])
  open import Clock.Interpret
    as Interpret
    using (Step)

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

    _⊑_ : {exec : Γ₁ ⇶ Γ₂} → Event exec → Event exec → Type
    _⊑_ {exec = exec} e₁ e₂
      = ∀ actions input →
        let C[_] = Interpret.timestamp alg exec actions input
        in C[ e₁ ] ≤ C[ e₂ ]

    timestamp-trailing : (exec : Γ₁ ⇶ Γ₂)
                       → (s : Site Γ₁)
                       → ∀ actions input
                       → input s
                       ≤ Interpret.timestamp alg exec actions input TrailingEvent[ exec , s ]
    timestamp-trailing (x₁ ∥ x₂) (Site.thereˡ _ s) actions input = timestamp-trailing x₁ s (actions ∘ inj₁) (input ∘ Site.thereˡ _)
    timestamp-trailing (x₁ ∥ x₂) (Site.thereʳ _ s) actions input = timestamp-trailing x₂ s (actions ∘ inj₂) (input ∘ Site.thereʳ _)
    timestamp-trailing (x₁ ⟫ x₂) s actions input = timestamp-trailing x₁ s (actions ∘ inj₁) input
    timestamp-trailing tick      s actions input = ≤-refl _
    timestamp-trailing fork      s actions input = ≤-refl _
    timestamp-trailing join      s actions input = ≤-refl _
    timestamp-trailing term      s actions input = ≤-refl _
    timestamp-trailing (perm σ)  s actions input = ≤-refl _

    timestamp-mono : (exec : Γ₁ ⇶ Γ₂)
                   → (e₁ e₂ : Event exec)
                   → e₁ ↝ e₂
                   → e₁ ⊑ e₂
    timestamp-mono (x₁ ∥ x₂) (inj₁ e₁) (inj₁ e₂) p₁₂ actions input = timestamp-mono x₁ e₁ e₂ p₁₂ (actions ∘ inj₁) (input ∘ Site.thereˡ _)
    timestamp-mono (x₁ ∥ x₂) (inj₂ e₁) (inj₂ e₂) p₁₂ actions input = timestamp-mono x₂ e₁ e₂ p₁₂ (actions ∘ inj₂) (input ∘ Site.thereʳ _)
    timestamp-mono (x₁ ⟫ x₂) (inj₁ e₁) (inj₁ e₂) p₁₂ actions input = timestamp-mono x₁ e₁ e₂ p₁₂ (actions ∘ inj₁) input
    timestamp-mono (x₁ ⟫ x₂) (inj₁ e₁) (inj₂ e₂) (sₘ , p₁ₘ , pₘ₂) actions input =
      (≤-trans _ _ _ (≤-trans _ _ _
        (timestamp-mono x₁ e₁ LeadingEvent[ x₁ , sₘ ] p₁ₘ (actions ∘ inj₁) input)
        (timestamp-trailing x₂ sₘ (actions ∘ inj₂) _) )
        (timestamp-mono x₂ TrailingEvent[ x₂ , sₘ ] e₂ pₘ₂ (actions ∘ inj₂) _) )
    timestamp-mono (x₁ ⟫ x₂) (inj₂ e₁) (inj₂ e₂) p₁₂ actions input =
      timestamp-mono x₂ e₁ e₂ p₁₂ (actions ∘ inj₂)
        (Interpret.timestamp alg x₁ (actions ∘ inj₁) input ∘ LeadingEvent[ x₁ ,_])
    timestamp-mono tick (inj₁ s₁) (inj₁ s₂) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono tick (inj₂ s₁) (inj₂ s₂) p₁₂ actions input = ≤-refl _
    timestamp-mono tick (inj₁ Site.here) (inj₂ s₂) p₁₂ actions input = act-mono (actions _) _
    timestamp-mono fork (inj₁ s₁) (inj₁ s₂) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono fork (inj₁ Site.here) (inj₂ s₂) p₁₂ actions input = ≤-refl _
    timestamp-mono fork (inj₂ s₁) (inj₂ s₂) p₁₂ actions input = ≤-refl _
    timestamp-mono join (inj₁ x) (inj₁ x₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono join (inj₁ (Site.thereˡ _ Site.here)) (inj₂ y) p₁₂ actions input =
      merge-mono¹ (input (Site.thereˡ _ Site.here)) (input (Site.thereʳ _ Site.here))
    timestamp-mono join (inj₁ (Site.thereʳ _ Site.here)) (inj₂ y) p₁₂ actions input =
      merge-mono² (input (Site.thereˡ _ Site.here)) (input (Site.thereʳ _ Site.here))
    timestamp-mono join (inj₂ y) (inj₂ y₁) p₁₂ actions input = ≤-refl _
    timestamp-mono init (inj₂ y) (inj₂ y₁) p₁₂ actions input = ≤-refl _
    timestamp-mono term (inj₁ x) (inj₁ x₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono (perm σ) (inj₁ x) (inj₁ x₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono (perm σ) (inj₂ y) (inj₂ y₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono (perm σ) (inj₁ x) (inj₂ y) p₁₂ actions input =
      (≤-reflexive ∘ Eq.cong input)
        (Eq.trans
          (Eq.sym (Tree.‶index σ x))
          (Eq.cong (Tree.‵index (Tree.‵sym σ)) p₁₂) )
```
