```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```

```agda
module Clock.Monotonicity where
  open import Data.Nat
    using (ℕ)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)
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
    using (Event; Tick)
  open import Execution.Causality
    as HB
    using (_↝_; TrailingEvent[_,_]; LeadingEvent[_,_])
  open import Clock.Interpret
    as Interpret
    using (Step; Stepped; Timestamped; timestamped; timestamped⁻¹)

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

    ≤-reflexive : ∀{s₁ s₂} → (s₁ ≡ s₂) → (s₁ ≤ s₂)
    ≤-reflexive Eq.refl = ≤-refl _

    _⊑_ : {exec : Γ₁ ⇶ Γ₂} → Event exec → Event exec → Type
    _⊑_ {exec = exec} e₁ e₂
      = ∀ actions input →
        let C[_] = Interpret.timestamp alg exec actions input
        in C[ e₁ ] ≤ C[ e₂ ]

    timestamped-inverse : (Γ : Tree (Tree T)) → (ts : Site Γ → State) → ∀ s → timestamped (timestamped⁻¹ ts) s ≡ ts s
    timestamped-inverse (Tree.leaf Γ) ts Site.here         = Eq.refl
    timestamped-inverse (Γ Tree.∗ _)  ts (Site.thereˡ _ s) = timestamped-inverse Γ (ts ∘ Site.thereˡ _) s
    timestamped-inverse (_ Tree.∗ Γ)  ts (Site.thereʳ _ s) = timestamped-inverse Γ (ts ∘ Site.thereʳ _) s

    timestamp-trailing : (exec : Γ₁ ⇶ Γ₂)
                      → (s : Site Γ₁)
                      → (actions : Stepped Action exec) → (input : Timestamped State Γ₁)
                      → Interpret.timestamped input s
                      ≤ Interpret.timestamp alg exec actions input TrailingEvent[ _ , s ]
    timestamp-trailing (x₁ ∥ x₂) (Site.thereˡ _ s) (actions , _) (input , _) = timestamp-trailing x₁ s actions input
    timestamp-trailing (x₁ ∥ x₂) (Site.thereʳ _ s) (_ , actions) (_ , input) = timestamp-trailing x₂ s actions input
    timestamp-trailing (x₁ ⟫ x₂) s (actions , _) input = timestamp-trailing x₁ s actions input
    timestamp-trailing tick Site.here actions input = ≤-refl _
    timestamp-trailing fork Site.here actions input = ≤-refl _
    timestamp-trailing join (Site.thereˡ _ Site.here) actions input = ≤-refl _
    timestamp-trailing join (Site.thereʳ _ Site.here) actions input = ≤-refl _
    timestamp-trailing term Site.here actions input = ≤-refl _
    timestamp-trailing (perm σ) s actions input = ≤-refl _

    timestamp-mono : (exec : Γ₁ ⇶ Γ₂)
                   → (e₁ e₂ : Event exec)
                   → e₁ ↝ e₂
                   → e₁ ⊑ e₂
    timestamp-mono (x₁ ∥ x₂) (inj₁ e₁) (inj₁ e₂) p₁₂ (actions , _) (input , _) = timestamp-mono x₁ e₁ e₂ p₁₂ actions input
    timestamp-mono (x₁ ∥ x₂) (inj₂ e₁) (inj₂ e₂) p₁₂ (_ , actions) (_ , input) = timestamp-mono x₂ e₁ e₂ p₁₂ actions input
    timestamp-mono (x₁ ⟫ x₂) (inj₁ e₁) (inj₁ e₂) p₁₂ (actions , _) input = timestamp-mono x₁ e₁ e₂ p₁₂ actions input
    timestamp-mono (x₁ ⟫ x₂) (inj₁ e₁) (inj₂ e₂) (sₘ , p₁ₘ , pₘ₂) (act₁ , act₂) input =
      (≤-trans _ _ _ (≤-trans _ _ _ (≤-trans _ _ _
        (timestamp-mono x₁ e₁ LeadingEvent[ x₁ , sₘ ] p₁ₘ act₁ input)
        (≤-reflexive (Eq.sym (timestamped-inverse _ _ sₘ))) )
        (timestamp-trailing x₂ sₘ act₂ _) )
        (timestamp-mono x₂ TrailingEvent[ x₂ , sₘ ] e₂ pₘ₂ act₂ _) )
    timestamp-mono (x₁ ⟫ x₂) (inj₂ e₁) (inj₂ e₂) p₁₂ (act₁ , act₂) input =
      timestamp-mono x₂ e₁ e₂ p₁₂ act₂ (Interpret.apply alg x₁ act₁ input)
    timestamp-mono tick (inj₁ s₁) (inj₁ s₂) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono tick (inj₂ s₁) (inj₂ s₂) p₁₂ actions input = ≤-refl _
    timestamp-mono tick (inj₁ Site.here) (inj₂ s₂) p₁₂ actions input = act-mono actions _
    timestamp-mono fork (inj₁ s₁) (inj₁ s₂) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono fork (inj₁ Site.here) (inj₂ s₂) p₁₂ actions input = ≤-refl _
    timestamp-mono fork (inj₂ s₁) (inj₂ s₂) p₁₂ actions input = ≤-refl _
    timestamp-mono join (inj₁ x) (inj₁ x₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono join (inj₁ (Site.thereˡ _ Site.here)) (inj₂ y) p₁₂ actions (in₁ , in₂) =
      merge-mono¹ in₁ in₂
    timestamp-mono join (inj₁ (Site.thereʳ _ Site.here)) (inj₂ y) p₁₂ actions (in₁ , in₂) =
      merge-mono² in₁ in₂
    timestamp-mono join (inj₂ y) (inj₂ y₁) p₁₂ actions input = ≤-refl _
    timestamp-mono init (inj₂ y) (inj₂ y₁) p₁₂ actions input = ≤-refl _
    timestamp-mono term (inj₁ x) (inj₁ x₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono (perm σ) (inj₁ x) (inj₁ x₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono (perm σ) (inj₂ y) (inj₂ y₁) p₁₂ actions input = ≤-reflexive (Eq.cong _ p₁₂)
    timestamp-mono (perm σ) (inj₁ x) (inj₂ y) p₁₂ actions input =
      (≤-reflexive ∘ Eq.cong (timestamped input))
        (Eq.trans
          (Eq.sym (Tree.‶index σ x))
          (Eq.cong (Tree.‵index (Tree.‵sym σ)) p₁₂) )
```
