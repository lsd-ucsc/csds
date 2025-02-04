{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock.Interpret where
  open import Function
    using (_∘_)
  open import Data.Sum
    using (inj₁; inj₂)
  open import Execution.Sites
    as Sites
    using (Tree; Site; _∗_)
  open import Execution.Core
    using (_⇶_; perm; tick; fork; join; init; term; _⟫_; _∥_; id)
    using (Event; Tick)
  open import Execution.Causality
    as HB
    using (TrailingEvent[_,_]; LeadingEvent[_,_])

  variable
    T : Type
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)
    Action State : Type

  data Step (Action State : Type) : Type where
    start :                  Step Action State
    act   : Action → State → Step Action State
    merge : State  → State → Step Action State

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ (alg : Step Action State → State) where
    timestamp : (exec : Γ₁ ⇶ Γ₂) (acts : Tick exec → Action)
              → (Site Γ₁ → State) → (Event exec → State)
    timestamp (x₁ ∥ x₂) acts inputs (inj₁ e) = timestamp x₁ (acts ∘ inj₁) (inputs ∘ Site.thereˡ _) e
    timestamp (x₁ ∥ x₂) acts inputs (inj₂ e) = timestamp x₂ (acts ∘ inj₂) (inputs ∘ Site.thereʳ _) e
    timestamp (x₁ ⟫ x₂) acts inputs (inj₁ e) = timestamp x₁ (acts ∘ inj₁) inputs e
    timestamp (x₁ ⟫ x₂) acts inputs (inj₂ e) = timestamp x₂ (acts ∘ inj₂) (timestamp x₁ (acts ∘ inj₁) inputs ∘ LeadingEvent[ x₁ ,_]) e
    timestamp tick acts inputs (inj₁ s) = inputs s
    timestamp tick acts inputs (inj₂ s) = alg (act (acts _) (inputs Site.here))
    timestamp fork acts inputs (inj₁ s) = inputs s
    timestamp fork acts inputs (inj₂ s) = inputs Site.here
    timestamp join acts inputs (inj₁ s) = inputs s
    timestamp join acts inputs (inj₂ s) = alg (merge (inputs (Site.thereˡ _ Site.here)) (inputs (Site.thereʳ _ Site.here)))
    timestamp term acts inputs (inj₁ s) = inputs s
    timestamp init acts inputs (inj₂ s) = alg start
    timestamp (perm σ) acts inputs (inj₁ s) = inputs s
    timestamp (perm σ) acts inputs (inj₂ s) = inputs (Sites.‵index (Sites.‵sym σ) s)
