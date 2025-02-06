{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock.Interpret where
  open import Function
    using (_∘_)
  open import Data.Unit
    using (⊤; tt)
  open import Data.Product
    using (_×_; _,_)
  open import Data.Sum
    using (inj₁; inj₂)
  open import Execution.Sites
    as Sites
    using (Tree; Site; ∅; leaf; _∗_)
  open import Execution.Core
    using (_⇶_; perm; tick; fork; join; init; term; _⟫_; _∥_)
    using (Event)
  open import Execution.Causality
    using (LeadingEvent[_,_])

  variable
    T : Type
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)
    Action State : Type

  data Step (Action State : Type) : Type where
    start :                  Step Action State
    act   : Action → State → Step Action State
    merge : State  → State → Step Action State

  module _ (State : Type) where
    Timestamped : Tree (Tree T) → Type
    Timestamped ∅ = ⊤
    Timestamped (leaf _) = State
    Timestamped (Γ₁ ∗ Γ₂) = Timestamped Γ₁ × Timestamped Γ₂

  timestamped : {Γ : Tree (Tree T)} → Timestamped State Γ → (Site Γ → State)
  timestamped ts          Site.here         = ts
  timestamped (ts₁ , ts₂) (Site.thereˡ _ s) = timestamped ts₁ s
  timestamped (ts₁ , ts₂) (Site.thereʳ _ s) = timestamped ts₂ s

  timestamped⁻¹ : {Γ : Tree (Tree T)} → (Site Γ → State) → Timestamped State Γ
  timestamped⁻¹ {Γ = ∅}       ts = tt
  timestamped⁻¹ {Γ = leaf Γ}  ts = ts Site.here
  timestamped⁻¹ {Γ = Γ₁ ∗ Γ₂} ts = (timestamped⁻¹ (ts ∘ Site.thereˡ _) , timestamped⁻¹ (ts ∘ Site.thereʳ _))

  module _ (Action : Type) where
    Stepped : {Γ₁ Γ₂ : Tree (Tree T)} → (Γ₁ ⇶ Γ₂) → Type
    Stepped (x₁ ∥ x₂) = Stepped x₁ × Stepped x₂
    Stepped (x₁ ⟫ x₂) = Stepped x₁ × Stepped x₂
    Stepped tick = Action
    Stepped fork = ⊤
    Stepped join = ⊤
    Stepped init = ⊤
    Stepped term = ⊤
    Stepped (perm σ) = ⊤

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ {Action State : Type} (alg : Step Action State → State) where
      apply : (exec : Γ₁ ⇶ Γ₂) (acts : Stepped Action exec)
            → Timestamped State Γ₁ → Timestamped State Γ₂
      timestamp : (exec : Γ₁ ⇶ Γ₂) (acts : Stepped Action exec)
                → Timestamped State Γ₁ → (Event exec → State)

      apply exec acts ts = timestamped⁻¹ (timestamp exec acts ts ∘ LeadingEvent[ exec ,_])

      timestamp (x₁ ∥ x₂) (acts , _) (ts , _) (inj₁ e) = timestamp x₁ acts ts e
      timestamp (x₁ ∥ x₂) (_ , acts) (_ , ts) (inj₂ e) = timestamp x₂ acts ts e
      timestamp (x₁ ⟫ x₂) (acts , _)      ts  (inj₁ e) = timestamp x₁ acts ts e
      timestamp (x₁ ⟫ x₂) (acts₁ , acts₂) ts  (inj₂ e) = timestamp x₂ acts₂ (apply x₁ acts₁ ts) e
      -- trailing events
      timestamp tick      _               ts  (inj₁ s) = timestamped ts s
      timestamp fork      _               ts  (inj₁ s) = timestamped ts s
      timestamp join      _               ts  (inj₁ s) = timestamped ts s
      timestamp term      _               ts  (inj₁ s) = timestamped ts s
      timestamp (perm _)  _               ts  (inj₁ s) = timestamped ts s
      -- leading events
      timestamp tick      action          t   (inj₂ s) = alg (act action t)
      timestamp fork      _               t   (inj₂ s) = t
      timestamp join      _        (t₁ , t₂)  (inj₂ s) = alg (merge t₁ t₂)
      timestamp init      _               _   (inj₂ s) = alg start
      timestamp (perm σ)  _               ts  (inj₂ s) = timestamped ts (Sites.‵index (Sites.‵sym σ) s)
