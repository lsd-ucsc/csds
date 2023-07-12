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
    using (perm; tick; fork; join)
    using (_⇶[_]_; _⇶_; id; _∥_; _⟫_)
    using (Event; Tick)
  open import Execution.Causality
    as HB
    using ()
  open Event
    using (_,_)

  variable
    T : Type
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)
    Action State : Type

  Valuation : Type → Tree (Tree T) → Type
  Valuation State Γ = Site Γ → State

  par : Valuation State Γ₁ → Valuation State Γ₂ → Valuation State (Γ₁ ∗ Γ₂)
  par f g (Site.thereˡ _ ix) = f ix
  par f g (Site.thereʳ _ ix) = g ix

  left : Valuation State (Γ₁ ∗ Γ₂) → Valuation State Γ₁
  left f = f ∘ Site.thereˡ _

  right : Valuation State (Γ₁ ∗ Γ₂) → Valuation State Γ₂
  right f = f ∘ Site.thereʳ _

  _⊗_ : (Valuation State Γ₁        → Valuation State Γ₂       )
      → (Valuation State       Γ₃  → Valuation State       Γ₄ )
      → (Valuation State (Γ₁ ∗ Γ₃) → Valuation State (Γ₂ ∗ Γ₄))
  (f ⊗ g) x = par (f (left x)) (g (right x))

  data Step (Action State : Type) : Type where
    act   : Action → State → Step Action State
    merge : State  → State → Step Action State

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ (alg : Step Action State → State) where
    apply : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) (acts : Tick exec → Action)
          → (Valuation State Γ₁ → Valuation State Γ₂)
    apply  id   acts   = Function.id
    apply (perm σ) _ f = f ∘ Sites.‵index (Sites.‵sym σ)
    apply  fork    _ f = Function.const (f Site.here)
    apply  tick acts f = Function.const (alg (act (acts _) (f Site.here)))
    apply  join    _ f = Function.const (alg (merge (f (Site.thereˡ _ Site.here))
                                                    (f (Site.thereʳ _ Site.here)) ))
    apply (  left ∥  right) acts = apply left   (acts ∘ inj₁) ⊗ apply right  (acts ∘ inj₂)
    apply (prefix ⟫ suffix) acts = apply suffix (acts ∘ inj₂) ∘ apply prefix (acts ∘ inj₁)

    timestamp : {exec : Γ₁ ⇶ Γ₂}
              → (Tick exec → Action)
              → Valuation State Γ₁
              → (Event exec → State)
    timestamp acts init (t , s) = apply (HB.before[ t ]) (acts ∘ HB.tliftˡ t) init s
