{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock.Interpret2 where
  open import Function
    using (_∘_)
  open import Data.Product
    using ()
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

  open import Data.Unit
    using (⊤)
  open import Data.Product
    using (_×_)

  infix 5 _↦_

  Instance : Type → Tree ⊤ → Type
  Instance τ Tree.∅ = ⊤
  Instance τ (Tree.leaf _) = τ
  Instance τ (x ∗ y) = Instance τ x × Instance τ y

  _↦_ : Tree (Tree ⊤) → Type → Type
  Γ ↦ τ = (s : Site Γ) → Instance τ (Sites.lookup s)


  variable
    Action State : Type
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree ⊤)

  par : (Γ₁ ↦ State) → (Γ₂ ↦ State) → (Γ₁ ∗ Γ₂ ↦ State)
  par f g (Sites.thereˡ _ ix) = f ix
  par f g (Sites.thereʳ _ ix) = g ix

  left : (Γ₁ ∗ Γ₂ ↦ State) → (Γ₁ ↦ State)
  left f = f ∘ Sites.thereˡ _

  right : (Γ₁ ∗ Γ₂ ↦ State) → (Γ₂ ↦ State)
  right f = f ∘ Sites.thereʳ _

  _⊗_ : ((Γ₁      ↦ State) → (Γ₂      ↦ State))
      → ((     Γ₃ ↦ State) → (     Γ₄ ↦ State))
      → ((Γ₁ ∗ Γ₃ ↦ State) → (Γ₂ ∗ Γ₄ ↦ State))
  (f ⊗ g) x = par (f (left x)) (g (right x))

  data Step (Action State : Type) : Type where
    act   : Action → State → Step Action State
    merge : State  → State → Step Action State

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ (alg : Step Action State → State) where
    apply : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) (acts : Tick exec → Action)
          → ((Γ₁ ↦ State) → (Γ₂ ↦ State))
    apply  id   acts   = Function.id
    apply (perm σ) _ f = f ∘ {!Sites.‵index (Sites.‵sym σ)!}
    apply  fork    _ f = {!Function.const (f Sites.here)!}
    apply  tick acts f = {!Function.const (alg (act (acts _) (f Sites.here)))!}
    apply  join    _ f = {!Function.const (alg (merge (f (Sites.thereˡ _ Sites.here))
                                                    (f (Sites.thereʳ _ Sites.here)) ))!}
    apply (  left ∥  right) acts = apply left   (acts ∘ inj₁) ⊗ apply right  (acts ∘ inj₂)
    apply (prefix ⟫ suffix) acts = apply suffix (acts ∘ inj₂) ∘ apply prefix (acts ∘ inj₁)

    timestamp : {exec : Γ₁ ⇶ Γ₂}
              → (Tick exec → Action)
              → (Γ₁ ↦ State)
              → (Event exec → State)
    timestamp acts init (t , s) = apply (HB.before[ t ]) (acts ∘ HB.tliftˡ t) init s
