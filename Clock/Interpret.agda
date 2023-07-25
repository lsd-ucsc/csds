{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock.Interpret where
  open import Function
    using (_∘_)
  open import Data.Unit
    using (⊤)
  open import Data.Product
    using (_×_; _,_; -,_)
  open import Data.Sum
    using (inj₁; inj₂)
  open import Execution.Sites
    as Sites
    using (Tree; Site; _∗_; site)
  open import Execution.Core
    using (perm; tick; fork; join)
    using (_⇶[_]_; _⇶_; id; _∥_; _⟫_)
    using (Cut; Event; Tick)
  open Event
    using ()

  infix 5 _↦_

  Instance : {T : Type} → (T → Type) → (Tree T → Type)
  Instance f Tree.∅ = ⊤
  Instance f (Tree.leaf x) = f x
  Instance f (Γ₁ ∗ Γ₂) = Instance f Γ₁ × Instance f Γ₂

  _↦_ : {T : Type} → Tree (Tree T) → (T → Type) → Type
  Γ ↦ τ = Instance τ (Sites.flatten Γ)

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ {T : Type} {State : T → Type} {Action : Tree T → Tree T → Type} where
    variable
      Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)

    foo : (Γ₁ Sites.≅ Γ₂) → (Γ₁ ↦ State) → (Γ₂ ↦ State)
    foo (Sites.‵refl _) =
      λ f → f
    foo (Sites.‵swap  _ _) =
      λ(f , g) → (g , f)
    foo (Sites.‵assoc _ _ _) =
      λ((f , g) , h) → (f , (g , h))
    foo (Sites.‵cong  σ₁ σ₂) =
      λ(f , g) → (foo σ₁ f , foo σ₂ g)
    foo (Sites.‵trans σ₁ σ₂) =
      foo σ₂ ∘ foo σ₁

    -- A labeling of the `tick`s in an execution.
    Actions : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) → Type
    Actions (perm σ) = ⊤
    Actions (tick {Γ₁} {Γ₂}) = Instance State Γ₁ → Instance State Γ₂
    Actions fork = ⊤
    Actions join = ⊤
    Actions id   = ⊤
    Actions (x ∥ y) = Actions x × Actions y
    Actions (x ⟫ y) = Actions x × Actions y

    apply : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) → Actions exec
          → ((Γ₁ ↦ State) → (Γ₂ ↦ State))
    apply (id)     _ = Function.id
    apply (fork)   _ = Function.id
    apply (join)   _ = Function.id
    apply (perm σ) _ = foo σ
    apply (tick)   a = a
    apply (x ∥ y) (a₁ , a₂) = Data.Product.map (apply x a₁) (apply y a₂)
    apply (x ⟫ y) (a₁ , a₂) = apply y a₂ ∘ apply x a₁

    probe : {exec : Γ₁ ⇶ Γ₂}
          → (t : Execution.Core.Cut.Cut exec)
          → Actions exec
          → (Γ₁ ↦ State)
          → (Execution.Core.Cut.Γ[ t ] ↦ State)
    probe (Cut.now _)       (acts)     = apply _ acts
    probe (Cut.back step t) (acts , _) = probe t acts

    pick : ∀{a} → (a Sites.∈ Γ₁)
         → (Γ₁ ↦ State)
         → Instance State a
    pick (Sites.here)        f      =        f
    pick (Sites.thereˡ _ x) (f , _) = pick x f
    pick (Sites.thereʳ _ x) (_ , f) = pick x f

    timestamp : {exec : Γ₁ ⇶ Γ₂}
              → Actions exec
              → (Γ₁ ↦ State)
              → (t : Event exec)
              → Instance State Event.state[ t ]
    timestamp acts inputs (t Event., s) = pick s (probe t acts inputs)
