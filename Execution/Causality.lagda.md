<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
module Execution.Causality where
```

<details>
<summary>Imports, fixity, and variables</summary>

```agda
  open import Data.Empty
    using (⊥)
  open import Data.Unit
    using (⊤; tt)
  open import Data.Product
    using (∃-syntax; Σ-syntax; _×_; _,_)
  open import Data.Sum
    using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.Construct.Composition
    as Rel
    using ()
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)
  open import Execution.Sites
    as Tree
    using (Tree; Site; _∗_)
  open import Execution.Core
    using (_⇶_; Event; Tick)
    using (perm; tick; fork; join; init; term; _∥_; _⟫_)

  variable
    T : Type
    Γ₁ Γ₂ Γᵢ : Tree
```

</details>

```agda
  TrailingEvent[_,_] : (exec : Γ₁ ⇶ Γ₂) → Site Γ₁ → Event exec
  TrailingEvent[ x₁ ∥ x₂ , Site.thereˡ _ s ] = inj₁ TrailingEvent[ x₁ , s ]
  TrailingEvent[ x₁ ∥ x₂ , Site.thereʳ _ s ] = inj₂ TrailingEvent[ x₂ , s ]
  TrailingEvent[ x₁ ⟫ x₂ , s ] = inj₁ TrailingEvent[ x₁ , s ]
  TrailingEvent[ tick    , s ] = inj₁ s
  TrailingEvent[ fork    , s ] = inj₁ s
  TrailingEvent[ join    , s ] = inj₁ s
  TrailingEvent[ term    , s ] = inj₁ s
  TrailingEvent[ perm σ  , s ] = inj₁ s

  LeadingEvent[_,_] : (exec : Γ₁ ⇶ Γ₂) → Site Γ₂ → Event exec
  LeadingEvent[ x₁ ∥ x₂ , Site.thereˡ _ s ] = inj₁ LeadingEvent[ x₁ , s ]
  LeadingEvent[ x₁ ∥ x₂ , Site.thereʳ _ s ] = inj₂ LeadingEvent[ x₂ , s ]
  LeadingEvent[ x₁ ⟫ x₂ , s ] = inj₂ LeadingEvent[ x₂ , s ]
  LeadingEvent[ tick    , s ] = inj₂ s
  LeadingEvent[ fork    , s ] = inj₂ s
  LeadingEvent[ join    , s ] = inj₂ s
  LeadingEvent[ init    , s ] = inj₂ s
  LeadingEvent[ perm σ  , s ] = inj₂ s


  -- An interior path between two events within an execution.
  Arr[_] : (exec : Γ₁ ⇶ Γ₂) (e₁ e₂ : Event exec) → Type
  -- Paths through a parallel composition
  Arr[ x₁ ∥ x₂ ] (inj₁ e₁) (inj₁ e₂) = Arr[ x₁ ] e₁ e₂
  Arr[ x₁ ∥ x₂ ] (inj₂ e₁) (inj₂ e₂) = Arr[ x₂ ] e₁ e₂
  Arr[ x₁ ∥ x₂ ] (inj₂ e₁) (inj₁ e₂) = ⊥
  Arr[ x₁ ∥ x₂ ] (inj₁ e₁) (inj₂ e₂) = ⊥
  -- Paths through a sequential composition
  Arr[ x₁ ⟫ x₂ ] (inj₁ e₁) (inj₁ e₂) = Arr[ x₁ ] e₁ e₂
  Arr[ x₁ ⟫ x₂ ] (inj₂ e₁) (inj₂ e₂) = Arr[ x₂ ] e₁ e₂
  Arr[ x₁ ⟫ x₂ ] (inj₂ e₁) (inj₁ e₂) = ⊥
  Arr[ x₁ ⟫ x₂ ] (inj₁ e₁) (inj₂ e₂) =
    ∃[ sₘ ] ( Arr[ x₁ ] e₁ LeadingEvent[ x₁ , sₘ ]
            × Arr[ x₂ ] TrailingEvent[ x₂ , sₘ ] e₂)
  -- Paths through atomic diagrams
  Arr[ tick ] (inj₁ s₁) (inj₁ s₂) = s₁ ≡ s₂
  Arr[ tick ] (inj₂ s₁) (inj₂ s₂) = s₁ ≡ s₂
  Arr[ tick ] (inj₂ s₁) (inj₁ s₂) = ⊥
  Arr[ tick ] (inj₁ s₁) (inj₂ s₂) = ⊤
  --
  Arr[ fork ] (inj₁ s₁) (inj₁ s₂) = s₁ ≡ s₂
  Arr[ fork ] (inj₂ s₁) (inj₂ s₂) = s₁ ≡ s₂
  Arr[ fork ] (inj₂ s₁) (inj₁ s₂) = ⊥
  Arr[ fork ] (inj₁ s₁) (inj₂ s₂) = ⊤
  --
  Arr[ join ] (inj₁ s₁) (inj₁ s₂) = s₁ ≡ s₂
  Arr[ join ] (inj₂ s₁) (inj₂ s₂) = s₁ ≡ s₂
  Arr[ join ] (inj₂ s₁) (inj₁ s₂) = ⊥
  Arr[ join ] (inj₁ s₁) (inj₂ s₂) = ⊤
  --
  Arr[ init ] (inj₁ s₁) (inj₁ s₂) = s₁ ≡ s₂
  Arr[ init ] (inj₂ s₁) (inj₂ s₂) = s₁ ≡ s₂
  Arr[ init ] (inj₂ s₁) (inj₁ s₂) = ⊥
  Arr[ init ] (inj₁ s₁) (inj₂ s₂) = ⊤
  --
  Arr[ term ] (inj₁ s₁) (inj₁ s₂) = s₁ ≡ s₂
  Arr[ term ] (inj₂ s₁) (inj₂ s₂) = s₁ ≡ s₂
  Arr[ term ] (inj₂ s₁) (inj₁ s₂) = ⊥
  Arr[ term ] (inj₁ s₁) (inj₂ s₂) = ⊤
  --
  Arr[ perm σ ] (inj₁ s₁) (inj₁ s₂) = s₁ ≡ s₂
  Arr[ perm σ ] (inj₂ s₁) (inj₂ s₂) = s₁ ≡ s₂
  Arr[ perm σ ] (inj₂ s₁) (inj₁ s₂) = ⊥
  Arr[ perm σ ] (inj₁ s₁) (inj₂ s₂) = Tree.forward σ s₁ ≡ s₂

  _↝_ : {exec : Γ₁ ⇶ Γ₂} → (_ _ : Event exec) → Type
  e₁ ↝ e₂ = Arr[ _ ] e₁ e₂

  start[_] : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Event exec} → (t₁ ↝ t₂) → Event exec
  start[_] {t₁ = t₁} _ = t₁

  end[_] : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Event exec} → (t₁ ↝ t₂) → Event exec
  end[_] {t₂ = t₂} _ = t₂
```
