<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
module Execution.Core where
```

<details>
<summary>Imports, variables, and fixity</summary>

```agda
  open import Data.Empty
    using (⊥)
  open import Data.Unit
    using (⊤; tt)
  open import Data.Sum
    as Sum
    using (_⊎_; inj₁; inj₂)
  open import Data.Product
    as Prod
    using (_×_; _,_)
  open import Function
    as Function
    using (_∘_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; site; _∗_)

  variable
    -- Sets of sites over which executions act
    Γ  Γ₁ Γ₂ Γ₃ Γ₄ : Tree

  infix   5 _⇶_
--infix   6 _∗_
  infixl 15 _⟫_
  infix  20 _∥_
```

</details>

```agda
  data _⇶_ : (Γ₁ Γ₂ : Tree) → Type where
    -- concurrent composition
    _∥_ : (x  : Γ₁ ⇶ Γ₂)
        → (x' : Γ₃ ⇶ Γ₄)
        → (Γ₁ ∗ Γ₃ ⇶ Γ₂ ∗ Γ₄)

    -- sequential composition
    _⟫_ : (x₁ : Γ₁ ⇶ Γ₂)
        → (x₂ : Γ₂ ⇶ Γ₃)
        → (Γ₁ ⇶ Γ₃)

    -- a local computation at a site
    tick : site ⇶ site

    -- the factorization of one site into two
    fork : site ⇶ site ∗ site

    -- the assimilation of two sites into one
    join : site ∗ site ⇶ site

    -- the creation of a site
    init : ∅ ⇶ site

    -- the destruction of a site
    term : site ⇶ ∅

    -- a permutation on sites
    perm : ∀{Γ₁ Γ₂} → (σ : Γ₁ Sites.≅ Γ₂) → (Γ₁ ⇶ Γ₂)

  -- Helpers for extracting the type-level implicits from an execution
  leading[_] : (exec : Γ₁ ⇶ Γ₂) → Tree
  leading[_] {Γ₁ = Γ₁} exec = Γ₁

  trailing[_] : (exec : Γ₁ ⇶ Γ₂) → Tree
  trailing[_] {Γ₂ = Γ₂} exec = Γ₂


  Tick : {Γ₁ Γ₂ : Tree} → (Γ₁ ⇶ Γ₂) → Type
  Tick (x ∥ y)  = Tick x ⊎ Tick y
  Tick (x ⟫ y)  = Tick x ⊎ Tick y
  Tick tick     = ⊤
  Tick fork     = ⊥
  Tick join     = ⊥
  Tick init     = ⊥
  Tick term     = ⊥
  Tick (perm σ) = ⊥

  -- A site at a time.
  Event : {Γ₁ Γ₂ : Tree} → (Γ₁ ⇶ Γ₂) → Type
  Event                (x₁ ∥ x₂)     = Event x₁ ⊎ Event x₂
  Event                (x₁ ⟫ x₂)     = Event x₁ ⊎ Event x₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} tick     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} fork     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} join     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} init     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} term     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} (perm σ) = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
```
