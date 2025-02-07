<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
module Execution.Cut where
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
    using (_×_; _,_; ∃-syntax; ∃₂)
  open import Function
    as Function
    using (_∘_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; site; _∗_)
    using (Tree[_]; lookup; permute; repeat)
  open import Execution.Core
    using (_⇶_; _∥_; _⟫_; tick; fork; join; init; term; perm; Event)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  variable
    T : Type
    -- Sets of sites over which executions act
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree
```

</details>

```agda
  data Label : Type where
    Before After : Label

  _≤_ : Label → Label → Type
  Before ≤ Before = ⊤
  Before ≤ After = ⊤
  After ≤ Before = ⊥
  After ≤ After = ⊤

  _≤'_ : {Γ : Tree} → (_ _ : Tree[ Γ ] Label) → Type
  _≤'_ {Γ = ∅} l₁ l₂ = ⊤
  _≤'_ {Γ = site} l₁ l₂ = l₁ ≤ l₂
  _≤'_ {Γ = Γ₁ ∗ Γ₂} (l₁₁ , l₁₂) (l₂₁ , l₂₂) = (l₁₁ ≤' l₂₁) × (l₁₂ ≤' l₂₂)

  -- This isn't exactly a functor, since it maps products to either glbs or lubs depending on which side
  -- the product appears on. Is it a profunctor? The interpretation also appears related to
  -- the category of relations, since sequential composition is exactly relational composition.
  --
  -- In any event, Cut' is an ingredient in defining the category of "monotone CSDs",
  -- if we abstract ⟨ Label, ≤ ⟩ to any choice of partial order. A cut is just any monotone labeling
  -- with booleans. If we replace Label with ℕ, we get a whole topographical atlas of cuts; in general,
  -- we can extract cuts from a labeled CSD with just a monotone function on those labels.
  Cut' : {Γ₁ Γ₂ : Tree} → (Γ₁ ⇶ Γ₂) → (Tree[ Γ₁ ] Label → Tree[ Γ₂ ] Label → Type)
  Cut' (x₁ ∥ x₂) (l₁₁ , l₂₁) (l₁₂ , l₂₂) = Cut' x₁ l₁₁ l₁₂ × Cut' x₂ l₂₁ l₂₂
  Cut' (x₁ ⟫ x₂) l₁          l₂          = ∃[ lₘ ] (Cut' x₁ l₁ lₘ × Cut' x₂ lₘ l₂)
  Cut' tick      l₁          l₂          = l₁  ≤ l₂
  Cut' fork      l₁          (l₂₁ , l₂₂) = l₁  ≤ l₂₁ × l₁  ≤ l₂₂
  Cut' join      (l₁₁ , l₁₂) l₂          = l₁₁ ≤ l₂  × l₁₂ ≤ l₂
  Cut' init      _           _           = ⊤
  Cut' term      _           _           = ⊤
  Cut' (perm σ)  l₁          l₂          = permute σ l₁ ≡ l₂

  Cut : {Γ₁ Γ₂ : Tree} → (Γ₁ ⇶ Γ₂) → Type
  Cut exec = ∃₂ (Cut' exec)

  Foo : {Γ₁ Γ₂ : Tree} (l₁ : Tree[ Γ₁ ] Label) (l₂ : Tree[ Γ₂ ] Label)
      → (exec : Γ₁ ⇶ Γ₂) → (c : Cut' exec l₁ l₂)
      → (Event exec → Label)
  Foo (l₁ , _) (l₂ , _) (x ∥ _) (c , _) (inj₁ e) = Foo l₁ l₂ x c e
  Foo (_ , l₁) (_ , l₂) (_ ∥ x) (_ , c) (inj₂ e) = Foo l₁ l₂ x c e
  Foo l₁ l₂ (x₁ ⟫ x₂) (lₘ , c₁ , c₂) (inj₁ e) = Foo l₁ lₘ x₁ c₁ e
  Foo l₁ l₂ (x₁ ⟫ x₂) (lₘ , c₁ , c₂) (inj₂ e) = Foo lₘ l₂ x₂ c₂ e
  Foo l₁ l₂ tick c (inj₁ _) = l₁
  Foo l₁ l₂ tick c (inj₂ _) = l₂
  Foo l₁ l₂ fork c (inj₁ _) = l₁
  Foo l₁ (l₂ , _) fork c (inj₂ (Sites.thereˡ _ _)) = l₂
  Foo l₁ (_ , l₂) fork c (inj₂ (Sites.thereʳ _ _)) = l₂
  Foo (l₁ , _) l₂ join c (inj₁ (Sites.thereˡ _ _)) = l₁
  Foo (_ , l₁) l₂ join c (inj₁ (Sites.thereʳ _ _)) = l₁
  Foo l₁ l₂ join c (inj₂ _) = l₂
  Foo l₁ l₂ init c e = l₂
  Foo l₁ l₂ term c e = l₁
  Foo l₁ l₂ (perm σ) c (inj₁ s) = lookup l₁ s
  Foo l₁ l₂ (perm σ) c (inj₂ s) = lookup l₂ s

  cut-⊥ : {Γ₁ Γ₂ : Tree} (exec : Γ₁ ⇶ Γ₂) → Cut' exec (repeat _ After) (repeat _ After)
  cut-⊥ (x₁ ∥ x₂) = (cut-⊥ x₁ , cut-⊥ x₂)
  cut-⊥ (x₁ ⟫ x₂) = (repeat _ After , cut-⊥ x₁ , cut-⊥ x₂)
  cut-⊥ tick = tt
  cut-⊥ fork = (tt , tt)
  cut-⊥ join = (tt , tt)
  cut-⊥ init = tt
  cut-⊥ term = tt
  cut-⊥ (perm σ) = Eq.sym (Sites.permute-tabulate σ (λ _ → After))

  -- 
{-
  dependencies : {Γ₁ Γ₂ : Tree (Tree T)} {x : Γ₁ ⇶ Γ₂}
               → (e₁ e₂ : Event x)  → Event x → Label
  dependencies {x = x₁ ∥ x₂} (inj₁ e) (l₁ , l₂) = (dependencies e l₁ , repeat After _)
  dependencies {x = x₁ ∥ x₂} (inj₂ e) (l₁ , l₂) = (repeat After _ , dependencies e l₂)
  dependencies {x = x₁ ⟫ x₂} e = {!!}
  dependencies {x = tick} e = {!!}
  dependencies {x = fork} e = {!!}
  dependencies {x = join} e = {!!}
  dependencies {x = init} e = {!!}
  dependencies {x = term} e = {!!}
  dependencies {x = perm σ} e = {!!}

  downcut : {Γ₁ Γ₂ : Tree (Tree T)} (exec : Γ₁ ⇶ Γ₂)
          → (e : Event exec) → Cut' exec (dependencies e) {!!}
  downcut (x₁ ∥ x₂) (inj₁ e) = {!downcut x₁ e!}
  downcut (x₁ ∥ x₂) (inj₂ y) = {!!}
  downcut (x₁ ⟫ x₂) e = {!!}
  downcut tick e = {!!}
  downcut fork e = {!!}
  downcut join e = {!!}
  downcut init e = {!!}
  downcut term e = {!!}
  downcut (perm σ) e = {!!}
-}
```
