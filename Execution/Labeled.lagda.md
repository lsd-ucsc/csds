<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
module Execution.Labeled where
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
    using (_×_; _,_; ∃-syntax; Σ-syntax)
  open import Function
    as Function
    using (_∘_)
  open import Execution.Core
    using (_⇶_; perm; tick; fork; join; init; term; _∥_; _⟫_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; site; _∗_; Tree[_]; permute)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)


  variable
    Γ  Γ₁ Γ₂ Γ₃ Γ₄ : Tree
```

</details>

```agda
  module _ (T : Type) where
    Lol : Type
    Lol = ∃[ Γ ] Tree[ Γ ] T

    Foo : ∀{Γ₁ Γ₂} → (exec : Γ₁ ⇶ Γ₂)
        → (l₁ : Tree[ Γ₁ ] Tree) (l₂ : Tree[ Γ₂ ] Tree) → Type
    Foo (x  ∥ x') (l₁ , l₁') (l₂ , l₂') = Foo x l₁ l₂ × Foo x' l₁' l₂'
    Foo (x₁ ⟫ x₂) l₁ l₂ = ∃[ lₘ ] (Foo x₁ l₁ lₘ × Foo x₂ lₘ l₂)
    Foo tick l₁ l₂ = ⊤
    Foo fork l₁ (l₂ , l₂') = l₁ ≡ (l₂ ∗ l₂')
    Foo join (l₁ , l₁') l₂ = (l₁ ∗ l₁') ≡ l₂
    Foo init l₁ l₂ = ∅ ≡ l₂
    Foo term l₁ l₂ = l₁ ≡ ∅
    Foo (perm σ) l₁ l₂ = permute σ l₁ ≡ l₂

    Foo' : ∀{Γ₁ Γ₂} → (exec : Γ₁ ⇶ Γ₂)
         → (l₁ : Tree[ Γ₁ ] Lol) (l₂ : Tree[ Γ₂ ] Lol) → Type
    Foo' (x  ∥ x') (l₁ , l₁') (l₂ , l₂') = Foo' x l₁ l₂ × Foo' x' l₁' l₂'
    Foo' (x₁ ⟫ x₂) l₁ l₂ = ∃[ lₘ ] (Foo' x₁ l₁ lₘ × Foo' x₂ lₘ l₂)
    Foo' tick l₁ l₂ = ⊤
    Foo' fork (Γ₁ , l₁) ((Γ₂ , l₂) , (Γ₂' , l₂')) = Σ[ p ∈ Γ₁ ≡ (Γ₂ ∗ Γ₂') ] Eq.subst (λ ▢ → Tree[ ▢ ] T) p l₁ ≡ (l₂ , l₂')
    Foo' join ((Γ₁ , l₁) , (Γ₁' , l₁')) (Γ₂ , l₂) = Σ[ p ∈ (Γ₁ ∗ Γ₁') ≡ Γ₂ ] Eq.subst (λ ▢ → Tree[ ▢ ] T) p (l₁ , l₁') ≡ l₂
    Foo' init _ (Γ₂ , _) = ∅ ≡ Γ₂
    Foo' term (Γ₁ , _) _ = Γ₁ ≡ ∅
    Foo' (perm σ) l₁ l₂ = permute σ l₁ ≡ l₂
```
