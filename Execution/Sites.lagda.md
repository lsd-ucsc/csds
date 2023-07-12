---
title: Distributed sites
author: Jonathan Castello
date: 2023-01-28
css: ['/styles/styles.css']
---
<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
module Execution.Sites where
```

<details>
<summary>Imports, fixity, and variables</summary>

```agda
  open import Function
    using (_∘_)
  open import Data.Nat
    as ℕ
    using (ℕ)
  open import Data.Nat.Properties
    as ℕ-Prop
    using ()
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  infix 6 _∗_

  variable
    T : Type
```

</details>

```agda
  data Tree (T : Type) : Type where
    ∅    :                   Tree T
    leaf : T      →          Tree T
    _∗_  : Tree T → Tree T → Tree T

  -- Equivalence of trees up to balance and order,
  -- establishing ⟨Tree T / _≅_ , _∗_⟩ as a semigroup.
  data _≅_ {T : Type} : (_ _ : Tree T) → Type where
    _‵∗_     : ∀{a₁ a₂ b₁ b₂} → (a₁ ≅ a₂) → (b₁ ≅ b₂) → ((a₁ ∗ b₁) ≅ (a₂ ∗ b₂))

    ‵trans   : ∀{a b c} → (a ≅ b) → (b ≅ c) → (a ≅ c)
    ‵refl    : ∀ a      → (a ≅ a)
    ‵swap    : ∀ a b    → (a ∗ b) ≅ (b ∗ a)

    ‵assoc   : ∀ a b c  → ((a ∗  b) ∗ c ) ≅ ( a ∗ (b  ∗ c))
    ‵assoc⁻¹ : ∀ a b c  → ( a ∗ (b  ∗ c)) ≅ ((a ∗  b) ∗ c )

    -- These rules additionally make ⟨Tree T / _≅_ , ∅ , _∗_⟩ a monoid.
    --‵unitₗ   : ∀ a → (∅ ∗ a) ≅      a
    --‵unit₁⁻¹ : ∀ a →      a  ≅ (∅ ∗ a)

    --‵unitᵣ   : ∀ a → (a ∗ ∅) ≅  a
    --‵unitᵣ⁻¹ : ∀ a →  a      ≅ (a ∗ ∅)

  syntax ‵trans s₁ s₂ = s₁ ∘≅ s₂

  ‵sym : {a b : Tree T} → (a ≅ b) → (b ≅ a)
  ‵sym (p ‵∗ q)         = ‵sym p ‵∗ ‵sym q
  ‵sym (‵trans   p q)   = ‵trans (‵sym q) (‵sym p)
  ‵sym (‵refl    _)     = ‵refl _
  ‵sym (‵swap    a b)   = ‵swap b a
  ‵sym (‵assoc   a b c) = ‵assoc⁻¹ a b c
  ‵sym (‵assoc⁻¹ a b c) = ‵assoc a b c

  ‶sym : {a b : Tree T} → (p : a ≅ b) → ‵sym (‵sym p) ≡ p
  ‶sym (p ‵∗ q)         = Eq.cong₂ _‵∗_   (‶sym p) (‶sym q)
  ‶sym (‵trans   p q)   = Eq.cong₂ ‵trans (‶sym p) (‶sym q)
  ‶sym (‵refl    _)     = Eq.refl
  ‶sym (‵swap    a b)   = Eq.refl
  ‶sym (‵assoc   a b c) = Eq.refl
  ‶sym (‵assoc⁻¹ a b c) = Eq.refl

  size : Tree T → ℕ
  size Tree.∅              = 0
  size (Tree.leaf atom)    = 1
  size (left Tree.∗ right) = size left ℕ.+ size right

  ‵size : ∀{a b : Tree T} → (a ≅ b) → (size a ≡ size b)
  ‵size (p ‵∗ q)         = Eq.cong₂ ℕ._+_ (‵size p) (‵size q)
  ‵size (‵trans   p q)   = Eq.trans (‵size p) (‵size q)
  ‵size (‵refl    _)     = Eq.refl
  ‵size (‵swap    a b)   = ℕ-Prop.+-comm (size a) (size b)
  ‵size (‵assoc   a b c) =         ℕ-Prop.+-assoc (size a) (size b) (size c)
  ‵size (‵assoc⁻¹ a b c) = Eq.sym (ℕ-Prop.+-assoc (size a) (size b) (size c))


  data Site {T : Type} : Tree T → Type where
    here   : ∀{a}    →                  Site (leaf a)
    thereˡ : ∀{l} r  → (ixˡ : Site l) → Site (l ∗ r)
    thereʳ : ∀ l {r} → (ixʳ : Site r) → Site (l ∗ r)

  module _ where
    ‵index : {Γ₁ Γ₂ : Tree T}
           → (Γ₁ ≅ Γ₂)
           → Site Γ₁ → Site Γ₂

    ‵index (p ‵∗ q) (thereˡ _ ix) = thereˡ _ (‵index p ix)
    ‵index (p ‵∗ q) (thereʳ _ ix) = thereʳ _ (‵index q ix)

    ‵index (‵trans   p q) = ‵index q Function.∘ ‵index p
    ‵index (‵refl    _)   = Function.id

    ‵index (‵swap    _ _) (thereˡ _ ix) = thereʳ _ ix
    ‵index (‵swap    _ _) (thereʳ _ ix) = thereˡ _ ix

    ‵index (‵assoc   a b c) (thereˡ _ (thereˡ _ ix)) = thereˡ _           ix
    ‵index (‵assoc   a b c) (thereˡ _ (thereʳ _ ix)) = thereʳ _ (thereˡ _ ix)
    ‵index (‵assoc   a b c) (thereʳ _           ix ) = thereʳ _ (thereʳ _ ix)

    ‵index (‵assoc⁻¹ a b c) (thereˡ _           ix ) = thereˡ _ (thereˡ _ ix)
    ‵index (‵assoc⁻¹ a b c) (thereʳ _ (thereˡ _ ix)) = thereˡ _ (thereʳ _ ix)
    ‵index (‵assoc⁻¹ a b c) (thereʳ _ (thereʳ _ ix)) = thereʳ _ ix

  module _ where
    ‶index : {Γ₁ Γ₂ : Tree T} (p : Γ₁ ≅ Γ₂)
           → (ix : Site Γ₁)
           → (‵index (‵sym p) ∘ ‵index p) ix ≡ ix

    ‶index (p ‵∗ _) (thereˡ _ ix) = Eq.cong (thereˡ _) (‶index p ix)
    ‶index (_ ‵∗ q) (thereʳ _ ix) = Eq.cong (thereʳ _) (‶index q ix)

    ‶index (‵trans p q) ix = Eq.trans (Eq.cong (‵index (‵sym p)) (‶index q (‵index p ix)))
                                      (‶index p ix)

    ‶index (‵refl _) _ = Eq.refl

    ‶index (‵swap _ _) (thereˡ _ _) = Eq.refl
    ‶index (‵swap _ _) (thereʳ _ _) = Eq.refl

    ‶index (‵assoc _ _ _) (thereˡ _ (thereˡ _ _)) = Eq.refl
    ‶index (‵assoc _ _ _) (thereˡ _ (thereʳ _ _)) = Eq.refl
    ‶index (‵assoc _ _ _) (thereʳ _           _ ) = Eq.refl

    ‶index (‵assoc⁻¹ _ _ _) (thereˡ _           _ ) = Eq.refl
    ‶index (‵assoc⁻¹ _ _ _) (thereʳ _ (thereˡ _ _)) = Eq.refl
    ‶index (‵assoc⁻¹ _ _ _) (thereʳ _ (thereʳ _ _)) = Eq.refl

  lookup : {Γ : Tree T} → Site Γ → T
  lookup (here {a})   = a
  lookup (thereˡ _ x) = lookup x
  lookup (thereʳ _ x) = lookup x

  module _ where
    ‵lookup : {Γ₁ Γ₂ : Tree T} (p : Γ₁ ≅ Γ₂)
            → (ix : Site Γ₁)
            → lookup ix ≡ lookup (‵index p ix)

    ‵lookup (p ‵∗ _) (thereˡ _ ix) = ‵lookup p ix
    ‵lookup (_ ‵∗ q) (thereʳ _ ix) = ‵lookup q ix

    ‵lookup (‵trans p q) ix = Eq.trans (‵lookup p ix)
                                       (‵lookup q (‵index p ix))

    ‵lookup (‵refl _) _ = Eq.refl

    ‵lookup (‵swap _ _) (thereˡ _ _) = Eq.refl
    ‵lookup (‵swap _ _) (thereʳ _ _) = Eq.refl

    ‵lookup (‵assoc _ _ _) (thereˡ _ (thereˡ _ _)) = Eq.refl
    ‵lookup (‵assoc _ _ _) (thereˡ _ (thereʳ _ _)) = Eq.refl
    ‵lookup (‵assoc _ _ _) (thereʳ _           _ ) = Eq.refl

    ‵lookup (‵assoc⁻¹ _ _ _) (thereˡ _           _ ) = Eq.refl
    ‵lookup (‵assoc⁻¹ _ _ _) (thereʳ _ (thereˡ _ _)) = Eq.refl
    ‵lookup (‵assoc⁻¹ _ _ _) (thereʳ _ (thereʳ _ _)) = Eq.refl
```
