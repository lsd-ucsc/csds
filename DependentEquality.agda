{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using (Level) renaming (Set to Type)

module DependentEquality where
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

  -- An equality between terms of two different types,
  -- parameterized by a proof that their types are propositionally equal after all.
  --
  -- This is obviously different from standard homogeneous equality,
  -- but it's also somehow different from the usual heterogeneous ("John Major") equality.
  _≡[_]_ : {A B : Type ℓ}
         → (a : A)
         → (σ : A ≡ B)
         → (b : B)
         → Type ℓ
  a ≡[ Eq.refl ] b = a ≡ b

  -- Apply a homotopy (an equality of equalities).
  hom : {A B : Type ℓ}
      → {a : A}
      → {b : B}
      → {σ τ : A ≡ B}
      → (σ≡τ : σ ≡ τ)
      → a ≡[ σ ] b
      → a ≡[ τ ] b
  hom Eq.refl p = p

  -- Follow an equality backwards.
  sym : {A B : Type ℓ}
      → {a : A}
      → {b : B}
      → (σ : A ≡ B)
      → a ≡[        σ ] b
      → b ≡[ Eq.sym σ ] a
  sym Eq.refl = Eq.sym

  -- Concatenate two equalities by chaining paths along their types.
  trans : {A B C : Type ℓ}
        → {a : A}
        → {b : B}
        → {c : C}
        → (σ : A ≡ B)
        → (τ : B ≡ C)
        → a ≡[ σ ] b
        → b ≡[ τ ] c
        → a ≡[ Eq.trans σ τ ] c
  trans Eq.refl Eq.refl = Eq.trans

  -- Apply a dependent function on both sides of an equality.
  cong : {I :     Type ℓ₁}
       → {A : I → Type ℓ₂}
       → {B : I → Type ℓ₃}
       → {i₁ : I} {x : A i₁}
       → {i₂ : I} {y : A i₂}
       → (f : (z : I) → A z → B z)
       → (σ : i₁ ≡ i₂)
       → (     x ≡[ Eq.cong A σ ]      y)
       → (f i₁ x ≡[ Eq.cong B σ ] f i₂ y)
  cong _ Eq.refl Eq.refl = Eq.refl
