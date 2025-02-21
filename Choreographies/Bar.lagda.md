<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
open import Relation.Binary using (DecidableEquality)

module Choreographies.Bar {Loc : Type} {_≟_ : DecidableEquality Loc} where
```

<details>
<summary>Imports, variables, and fixity</summary>

```agda
  open import Function
    using (_∘_)
  open import Data.Unit
    using (⊤; tt)
  open import Data.Empty
    using (⊥)
  open import Data.Product
    using (_×_; _,_; ∃-syntax)
  open import Data.Sum
    using (_⊎_)
  open import Data.Nat
    using (ℕ)
  open import Data.Bool
    using (Bool; true; false; if_then_else_)
  open import Data.Maybe
    as Maybe
    using (Maybe; fromMaybe)
    renaming (just to some; nothing to none)
  open import Data.These
    using (These; this; that; these)
  open import Data.List
    using (List; []; _∷_; [_])
  open import Relation.Nullary.Negation
    using (¬_)
  open import Relation.Nullary.Decidable
    using (Dec; does; _because_; yes; no; _⊎-dec_)
  open import Data.List.Membership.DecPropositional _≟_
    using (_∈?_)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  infixl 25 _⊗_
  infixl 24 _⊕_
  infix  23 _＠_
  infixl 22 _∗_
  infix  21 _+_
  infix  20 _⇶_
```
</details>

```agda
  data Ty : Type where
    𝟙 : Ty
    _⊗_ : Ty → Ty → Ty
    _⊕_ : Ty → Ty → Ty

  ⟦_⟧ : Ty → Type
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ τ₁ ⊗ τ₂ ⟧ = ⟦ τ₁ ⟧ × ⟦ τ₂ ⟧
  ⟦ τ₁ ⊕ τ₂ ⟧ = ⟦ τ₁ ⟧ ⊎ ⟦ τ₂ ⟧

  _⟶_ : Ty → Ty → Type
  τ₁ ⟶ τ₂ = ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧


  data ChoreoHeap : Type where
    ∅    : ChoreoHeap
    _＠_ : Ty → Loc → ChoreoHeap
    _∗_  : (_ _ : ChoreoHeap) → ChoreoHeap
    _+_  : (_ _ : ChoreoHeap) → ChoreoHeap

  variable
    Γ  Γ₁  Γ₂  Γ₃  : ChoreoHeap
    Γ' Γ₁' Γ₂' Γ₃' : ChoreoHeap

  data _⇶_ : (_ _ : ChoreoHeap) → Type where
    id : ∀ Γ → Γ ⇶ Γ

    -- concurrent composition over products
    _∥_ : (Γ₁       ⇶ Γ₂      )
        → (     Γ₁' ⇶      Γ₂')
        → (Γ₁ ∗ Γ₁' ⇶ Γ₂ ∗ Γ₂')

    -- concurrent composition over sums
    _◇_ : (Γ₁       ⇶ Γ₂)
        → (     Γ₁' ⇶ Γ₂)
        → (Γ₁ + Γ₁' ⇶ Γ₂)

    -- sequential composition
    _;_ : (x₁ : Γ₁ ⇶ Γ₂)
        → (x₂ : Γ₂ ⇶ Γ₃)
        → (Γ₁ ⇶ Γ₃)

    -- a local computation at a site
    locally : ∀{a b} l → (a ⟶ b) → ((a ＠ l) ⇶ (b ＠ l))
    -- transferrence of state between chroreographic locations
    transmit : ∀{a} l₁ l₂ → (a ＠ l₁) ⇶ (a ＠ l₂)

    -- the creation of a site
  --init : ∀ l → ∅ ⇶ (𝟙 ＠ l)
    -- the destruction of a site
  --term : ∀ l → (𝟙 ＠ l) ⇶ ∅

    -- the factorization of one site into two
    fork : ∀ l a b → (a ⊗ b ＠ l) ⇶ (a ＠ l ∗ b ＠ l)
    -- the assimilation of two sites into one
    join : ∀ l a b → (a ＠ l) ∗ (b ＠ l) ⇶ (a ⊗ b ＠ l)

    -- the superposition of one site in two possibilities
    branch : ∀ l a b → (a ⊕ b ＠ l) ⇶ (a ＠ l + b ＠ l)
    -- products can distribute over sums
    distrib : (Γ₁ + Γ₂ ∗ Γ₃) ⇶ ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃))
    -- distrib⁻¹ : ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃)) ⇶ (Γ₁ + Γ₂ ∗ Γ₃)

    -- permutations on sites
    swap    : ∀ Γ₁ Γ₂    → (Γ₁ ∗ Γ₂) ⇶ (Γ₂ ∗ Γ₁)
    assoc   : ∀ Γ₁ Γ₂ Γ₃ → ((Γ₁ ∗  Γ₂) ∗ Γ₃ ) ⇶ ( Γ₁ ∗ (Γ₂  ∗ Γ₃))
    assoc⁻¹ : ∀ Γ₁ Γ₂ Γ₃ → ( Γ₁ ∗ (Γ₂  ∗ Γ₃)) ⇶ ((Γ₁ ∗  Γ₂) ∗ Γ₃ )
  --unitₗ   : ∀ Γ        → (∅ ∗ Γ) ⇶      Γ
  --unitₗ⁻¹ : ∀ Γ        →      Γ  ⇶ (∅ ∗ Γ)


  data NetworkProgram : Type where
    pure : (τ₁ : Ty) → ⟦ τ₁ ⟧ → NetworkProgram
    send : (τ : Ty) (id : ℕ) (payload : ⟦ τ ⟧) → (⊤ → NetworkProgram) → NetworkProgram
    recv : (τ : Ty) (id : ℕ) → (⟦ τ ⟧ → NetworkProgram) → NetworkProgram

  _in:_ : Loc → ChoreoHeap → Type
  self in: ∅        = ⊥
  self in: (τ ＠ l) = l ≡ self
  self in: (Γ ∗ Γ') = self in: Γ ⊎ self in: Γ'
  self in: (Γ + Γ') = self in: Γ ⊎ self in: Γ'

  _in?_ : (l : Loc) → (Γ : ChoreoHeap) → Dec (l in: Γ)
  self in? ∅ = no λ ■ → ■
  self in? (τ ＠ l) = l ≟ self
  self in? (Γ ∗ Γ') = (self in? Γ) ⊎-dec (self in? Γ')
  self in? (Γ + Γ') = (self in? Γ) ⊎-dec (self in? Γ')

  _ddd:_ : ∀{ℓ} {T₁ T₂ : Type ℓ} → Maybe T₁ → Maybe T₂ → Maybe (These T₁ T₂)
  some s ddd: some s' = some (these s s')
  some s ddd: none    = some (this s)
  none   ddd: some s' = some (that s')
  none   ddd: none    = none

  Selector : ChoreoHeap → Type
  Selector ∅ = ⊥
  Selector (_ ＠ _) = ⊤
  Selector (Γ ∗ Γ') = These (Selector Γ) (Selector Γ')
  Selector (Γ + Γ') = These (Selector Γ) (Selector Γ')

  --   Maybe (These (Selector Γ₁) (Selector Γ₁')) × Maybe (These (Selector Γ₂) (Selector Γ₂'))
  -- → (Maybe (Selector Γ₁) × Maybe (Selector Γ₂)) × (Maybe (Selector Γ₁') × Maybe (Selector Γ₂'))
  --
  bbb : {A B : Type} → Maybe (These A B) → (Maybe A × Maybe B)
  bbb (some (this a)) = some a , none
  bbb (some (that b)) = none , some b
  bbb (some (these a b)) = some a , some b
  bbb none = none , none

  Foo : (Γ₁ ⇶ Γ₂) → Maybe (Selector Γ₁) → Maybe (Selector Γ₂) → Type
  Foo (id _) s₁ s₂ = s₁ ≡ s₂
  Foo (x ∥ x') s₁ s₂ =
    let (s₁ , s₁') = bbb s₁ in
    let (s₂ , s₂') = bbb s₂ in
    Foo x s₁ s₂ × Foo x' s₁' s₂'
  Foo (x ◇ x') s₁ s₂ =
    let (s₁ , s₁') = bbb s₁ in
    Foo x s₁ s₂ × Foo x' s₁' s₂
  Foo (x₁ ; x₂) s₁ s₂ =
    ∃[ sₘ ] Foo x₁ s₁ sₘ × Foo x₂ sₘ s₂
  Foo (locally l x) (some s₁) (some s₂) = s₁ ≡ s₂
  Foo (locally l x) (some _) none = ⊥
  Foo (locally l x) none (some _) = ⊥
  Foo (locally l x) none none = ⊥
  Foo (transmit l₁ l₂) s₁ s₂ = ⊤
  Foo (fork l a b) (some s₁) (some s₂) = s₂ ≡ these s₁ s₁
  Foo (fork l a b) (some _) none = ⊥
  Foo (fork l a b) none (some _) = ⊥
  Foo (fork l a b) none none = ⊥
  Foo (join l a b) (some s₁) (some s₂) = s₁ ≡ these s₂ s₂
  Foo (join l a b) (some _) none = ⊥
  Foo (join l a b) none (some _) = ⊥
  Foo (join l a b) none none = ⊥
  Foo (branch l a b) (some s₁) (some s₂) = s₂ ≡ these s₁ s₁
  Foo (branch l a b) (some _) none = ⊥
  Foo (branch l a b) none (some _) = ⊥
  Foo (branch l a b) none none = ⊥
  Foo distrib (some s₁) (some s₂) = {!!}
  Foo distrib (some _) none = {!!}
  Foo distrib none (some _) = {!!}
  Foo distrib none none = {!!}
  Foo (swap Γ₁ Γ₂) s₁ s₂ = {!!}
  Foo (assoc Γ₁ Γ₂ Γ₃) s₁ s₂ = {!!}
  Foo (assoc⁻¹ Γ₁ Γ₂ Γ₃) s₁ s₂ = {!!}

  select : (Γ : ChoreoHeap) → Loc → Maybe (Selector Γ)
  select ∅        self = none
  select (_ ＠ l) self = if does (l ≟ self) then some tt else none
  select (Γ ∗ Γ') self = select Γ self ddd: select Γ' self
  select (Γ + Γ') self = select Γ self ddd: select Γ' self

  Epp : (Γ : ChoreoHeap) → Maybe (Selector Γ) → Ty
  Epp Γ = Maybe.fromMaybe 𝟙 ∘ Maybe.map (go Γ)
    where
      go : (Γ : ChoreoHeap) → Selector Γ → Ty
      go (τ ＠ _)        s     = τ
      go (Γ ∗ Γ') (this  s)    = go Γ s
      go (Γ ∗ Γ') (that    s') =          go Γ' s'
      go (Γ ∗ Γ') (these s s') = go Γ s ⊗ go Γ' s'
      go (Γ + Γ') (this  s)    = go Γ s ⊕ 𝟙
      go (Γ + Γ') (that    s') =      𝟙 ⊕ go Γ' s'
      go (Γ + Γ') (these s s') = go Γ s ⊕ go Γ' s'

{-
  Epp : (Γ : ChoreoHeap) → Loc → Ty
  Epp ∅         self = 𝟙
  Epp (τ ＠ l)  self = if does (l ≟ self) then τ else 𝟙
  Epp (Γ₁ ∗ Γ₂) self with self in? Γ₁ | self in? Γ₂
  ... | true  because _ | true  because _ = Epp Γ₁ self ⊗ Epp Γ₂ self
  ... | true  because _ | false because _ = Epp Γ₁ self
  ... | false because _ | true because  _ = Epp Γ₂ self
  ... | false because _ | false because _ = 𝟙
  Epp (Γ₁ + Γ₂) self = if does (self ∈? ls) then Epp Γ₁ self ⊕ Epp Γ₂ self else 𝟙

  epp : (Γ₁ ⇶ Γ₂) → (l : Loc) → ⟦ Epp Γ₁ l ⟧ → (⟦ Epp Γ₂ l ⟧ → NetworkProgram) → NetworkProgram
  epp (id _) self i k = k i
  epp {Γ₁ = Γ₁ ∗ Γ₁'} {Γ₂ = Γ₂ ∗ Γ₂'} (x  ∥ x') self (i , i') k =
    epp x  self i  λ o  →
    epp x' self i' λ o' →
    k (o , o')
  epp (x  ◇[ ls ] x') self i k with self ∈? ls | i
  ... | yes p | _ = {!!}
  ... | no ¬p | _ = {!!}
  epp (x₁ ; x') l i k = {!!}
  epp (locally l₁ x) l i k = {!!}
  epp (transmit l₁ l₂) l i k = {!!}
  epp (init l₁) l i k = {!!}
  epp (term l₁) l i k = {!!}
  epp (fork l₁ a b) l i k = {!!}
  epp (join l₁ a b) l i k = {!!}
  epp (branch l₁ a b) l i k = {!!}
  epp distrib l i k = {!!}
  epp (swap Γ₁ Γ₂) l i k = {!!}
  epp (assoc Γ₁ Γ₂ Γ₃) l i k = {!!}
  epp (assoc⁻¹ Γ₁ Γ₂ Γ₃) l i k = {!!}
  epp (unitₗ _) l i k = {!!}
  epp (unitₗ⁻¹ _) l i k = {!!}
-}
```
