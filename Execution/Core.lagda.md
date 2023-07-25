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
    using (⊤)
  open import Data.Sum
    using (_⊎_)
  open import Function
    as Function
    using (_∘_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; leaf; _∗_)

  variable
    T : Type
    -- Sets of sites over which executions act
    Γ  Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)

  infix   5 _⇶[_]_ _⇶₁_ _⇶_
--infix   6 _∗_
  infixl 15 _⟫_ _;_
  infix  20 _∥_ _⊗_
```

</details>

```agda
  -- define an indexing type with two values, one for each type we want to combine
  data Layer : Type where
    Par Seq : Layer

  -- forward-declare the type, before we define its constructors
  data _⇶[_]_ {T : Type} : Tree (Tree T) → Layer → Tree (Tree T) → Type

  -- now define aliases for a fixed index
  _⇶₁_ : {T : Type} → Tree (Tree T) → Tree (Tree T) → Type
  _⇶₁_ = _⇶[ Par ]_

  _⇶_ : {T : Type} → Tree (Tree T) → Tree (Tree T) → Type
  _⇶_ = _⇶[ Seq ]_

  data _⇶[_]_ {- signature declared earlier -} where
    -- a permutation on sites
    perm : ∀{a b} → (σ : a Sites.≅ b) → (a ⇶₁ b)

    -- a local computation at a site
    tick : ∀{a b} → leaf a          ⇶₁ leaf b

    -- the factorization of one site into two
    fork : ∀{a b} → leaf (a ∗ b)    ⇶₁ leaf a ∗ leaf b

    -- the assimilation of two sites into one
    join : ∀{a b} → leaf a ∗ leaf b ⇶₁ leaf (a ∗ b)

    -- We don't need these yet.
    ---- the creation of an empty site
    --init :                        ∅ ⇶₁ leaf ∅
    ---- the destruction of an empty site
    --term :                   leaf ∅ ⇶₁      ∅

    -- concurrently compose two groups of concurrent steps
    _∥_ : (Γ₁ ⇶₁ Γ₂)
        → (Γ₃ ⇶₁ Γ₄)
        → (Γ₁ ∗ Γ₃ ⇶₁ Γ₂ ∗ Γ₄)

    -- an empty sequence of groups of concurrent steps
    id : Γ ⇶ Γ
    -- sequentially append a group of concurrent steps
    _⟫_ : (Γ₁ ⇶  Γ₂)
        → (Γ₂ ⇶₁ Γ₃)
        → (Γ₁ ⇶  Γ₃)

  -- Helpers for extracting the type-level implicits from an execution
  Ty[_] : ∀{k} {T : Type} {Γ₁ Γ₂ : Tree (Tree T)} (exec : Γ₁ ⇶[ k ] Γ₂) → Type
  Ty[_] {T = T} exec = T

  leading[_] : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) → Tree (Tree Ty[ exec ])
  leading[_] {Γ₁ = Γ₁} exec = Γ₁

  trailing[_] : ∀{k} (exec : Γ₁ ⇶[ k ] Γ₂) → Tree (Tree Ty[ exec ])
  trailing[_] {Γ₂ = Γ₂} exec = Γ₂


  pad : (Γ : Tree (Tree T)) → (Γ ⇶₁ Γ)
  pad = perm ∘ Sites.‵refl

  _;_ : (Γ₁ ⇶ Γ₂) → (Γ₂ ⇶ Γ₃) → (Γ₁ ⇶ Γ₃)
  prefix ; id              =  prefix
  prefix ; (suffix ⟫ step) = (prefix ; suffix) ⟫ step

  _⊗_ : (Γ₁ ⇶ Γ₂) → (Γ₃ ⇶ Γ₄) → (Γ₁ ∗ Γ₃ ⇶ Γ₂ ∗ Γ₄)
  id                ⊗ id                = id
  id                ⊗ (prefix₂ ⟫ step₂) = (id      ⊗ prefix₂) ⟫ (pad _ ∥ step₂)
  (prefix₁ ⟫ step₁) ⊗ id                = (prefix₁ ⊗ id)      ⟫ (step₁ ∥ pad _)
  (prefix₁ ⟫ step₁) ⊗ (prefix₂ ⟫ step₂) = (prefix₁ ⊗ prefix₂) ⟫ (step₁ ∥ step₂)


  Tick : ∀{T : Type} {k} → {Γ₁ Γ₂ : Tree (Tree T)} → (Γ₁ ⇶[ k ] Γ₂) → Type
  -- ⇶₁
  Tick (perm σ) = ⊥
  Tick tick     = ⊤
  Tick fork     = ⊥
  Tick join     = ⊥
  Tick (x ∥ y)  = Tick x ⊎ Tick y
  -- ⇶
  Tick id      = ⊥
  Tick (x ⟫ y) = Tick x ⊎ Tick y

  module Cut where
    data Cut {T : Type} {Γ₁ Γ₂ : Tree (Tree T)} : (Γ₁ ⇶ Γ₂) → Type where
      now : (exec : Γ₁ ⇶ Γ₂)
          → Cut exec

      back : ∀{Γᵢ} {prefix : Γ₁ ⇶ Γᵢ}
           → (step : Γᵢ ⇶₁ Γ₂)
           → Cut prefix
           → Cut (prefix ⟫ step)

    Γ[_] : {exec : Γ₁ ⇶ Γ₂} → Cut exec → Tree (Tree Ty[ exec ])
    Γ[ Cut.now exec ] = trailing[ exec ]
    Γ[ Cut.back _ t ] = Γ[ t ]

    _∈_ : {exec : Γ₁ ⇶ Γ₂} → Tree Ty[ exec ] → Cut exec → Type
    a ∈ c = a Sites.∈ Γ[ c ]

    Site : {exec : Γ₁ ⇶ Γ₂} → Cut exec → Type
    Site c = Sites.Site Γ[ c ]
  Cut = Cut.Cut

  -- A site at a time.
  module Event where
    record Event (exec : Γ₁ ⇶ Γ₂) : Type where
      constructor _,_
      field {state[_]} : Tree Ty[ exec ]
      field cut[_]     : Cut exec
      field index[_]   : state[_] Cut.∈ cut[_]

      site[_] : Cut.Site cut[_]
      site[_] = Sites.site index[_]

    open Event public

    open import Relation.Binary.PropositionalEquality
      as Eq
      using (_≡_)
    open import DependentEquality
      using (_≡[_]_)

    -- With deepest gratitude to an archived Reddit comment by Jannis Limperg.
    -- https://old.reddit.com/r/agda/comments/ax9rnx/help_with_equality_of_dependent_records/ehu86iv/
    eq : {exec : Γ₁ ⇶ Γ₂}
       → {a b : Tree T}
       → {t₁ t₂ : Cut exec}
       → {s₁    : a Cut.∈ t₁ }
       → {   s₂ : b Cut.∈ t₂ }
       → (a  ≡ b )
       → (t₁ ≡ t₂)
       → (z : (x : a ≡ b) → (y : t₁ ≡ t₂) → (s₁ ≡[ Eq.cong₂ Cut._∈_ x y ] s₂))
       → (t₁ , s₁) ≡ (t₂ , s₂)
    eq x@Eq.refl y@Eq.refl f = Eq.cong (λ ▢ → (_ , ▢)) (f x y)
  Event = Event.Event
```
