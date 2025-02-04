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
    using (Tree; ∅; leaf; _∗_)

  variable
    T : Type
    -- Sets of sites over which executions act
    Γ  Γ₁ Γ₂ Γ₃ Γ₄ : Tree (Tree T)

  infix   5 _⇶_ _⇶[_]_
--infix   6 _∗_
  infixl 15 _⟫_ _;_
  infix  20 _∥_ _⊗_
```

</details>

```agda
  data _⇶_ {T : Type} : (Γ₁ Γ₂ : Tree (Tree T)) → Type where
    -- concurrent composition
    _∥_ : (Γ₁ ⇶ Γ₂)
        → (Γ₃ ⇶ Γ₄)
        → (Γ₁ ∗ Γ₃ ⇶ Γ₂ ∗ Γ₄)

    -- sequential composition
    _⟫_ : (Γ₁ ⇶ Γ₂)
        → (Γ₂ ⇶ Γ₃)
        → (Γ₁ ⇶ Γ₃)

    -- a local computation at a site
    tick : ∀{a b} → leaf a          ⇶ leaf b

    -- the factorization of one site into two
    fork : ∀{a b} → leaf (a ∗ b)    ⇶ leaf a ∗ leaf b

    -- the assimilation of two sites into one
    join : ∀{a b} → leaf a ∗ leaf b ⇶ leaf (a ∗ b)

    -- the creation of an empty site
    init :                        ∅ ⇶ leaf ∅

    -- the destruction of an empty site
    term :                   leaf ∅ ⇶      ∅

    -- a permutation on sites
    perm : ∀{a b} → (σ : a Sites.≅ b) → (a ⇶ b)

  -- Helpers for extracting the type-level implicits from an execution
  Ty[_] : {T : Type} {Γ₁ Γ₂ : Tree (Tree T)} (exec : Γ₁ ⇶ Γ₂) → Type
  Ty[_] {T = T} exec = T

  leading[_] : (exec : Γ₁ ⇶ Γ₂) → Tree (Tree Ty[ exec ])
  leading[_] {Γ₁ = Γ₁} exec = Γ₁

  trailing[_] : (exec : Γ₁ ⇶ Γ₂) → Tree (Tree Ty[ exec ])
  trailing[_] {Γ₂ = Γ₂} exec = Γ₂


  data Layer : Type where
    Permute : Layer
    Compute : Layer

  _⇶[_]_ : {T : Type} (Γ₁ : Tree (Tree T)) (k : Layer) (Γ₂ : Tree (Tree T)) → Type
  Γ₁ ⇶[ Permute ] Γ₂ = Γ₁ Sites.≅ Γ₂
  Γ₁ ⇶[ Compute ] Γ₂ = Γ₁ ⇶ Γ₂

  id : ∀{k} → (Γ : Tree (Tree T)) → (Γ ⇶[ k ] Γ)
  id {k = Permute} = Sites.‵refl
  id {k = Compute} = perm ∘ id

  _;_ : ∀{k} → (Γ₁ ⇶[ k ] Γ₂) → (Γ₂ ⇶[ k ] Γ₃) → (Γ₁ ⇶[ k ] Γ₃)
  _;_ {k = Permute} = Sites.‵trans
  _;_ {k = Compute} = _⟫_

  _⊗_ : ∀{k} → (Γ₁ ⇶[ k ] Γ₂) → (Γ₃ ⇶[ k ] Γ₄) → (Γ₁ ∗ Γ₃ ⇶[ k ] Γ₂ ∗ Γ₄)
  _⊗_ {k = Permute} = Sites._‵∗_
  _⊗_ {k = Compute} = _∥_


  Tick : {T : Type} {Γ₁ Γ₂ : Tree (Tree T)} → (Γ₁ ⇶ Γ₂) → Type
  Tick (x ∥ y)  = Tick x ⊎ Tick y
  Tick (x ⟫ y)  = Tick x ⊎ Tick y
  Tick tick     = ⊤
  Tick fork     = ⊥
  Tick join     = ⊥
  Tick init     = ⊥
  Tick term     = ⊥
  Tick (perm σ) = ⊥


  module Cut where
    Cut : (Γ₁ ⇶ Γ₂) → Type
    Cut (x₁ ∥ x₂) = Cut x₁ × Cut x₂
    Cut (x₁ ⟫ x₂) = Cut x₁ ⊎ Cut x₂
    Cut tick      = ⊤ ⊎ ⊤
    Cut fork      = ⊤ ⊎ ⊤
    Cut join      = ⊤ ⊎ ⊤
    Cut init      = ⊤ ⊎ ⊤
    Cut term      = ⊤ ⊎ ⊤
    Cut (perm _ ) = ⊤ ⊎ ⊤

    Γ[_] : {exec : Γ₁ ⇶ Γ₂} → Cut exec → Tree (Tree Ty[ exec ])
    Γ[_] {exec = x₁ ∥ x₂} (c₁ , c₂) = Γ[ c₁ ] ∗ Γ[ c₂ ]
    Γ[_] {exec = x₁ ⟫ x₂} (inj₁ c₁) = Γ[ c₁ ]
    Γ[_] {exec = x₁ ⟫ x₂} (inj₂ c₂) = Γ[ c₂ ]
    Γ[_] {Γ₁ = Γ₁} {Γ₂ = Γ₂} {exec = tick}   = Sum.[ (λ _ → Γ₁) , (λ _ → Γ₂) ]
    Γ[_] {Γ₁ = Γ₁} {Γ₂ = Γ₂} {exec = fork}   = Sum.[ (λ _ → Γ₁) , (λ _ → Γ₂) ]
    Γ[_] {Γ₁ = Γ₁} {Γ₂ = Γ₂} {exec = join}   = Sum.[ (λ _ → Γ₁) , (λ _ → Γ₂) ]
    Γ[_] {Γ₁ = Γ₁} {Γ₂ = Γ₂} {exec = init}   = Sum.[ (λ _ → Γ₁) , (λ _ → Γ₂) ]
    Γ[_] {Γ₁ = Γ₁} {Γ₂ = Γ₂} {exec = term}   = Sum.[ (λ _ → Γ₁) , (λ _ → Γ₂) ]
    Γ[_] {Γ₁ = Γ₁} {Γ₂ = Γ₂} {exec = perm σ} = Sum.[ (λ _ → Γ₁) , (λ _ → Γ₂) ]

    Site : {exec : Γ₁ ⇶ Γ₂} → Cut exec → Type
    Site c = Sites.Site Γ[ c ]
  Cut = Cut.Cut

  LeadingCut[_] : (exec : Γ₁ ⇶ Γ₂) → Cut exec
  LeadingCut[ x₁ ∥ x₂ ] = (LeadingCut[ x₁ ] , LeadingCut[ x₂ ])
  LeadingCut[ x₁ ⟫ x₂ ] = inj₂ (LeadingCut[ x₂ ])
  LeadingCut[ tick   ]  = inj₂ tt
  LeadingCut[ fork   ]  = inj₂ tt
  LeadingCut[ join   ]  = inj₂ tt
  LeadingCut[ init   ]  = inj₂ tt
  LeadingCut[ term   ]  = inj₂ tt
  LeadingCut[ perm _ ]  = inj₂ tt

  TrailingCut[_] : (exec : Γ₁ ⇶ Γ₂) → Cut exec
  TrailingCut[ x₁ ∥ x₂ ] = (TrailingCut[ x₁ ] , TrailingCut[ x₂ ])
  TrailingCut[ x₁ ⟫ x₂ ] = inj₁ (TrailingCut[ x₁ ])
  TrailingCut[ tick   ]  = inj₁ tt
  TrailingCut[ fork   ]  = inj₁ tt
  TrailingCut[ join   ]  = inj₁ tt
  TrailingCut[ init   ]  = inj₁ tt
  TrailingCut[ term   ]  = inj₁ tt
  TrailingCut[ perm _ ]  = inj₁ tt

  -- A site at a time.
  Event : {Γ₁ Γ₂ : Tree (Tree T)} → (Γ₁ ⇶ Γ₂) → Type
  Event                (x₁ ∥ x₂)     = Event x₁ ⊎ Event x₂
  Event                (x₁ ⟫ x₂)     = Event x₁ ⊎ Event x₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} tick     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} fork     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} join     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} init     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} term     = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
  Event {Γ₁ = Γ₁} {Γ₂ = Γ₂} (perm σ) = Sites.Site Γ₁ ⊎ Sites.Site Γ₂
```
