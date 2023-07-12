---
title: Causal order
author: Jonathan Castello
date: 2023-02-04
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
module Execution.Causality where
```

<details>
<summary>Imports, fixity, and variables</summary>

```agda
  open import Data.Unit
    using (⊤)
  open import Data.Product
    using (Σ-syntax)
  open import Data.Sum
    using (inj₁; inj₂)
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
    using (_⇶[_]_; _⇶_; _⇶₁_; Event; Tick; Cut)
    using (perm; tick; fork; join; id; _∥_; _⟫_)
  open Event using (_,_)

  infixl 20 _⊗_

  variable
    T : Type
    Γ₁ Γ₂ Γᵢ : Tree (Tree T)
```

</details>

```agda
  -- Concurrent composition of indexed families of paths.
  data _⊗_ {T : Type} {Γ₁ Γ₂ Γ₃ Γ₄ : Tree T}
           (f : Site Γ₁ → Site Γ₂ → Type)
           (g : Site Γ₃ → Site Γ₄ → Type)
         : Site (Γ₁ ∗ Γ₃) → Site (Γ₂ ∗ Γ₄) → Type where
    thereˡ : ∀ a b
           → f a b
           → (f ⊗ g) (Site.thereˡ Γ₃ a) (Site.thereˡ Γ₄ b)

    thereʳ : ∀ a b
           → g a b
           → (f ⊗ g) (Site.thereʳ Γ₁ a) (Site.thereʳ Γ₂ b)

  Spanning[_] : ∀{k} → (Γ₁ ⇶[ k ] Γ₂) → (Site Γ₁ → Site Γ₂ → Type)
  Spanning[ id     ] a b = b ≡ a
  Spanning[ perm p ] a b = b ≡ Tree.‵index p a
  Spanning[ tick   ] _ _ = ⊤
  Spanning[ fork   ] _ _ = ⊤
  Spanning[ join   ] _ _ = ⊤
  Spanning[ left   ∥ right  ] = Spanning[ left   ]     ⊗ Spanning[ right  ]
  Spanning[ prefix ⟫ suffix ] = Spanning[ prefix ] Rel.; Spanning[ suffix ]


  -- The type of time intervals within an execution.
  data _⋯_ {T : Type} : {Γ₁ Γ₂ : Tree (Tree T)} {exec : Γ₁ ⇶ Γ₂} (_ _ : Cut exec) → Type where
    init : (exec : Γ₁ ⇶ Γ₂)
         → (c₁ : Cut exec)
         → (c₁ ⋯ Cut.now exec)

    go : {prefix : Γ₁ ⇶ Γᵢ}
       → {c₁ c₂ : Cut prefix}
       → (step : Γᵢ ⇶₁ Γ₂)
       → (c₁ ⋯ c₂)
       → (Cut.back step c₁ ⋯ Cut.back step c₂)

  -- The execution "before" the given cut.
  before[_] : {exec : Γ₁ ⇶ Γ₂} → (c : Cut exec) → (Γ₁ ⇶ Cut.Γ[ c ])
  before[ Cut.now  exec ] = exec
  before[ Cut.back _ c  ] = before[ c ]

  -- The execution "after" the given cut.
  after[_] : {exec : Γ₁ ⇶ Γ₂} → (c : Cut exec) → (Cut.Γ[ c ] ⇶ Γ₂)
  after[ Cut.now       _ ] = _⇶[_]_.id
  after[ Cut.back step c ] = after[ c ] _⇶[_]_.⟫ step

  -- The execution "during" the span of time between two cuts.
  during[_] : {exec : Γ₁ ⇶ Γ₂} {c₁ c₂ : Cut exec}
            → (interval : c₁ ⋯ c₂)
            → (Cut.Γ[ c₁ ] ⇶ Cut.Γ[ c₂ ])
  during[ init _ t₁    ] = after[ t₁ ]
  during[ go   _ t₁≤t₂ ] = during[ t₁≤t₂ ]

  -- An interior path between two events within an execution.
  Arr[_] : (exec : Γ₁ ⇶ Γ₂) → (Event exec → Event exec → Type)
  Arr[ exec ] (t₁ , s₁) (t₂ , s₂)
    = Σ[ t₁⋯t₂ ∈ t₁ ⋯ t₂ ]
        Spanning[ during[ t₁⋯t₂ ] ] s₁ s₂


  ↝ₙ-syntax = Spanning[_]
  syntax ↝ₙ-syntax exec t₁ t₂ = t₁ ↝ₙ[ exec ] t₂

  _↝_ : {exec : Γ₁ ⇶ Γ₂} → (_ _ : Event exec) → Type
  e₁ ↝ e₂ = Arr[ _ ] e₁ e₂

  start[_] : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Event exec} → (t₁ ↝ t₂) → Event exec
  start[_] {t₁ = t₁} _ = t₁

  end[_] : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Event exec} → (t₁ ↝ t₂) → Event exec
  end[_] {t₂ = t₂} _ = t₂


  liftˡ : {exec : Γ₁ ⇶ Γ₂}
        → (pivot : Cut exec)
        → (Cut before[ pivot ] → Cut exec)
  liftˡ (Cut.now  _   ) t₂ = t₂
  liftˡ (Cut.back _ t₁) t₂ = Cut.back _ (liftˡ t₁ t₂)

  tliftˡ : {exec : Γ₁ ⇶ Γ₂}
         → (pivot : Cut exec)
         → (Tick before[ pivot ] → Tick exec)
  tliftˡ (Cut.now  _   ) a = a
  tliftˡ (Cut.back _ t₁) a = inj₁ (tliftˡ t₁ a)

  liftʳ : {exec : Γ₁ ⇶ Γ₂}
        → (pivot : Cut exec)
        → (Cut after[ pivot ] → Cut exec)
  liftʳ (Cut.now  _   ) (Cut.now  _   ) = Cut.now  _
  liftʳ (Cut.back _ _ ) (Cut.now  _   ) = Cut.now  _
  liftʳ (Cut.back _ t₁) (Cut.back _ t₂) = Cut.back _ (liftʳ t₁ t₂)

  tliftʳ : {exec : Γ₁ ⇶ Γ₂}
         → (pivot : Cut exec)
         → (Tick after[ pivot ] → Tick exec)
  tliftʳ (Cut.back _ _) (inj₂ a) = inj₂ a
  tliftʳ (Cut.back _ _) (inj₁ a) = inj₁ (tliftʳ _ a)

  lift : {exec : Γ₁ ⇶ Γ₂}
       → {t₁ t₂ : Cut exec}
       → (t₁≤t₂ : t₁ ⋯ t₂)
       → (Cut during[ t₁≤t₂ ] → Cut exec)
  lift (init _ t₁)    tᵢ  = liftʳ t₁ tᵢ
  lift (go   _ t₁<t₂) tᵢ  = Cut.back _ (lift t₁<t₂ tᵢ)

  tlift : {exec : Γ₁ ⇶ Γ₂}
        → {t₁ t₂ : Cut exec}
        → (t₁≤t₂ : t₁ ⋯ t₂)
        → (Tick during[ t₁≤t₂ ] → Tick exec)
  tlift (init _ t₁)    k = tliftʳ t₁ k
  tlift (go   _ t₁≤t₂) k = inj₁ (tlift t₁≤t₂ k)
```
