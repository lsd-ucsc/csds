---
title: Properties of causal paths
author: Jonathan Castello
date: 2023-02-23
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
module Execution.Causality.Properties where
```

<details>
<summary>Imports, fixity, and variables</summary>

```agda
  open import Data.Product
    using (_,_; proj₁; proj₂)
  open import Relation.Binary.Construct.Composition
    as Rel
    using ()
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)
  open import DependentEquality
    as DEq
    using (_≡[_]_)
  open import Execution.Sites
    as Tree
    using (Tree; Site)
  open import Execution.Core
    using (_⇶_; id; _⟫_; _;_)
    using (Event; Cut)
  open Event
    using (_,_)
  open import Execution.Causality
    using (_⋯_; init; go)
    using (before[_]; after[_]; during[_])
    using (Spanning[_])
    using (_↝_)

  infixl 20 _⋯∘_

  variable
    T : Type
    Γ₁ Γ₂ Γ₃ Γ₄ Γᵢ : Tree (Tree T)
```

</details>

```agda
  _⋯∘_ : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ t₃ : Cut exec}
       → (t₁ ⋯ t₂) → (t₂ ⋯ t₃) → (t₁ ⋯ t₃)
  _        ⋯∘ init _ _ = init _ _
  go _ t₁₂ ⋯∘ go _ t₂₃ = go _ (t₁₂ ⋯∘ t₂₃)

  ⋯-refl : {exec : Γ₁ ⇶ Γ₂}
         → (t : Cut exec)
         → (t ⋯ t)
  ⋯-refl (Cut.now  _  ) = _⋯_.init _ _
  ⋯-refl (Cut.back _ t) = _⋯_.go _ (⋯-refl t)

  ⋯-antisym : {exec : Γ₁ ⇶ Γ₂}
            → {t₁ t₂ : Cut exec}
            → (t₁ ⋯ t₂)
            → (t₂ ⋯ t₁)
            → (t₁ ≡ t₂)
  ⋯-antisym (init _ _) (init _ _) = Eq.refl
  ⋯-antisym (go _ t₁₂) (go _ t₂₁) = Eq.cong (Cut.back _) (⋯-antisym t₁₂ t₂₁)

  ⋯-trans = _⋯∘_

  ⋯∘-unitₗ : {exec : Γ₁ ⇶ Γ₂}
           → {t₁ t₂ : Cut exec}
           → (t₁₂ : t₁ ⋯ t₂)
           → ⋯-refl t₁ ⋯∘ t₁₂ ≡ t₁₂
  ⋯∘-unitₗ (init _ _)     = Eq.refl
  ⋯∘-unitₗ (go   _ t₁₂) = Eq.cong (go _) (⋯∘-unitₗ t₁₂)

  ⋯∘-unitᵣ : {exec : Γ₁ ⇶ Γ₂}
           → {t₁ t₂ : Cut exec}
           → (t₁₂ : t₁ ⋯ t₂)
           → t₁₂ ⋯∘ ⋯-refl t₂ ≡ t₁₂
  ⋯∘-unitᵣ (init _ _)   = Eq.refl
  ⋯∘-unitᵣ (go   _ t₁₂) = Eq.cong (go _) (⋯∘-unitᵣ t₁₂)

  ⋯-prop : {exec : Γ₁ ⇶ Γ₂}
         → {t₁ t₂ : Cut exec}
         → (t₁₂ t₁₂′ : t₁ ⋯ t₂)
         → t₁₂ ≡ t₁₂′
  ⋯-prop (init _ _)   (init _ _)    = Eq.refl
  ⋯-prop (go   _ t₁₂) (go   _ t₁₂′) = Eq.cong (go _) (⋯-prop t₁₂ t₁₂′)

  ⋯∘-assoc : {exec : Γ₁ ⇶ Γ₂}
           → {t₁ t₂ t₃ t₄ : Cut exec}
           → (t₁₂ : t₁ ⋯ t₂)
           → (t₂₃ : t₂ ⋯ t₃)
           → (t₃₄ : t₃ ⋯ t₄)
           → ((t₁₂ ⋯∘ t₂₃) ⋯∘ t₃₄) ≡ (t₁₂ ⋯∘ (t₂₃ ⋯∘ t₃₄))
  ⋯∘-assoc _ _ _ = ⋯-prop _ _

  bar″ : {exec : Γ₁ ⇶ Γ₂}
       → (t : Cut exec)
       → (before[ t ] ; after[ t ] ≡ exec)
  bar″ (Cut.now  _  ) = Eq.refl
  bar″ (Cut.back _ t) = Eq.cong (_⟫ _) (bar″ t)

  bar′ : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Cut exec}
       → (t₁₂ : t₁ ⋯ t₂)
       → (before[ t₁ ] ; during[ t₁₂ ] ≡ before[ t₂ ])
  bar′ (init _ t₁ ) = bar″ t₁
  bar′ (go   _ t₁₂) = bar′ t₁₂

  bar : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ : Cut exec}
      → (t₁₂ : t₁ ⋯ t₂)
      → (during[ t₁₂ ] ; after[ t₂ ] ≡ after[ t₁ ])
  bar (init _ _  ) = Eq.refl
  bar (go   _ t₁₂) = Eq.cong (_⟫ _) (bar t₁₂)

  foo : {exec : Γ₁ ⇶ Γ₂} {t₁ t₂ t₃ : Cut exec}
      → (t₁₂ : t₁ ⋯ t₂)
      → (t₂₃ : t₂ ⋯ t₃)
      → (during[ t₁₂ ] ; during[ t₂₃ ] ≡ during[ t₁₂ ⋯∘ t₂₃ ])
  foo       t₁₂  (init _ _  ) = bar t₁₂
  foo (go _ t₁₂) (go   _ t₂₃) = foo t₁₂ t₂₃

  quux : {exec : Γ₁ ⇶ Γ₂}
       → (t : Cut exec)
       → id ≡ during[ ⋯-refl t ]
  quux (Cut.now  _  ) = Eq.refl
  quux (Cut.back _ t) = quux t

  ;-assoc : (a : Γ₁ ⇶ Γ₂) (b : Γ₂ ⇶ Γ₃) (c : Γ₃ ⇶ Γ₄)
          → (a ; b) ; c ≡ a ; (b ; c)
  ;-assoc a b id      = Eq.refl
  ;-assoc a b (c ⟫ _) = Eq.cong (_⟫ _) (;-assoc a b c)

  -- Properties of spanning paths across separate executions
  module _ where
    _∘↝ₙ[_]_ : {prefix : Γ₁ ⇶ Γ₂}
             → ∀{t₁ t₂} → Spanning[ prefix          ] t₁ t₂
             → (suffix : Γ₂ ⇶ Γ₃)
             → ∀{t₃}    → Spanning[          suffix ] t₂ t₃
             →            Spanning[ prefix ; suffix ] t₁ t₃
    p₁₂ ∘↝ₙ[ id         ] Eq.refl          = p₁₂
    p₁₂ ∘↝ₙ[ suffix ⟫ _ ] (tᵢ , p₂ᵢ , pᵢ₃) = (tᵢ , p₁₂ ∘↝ₙ[ suffix ] p₂ᵢ , pᵢ₃)

    ∘↝ₙ-split : {prefix : Γ₁ ⇶ Γ₂} {suffix : Γ₂ ⇶ Γ₃}
              → {t₁ : Site Γ₁}
              → {t₃ : Site Γ₃}
              → Spanning[ prefix ; suffix ] t₁ t₃
              → (Spanning[ prefix ] Rel.; Spanning[ suffix ]) t₁ t₃
    ∘↝ₙ-split {suffix = id} t₁↝t₃ = (_ , t₁↝t₃ , Eq.refl)
    ∘↝ₙ-split {suffix = suffix ⟫ step} (tᵢ , t₁↝tᵢ , tᵢ↝t₃)
      = let (a , b , c) = ∘↝ₙ-split {suffix = suffix} t₁↝tᵢ in
        (a , b , (tᵢ , c , tᵢ↝t₃))

    ∘↝ₙ-assoc : {left : Γ₁ ⇶ Γ₂} {middle : Γ₂ ⇶ Γ₃} {right : Γ₃ ⇶ Γ₄}
              → {t₁ : Site Γ₁}
              → {t₂ : Site Γ₂}
              → {t₃ : Site Γ₃}
              → {t₄ : Site Γ₄}
              → (p₁₂ : Spanning[ left   ] t₁ t₂)
              → (p₂₃ : Spanning[ middle ] t₂ t₃)
              → (p₃₄ : Spanning[ right  ] t₃ t₄)
              → ((p₁₂ ∘↝ₙ[ middle ] p₂₃) ∘↝ₙ[ right ] p₃₄)
              ≡[ Eq.cong (λ z → Spanning[ z ] _ _) (;-assoc left middle right) ]
                (p₁₂ ∘↝ₙ[ middle ; right ] (p₂₃ ∘↝ₙ[ right ] p₃₄))
    ∘↝ₙ-assoc {right = id}
              p₁₂ p₂₃ Eq.refl
       = Eq.refl
    ∘↝ₙ-assoc {left = left} {middle} {right ⟫ _}
              p₁₂ p₂₃ (tᵢ , p₃ᵢ , pᵢ₄)
      = DEq.hom (Eq.cong-∘ (;-assoc left middle right))
                (DEq.cong (λ _ z → (_ , z , pᵢ₄))
                          (;-assoc left middle right)
                          (∘↝ₙ-assoc {left = left} {middle = middle} p₁₂ p₂₃ p₃ᵢ))

  --        t₁    t₂
  --    |   s₁----s₂    |
  -- -> |         s₂----| s₃
  -- -> |   s₁----------| s₃
  hehe : {exec : Γ₁ ⇶ Γ₂}
       → {t₁ t₂    : Cut exec}
       → {s₁       : Cut.Site t₁}
       → {   s₂    : Cut.Site t₂}
       → {      s₃ : Site Γ₂}
       → (t₁₂ : t₁ ⋯ t₂)
       → Spanning[ during[ t₁₂ ] ] s₁ s₂
       → Spanning[ after[   t₂ ] ] s₂ s₃
       → Spanning[ after[  t₁  ] ] s₁ s₃
  hehe (init t₁ t₂)  p₁₂ Eq.refl          = p₁₂
  hehe (go   _  t₁₂) p₁₂ (tᵢ , p₂ᵢ , pᵢ₃) = (tᵢ , hehe t₁₂ p₁₂ p₂ᵢ , pᵢ₃)

  --        t₁    t₂    t₃
  --    |   s₁----s₂    s₃   |
  -- -> |         s₂----s₃   |
  -- -> |   s₁----------s₃   |
  haha : {exec : Γ₁ ⇶ Γ₂}
       → {t₁ t₂ t₃ : Cut exec}
       → {s₁       : Cut.Site t₁}
       → {   s₂    : Cut.Site t₂}
       → {      s₃ : Cut.Site t₃}
       → (t₁₂ : t₁ ⋯ t₂)
       → (t₂₃ : t₂ ⋯ t₃)
       → Spanning[ during[ t₁₂        ] ] s₁ s₂
       → Spanning[ during[        t₂₃ ] ] s₂ s₃
       → Spanning[ during[ t₁₂ ⋯∘ t₂₃ ] ] s₁ s₃
  haha       t₁₂  (init t₂ t₃ ) p₁₂ p₂₃ = hehe t₁₂ p₁₂ p₂₃
  haha (go _ t₁₂) (go   _  t₂₃) p₁₂ p₂₃ = haha t₁₂ t₂₃ p₁₂ p₂₃

  _↝∘_ : {exec : Γ₁ ⇶ Γ₂} {e₁ e₂ e₃ : Event exec}
       → (e₁ ↝ e₂) → (e₂ ↝ e₃) → (e₁ ↝ e₃)
  proj₁ ((t₁₂ , _  ) ↝∘ (t₂₃ , _  ))
    = t₁₂ ⋯∘ t₂₃
  proj₂ ((t₁₂ , p₁₂) ↝∘ (t₂₃ , p₂₃))
    = haha t₁₂ t₂₃ p₁₂ p₂₃

  ↝-refl : {exec : Γ₁ ⇶ Γ₂}
         → (e : Event exec)
         → (e ↝ e)
  proj₁ (↝-refl (t , s)) = ⋯-refl t
  proj₂ (↝-refl (t , s)) = Eq.subst (λ z → Spanning[ z ] s s) (quux t) Eq.refl


  ↝-antisym : {exec : Γ₁ ⇶ Γ₂}
            → {t₁ t₂ : Cut exec}
            → {s₁    : Cut.Site t₁}
            → {   s₂ : Cut.Site t₂}
            → ((t₁ , s₁) ↝ (t₂ , s₂))
            → ((t₂ , s₂) ↝ (t₁ , s₁))
            → ((t₁ Event., s₁) ≡ (t₂ Event., s₂))
  ↝-antisym (t₁₂ , p₁₂) (t₂₁ , _) =
      Event.eq (⋯-antisym t₁₂ t₂₁) λ{Eq.refl → hah? t₁₂ p₁₂}
    where
      hah? : {exec : Γ₁ ⇶ Γ₂}
           → {t : Cut exec}
           → {s₁ s₂ : Cut.Site t}
           → (t₁₂ : t ⋯ t)
           → (p₁₂ : Spanning[ during[ t₁₂ ] ] s₁ s₂)
           → s₁ ≡ s₂
      hah? (init _ _)   Eq.refl = Eq.refl
      hah? (go   _ t₁₁) p₁₂     = hah? t₁₁ p₁₂

  ↝-trans = _↝∘_


  hehe∘haha : {exec : Γ₁ ⇶ Γ₂}
            → {t₁ t₂ t₃ : Cut exec}
            → {s₁          : Cut.Site t₁}
            → {   s₂       : Cut.Site t₂}
            → {      s₃    : Cut.Site t₃}
            → {         s₄ : Site Γ₂}
            → (t₁₂ : t₁ ⋯ t₂)
            → (t₂₃ : t₂ ⋯ t₃)
            → (p₁₂ : Spanning[ during[ t₁₂  ] ] s₁ s₂)
            → (p₂₃ : Spanning[ during[  t₂₃ ] ] s₂ s₃)
            → (p₃₄ : Spanning[  after[   t₃ ] ] s₃ s₄)
            → hehe (t₁₂ ⋯∘ t₂₃) (haha t₁₂ t₂₃ p₁₂ p₂₃) p₃₄
            ≡ hehe t₁₂ p₁₂ (hehe t₂₃ p₂₃ p₃₄)
  hehe∘haha       t₁₂  (init _ _) p₁₂ p₂₃ Eq.refl
    = Eq.refl
  hehe∘haha (go _ t₁₂) (go _ t₂₃) p₁₂ p₂₃ (sᵢ , p₃ᵢ , pᵢ₄)
    = Eq.cong (λ ▢ → (sᵢ , ▢ , pᵢ₄))
              (hehe∘haha t₁₂ t₂₃ p₁₂ p₂₃ p₃ᵢ)

  haha∘haha : {exec : Γ₁ ⇶ Γ₂}
            → {t₁ t₂ t₃ t₄ : Cut exec}
            → {s₁          : Cut.Site t₁}
            → {   s₂       : Cut.Site t₂}
            → {      s₃    : Cut.Site t₃}
            → {         s₄ : Cut.Site t₄}
            → (t₁₂ : t₁ ⋯ t₂)
            → (t₂₃ : t₂ ⋯ t₃)
            → (t₃₄ : t₃ ⋯ t₄)
            → (p₁₂ : Spanning[ during[ t₁₂   ] ] s₁ s₂)
            → (p₂₃ : Spanning[ during[  t₂₃  ] ] s₂ s₃)
            → (p₃₄ : Spanning[ during[   t₃₄ ] ] s₃ s₄)
            → haha (t₁₂ ⋯∘ t₂₃) t₃₄ (haha t₁₂ t₂₃ p₁₂ p₂₃) p₃₄
            ≡[ Eq.cong (λ z → Spanning[ during[ z ] ] s₁ s₄)
                  (⋯∘-assoc t₁₂ t₂₃ t₃₄)
            ] haha t₁₂ (t₂₃ ⋯∘ t₃₄) p₁₂ (haha t₂₃ t₃₄ p₂₃ p₃₄)
  haha∘haha       t₁₂        t₂₃  (init t₃ t₄)
                  p₁₂        p₂₃  p₃₄
    = hehe∘haha t₁₂ t₂₃ p₁₂ p₂₃ p₃₄
  haha∘haha (go _ t₁₂) (go _ t₂₃) (go _ t₃₄)
                  p₁₂        p₂₃        p₃₄
    = DEq.hom (Eq.cong-∘ (⋯∘-assoc t₁₂ t₂₃ t₃₄))
              (haha∘haha t₁₂ t₂₃ t₃₄ p₁₂ p₂₃ p₃₄)

  -- With deepest gratitude to an archived Reddit comment by Jannis Limperg.
  -- https://old.reddit.com/r/agda/comments/ax9rnx/help_with_equality_of_dependent_records/ehu86iv/
  ↝-eq : {exec : Γ₁ ⇶ Γ₂}
       → {t₁ t₂ : Cut exec}
       → {s₁    : Cut.Site t₁}
       → {   s₂ : Cut.Site t₂}
       → {ord₁  : t₁ ⋯ t₂}
       → {path₁ : Spanning[ during[ ord₁ ] ] s₁ s₂}
       → {ord₂  : t₁ ⋯ t₂}
       → {path₂ : Spanning[ during[ ord₂ ] ] s₁ s₂}
       → (x : ord₁ ≡ ord₂)
       → (y : path₁ ≡[ Eq.cong (λ ▢ → Spanning[ during[ ▢ ] ] _ _) x ] path₂)
       → (ord₁ Data.Product., path₁) ≡ (ord₂ Data.Product., path₂)
  ↝-eq Eq.refl Eq.refl = Eq.refl

  ↝∘-assoc : {exec : Γ₁ ⇶ Γ₂}
           → {t₁ t₂ t₃ t₄ : Event exec}
           → (p₁₂ : t₁ ↝ t₂)
           → (p₂₃ : t₂ ↝ t₃)
           → (p₃₄ : t₃ ↝ t₃)
           → (p₁₂ ↝∘  p₂₃) ↝∘ p₃₄
           ≡  p₁₂ ↝∘ (p₂₃  ↝∘ p₃₄)
  ↝∘-assoc (t₁₂ , p₁₂) (t₂₃ , p₂₃) (t₃₄ , p₃₄)
    = ↝-eq (⋯∘-assoc t₁₂ t₂₃ t₃₄)
           (haha∘haha t₁₂ t₂₃ t₃₄ p₁₂ p₂₃ p₃₄)
```
