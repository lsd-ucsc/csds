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
  open import Data.Product
    using (∃; -,_)
  open import Data.Nat
    as ℕ
    using (ℕ)
  open import Data.Nat.Properties
    as ℕ-Prop
    using ()
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  infix 5 _≅_ _∈_
  infix 6 _∗_ _⊗_

  variable
    T : Type
```

</details>

```agda
  -- A site configuration is a binary tree with labeled leaves.
  data Tree (T : Type) : Type where
    ∅    :                   Tree T
    leaf : T      →          Tree T
    _∗_  : Tree T → Tree T → Tree T

  -- A label may be found at zero or more sites in a configuration.
  data _∈_ {T : Type} (a : T) : Tree T → Type where
    here   :                           a ∈ leaf a
    thereˡ : ∀{l} r  → (ixˡ : a ∈ l) → a ∈ (l ∗ r)
    thereʳ : ∀ l {r} → (ixʳ : a ∈ r) → a ∈ (l ∗ r)

  -- The leaves in a configuration are its *sites*.
  record Site {T : Type} (Γ : Tree T) : Type where
    constructor site
    field {state[_]} : T
    field index[_]   : state[_] ∈ Γ
  open Site public

  -- Equivalence of trees up to balance and order,
  -- establishing ⟨Tree T / _≅_ , _∗_⟩ as an invertible semigroup.
  data _≅_ {T : Type} : (_ _ : Tree T) → Type where
    ‵cong    : ∀{a₁ a₂ b₁ b₂} → (a₁ ≅ a₂) → (b₁ ≅ b₂) → ((a₁ ∗ b₁) ≅ (a₂ ∗ b₂))

    ‵trans   : ∀{a b c} → (a ≅ b) → (b ≅ c) → (a ≅ c)
    ‵refl    : ∀ a      → (a ≅ a)
    ‵swap    : ∀ a b    → (a ∗ b) ≅ (b ∗ a)
    ‵assoc   : ∀ a b c  → ((a ∗  b) ∗ c) ≅ (a ∗ (b  ∗ c))

    -- These rules additionally make ⟨Tree T / _≅_ , ∅ , _∗_⟩ a group.
    --‵unitₗ   : ∀ a → (∅ ∗ a) ≅      a
    --‵unit₁⁻¹ : ∀ a →      a  ≅ (∅ ∗ a)

    --‵unitᵣ   : ∀ a → (a ∗ ∅) ≅  a
    --‵unitᵣ⁻¹ : ∀ a →  a      ≅ (a ∗ ∅)

  syntax ‵trans s₁ s₂ = s₁ ∘≅ s₂

  -- `≅` is symmetric.
  ‵sym : {a b : Tree T} → (a ≅ b) → (b ≅ a)
  ‵sym (‵cong    p q)   = ‵cong  (‵sym p) (‵sym q)
  ‵sym (‵trans   p q)   = ‵trans (‵sym q) (‵sym p)
  ‵sym (‵refl    _)     = ‵refl _
  ‵sym (‵swap    a b)   = ‵swap b a
  ‵sym (‵assoc   a b c) =
    (‵trans (‵trans (‵trans (‵trans
      (‵swap  _ _)
      (‵assoc _ _ _))
      (‵swap  _ _))
      (‵assoc _ _ _))
      (‵swap  _ _))

  -- The size of a configuration is the number of distinct leaves it contains.
  -- That is, `size Γ` is the cardinality of `Site Γ`.
  size : Tree T → ℕ
  size ∅              = 0
  size (leaf atom)    = 1
  size (left ∗ right) = size left ℕ.+ size right

  ‵size : ∀{a b : Tree T} → (a ≅ b) → (size a ≡ size b)
  ‵size (‵cong    p q)   = Eq.cong₂ ℕ._+_ (‵size p) (‵size q)
  ‵size (‵trans   p q)   = Eq.trans (‵size p) (‵size q)
  ‵size (‵refl    _)     = Eq.refl
  ‵size (‵swap    a b)   = ℕ-Prop.+-comm (size a) (size b)
  ‵size (‵assoc   a b c) = ℕ-Prop.+-assoc (size a) (size b) (size c)

  module _ where
    ‵index : {Γ₁ Γ₂ : Tree T} {a : T}
           → (Γ₁ ≅ Γ₂)
           → (a ∈ Γ₁) → (a ∈ Γ₂)

    ‵index (‵cong p q) (thereˡ _ ix) = thereˡ _ (‵index p ix)
    ‵index (‵cong p q) (thereʳ _ ix) = thereʳ _ (‵index q ix)

    ‵index (‵trans   p q) = ‵index q Function.∘ ‵index p
    ‵index (‵refl    _)   = Function.id

    ‵index (‵swap    _ _) (thereˡ _ ix) = thereʳ _ ix
    ‵index (‵swap    _ _) (thereʳ _ ix) = thereˡ _ ix

    ‵index (‵assoc   a b c) (thereˡ _ (thereˡ _ ix)) = thereˡ _           ix
    ‵index (‵assoc   a b c) (thereˡ _ (thereʳ _ ix)) = thereʳ _ (thereˡ _ ix)
    ‵index (‵assoc   a b c) (thereʳ _           ix ) = thereʳ _ (thereʳ _ ix)

  module _ where
    ‶index : {Γ₁ Γ₂ : Tree T} (p : Γ₁ ≅ Γ₂)
           → ∀{a} → (ix : a ∈ Γ₁)
           → (‵index (‵sym p) ∘ ‵index p) ix ≡ ix

    ‶index (‵cong p _) (thereˡ _ ix) = Eq.cong (thereˡ _) (‶index p ix)
    ‶index (‵cong _ q) (thereʳ _ ix) = Eq.cong (thereʳ _) (‶index q ix)

    ‶index (‵trans p q) ix = Eq.trans (Eq.cong (‵index (‵sym p)) (‶index q (‵index p ix)))
                                      (‶index p ix)

    ‶index (‵refl _) _ = Eq.refl

    ‶index (‵swap _ _) (thereˡ _ _) = Eq.refl
    ‶index (‵swap _ _) (thereʳ _ _) = Eq.refl

    ‶index (‵assoc _ _ _) (thereˡ _ (thereˡ _ _)) = Eq.refl
    ‶index (‵assoc _ _ _) (thereˡ _ (thereʳ _ _)) = Eq.refl
    ‶index (‵assoc _ _ _) (thereʳ _           _ ) = Eq.refl

  -- A configuration relation is a relation between two site configurations.
  _⇒_     : Tree T  → Tree T  → Type₁
  Γ₁ ⇒ Γ₂ = Site Γ₁ → Site Γ₂ → Type

  -- Two configuration relations can be composed concurrently.
  data _⊗_ {T : Type} {Γ₁ Γ₂ Γ₃ Γ₄ : Tree T}
           (f : Γ₁ ⇒ Γ₃)
           (g : Γ₂ ⇒ Γ₄)
         : (Γ₁ ∗ Γ₂) ⇒ (Γ₃ ∗ Γ₄) where
    thereˡ : {t₁ : T} (a : t₁ ∈ Γ₁)
           → {t₂ : T} (b : t₂ ∈ Γ₃)
           → f (site a) (site b)
           → (f ⊗ g) (site (thereˡ Γ₂ a)) (site (thereˡ Γ₄ b))
    thereʳ : {t₁ : T} (a : t₁ ∈ Γ₂)
           → {t₂ : T} (b : t₂ ∈ Γ₄)
           → g (site a) (site b)
           → (f ⊗ g) (site (thereʳ Γ₁ a)) (site (thereʳ Γ₃ b))

  -- The groupoid of site permutations can be interpreted
  -- into a groupoid of relations on sites.
  data Match[_] {T : Type}
              : {Γ₁ Γ₂ : Tree T} (σ : Γ₁ ≅ Γ₂)
              → (Γ₁ ⇒ Γ₂)
            where
    Match-refl : {Γ : Tree T}
               → ∀ s
               → Match[ ‵refl Γ ] s s

    Match-swapₗ : ({Γ₁} Γ₂ : Tree T)
                → ∀{a} (s₁ : a ∈ Γ₁)
                → Match[ ‵swap Γ₁ Γ₂ ] (site (thereˡ Γ₂ s₁)) (site (thereʳ Γ₂ s₁))
    Match-swapᵣ : (Γ₁ {Γ₂} : Tree T)
                → ∀{a} (s₂ : a ∈ Γ₂)
                → Match[ ‵swap Γ₁ Γ₂ ] (site (thereʳ Γ₁ s₂)) (site (thereˡ Γ₁ s₂))

    Match-assoc₁ : (Γ₁ {Γ₂} {Γ₃} : Tree T)
                 → ∀{a} (s₁ : a ∈ Γ₁)
                 → Match[ ‵assoc Γ₁ Γ₂ Γ₃ ] (site (thereˡ _ (thereˡ _ s₁))) (site (thereˡ _ s₁))
    Match-assoc₂ : ({Γ₁} Γ₂ {Γ₃} : Tree T)
                 → ∀{a} (s₂ : a ∈ Γ₂)
                 → Match[ ‵assoc Γ₁ Γ₂ Γ₃ ] (site (thereˡ _ (thereʳ _ s₂))) (site (thereʳ _ (thereˡ _ s₂)))
    Match-assoc₃ : ({Γ₁} {Γ₂} Γ₃ : Tree T)
                 → ∀{a} (s₃ : a ∈ Γ₃)
                 → Match[ ‵assoc Γ₁ Γ₂ Γ₃ ] (site (thereʳ _ s₃)) (site (thereʳ _ (thereʳ _ s₃)))

    Match-trans : {Γ₁ Γ₂ Γ₃ : Tree T}
                → {σ₁ : Γ₁ ≅ Γ₂}
                → {σ₂ : Γ₂ ≅ Γ₃}
                → ∀{s₁ s₂ s₃}
                → Match[ σ₁ ] s₁ s₂
                → Match[ σ₂ ] s₂ s₃
                → Match[ ‵trans σ₁ σ₂ ] s₁ s₃

    Match-congₗ : {Γ₁ Γ₁' Γ₂ Γ₂' : Tree T}
                → {σ₁ : Γ₁ ≅ Γ₁'}
                → (σ₂ : Γ₂ ≅ Γ₂')
                → ∀{a}  (s₁  : a  ∈ Γ₁)
                → ∀{a'} (s₁' : a' ∈ Γ₁')
                → Match[       σ₁    ] (site s₁)             (site s₁')
                → Match[ ‵cong σ₁ σ₂ ] (site (thereˡ Γ₂ s₁)) (site (thereˡ Γ₂' s₁'))
    Match-congᵣ : {Γ₁ Γ₁' Γ₂ Γ₂' : Tree T}
                → (σ₁ : Γ₁ ≅ Γ₁')
                → {σ₂ : Γ₂ ≅ Γ₂'}
                → ∀{a}  (s₂  : a  ∈ Γ₂)
                → ∀{a'} (s₂' : a' ∈ Γ₂')
                → Match[          σ₂ ] (site s₂)             (site s₂')
                → Match[ ‵cong σ₁ σ₂ ] (site (thereʳ Γ₁ s₂)) (site (thereʳ Γ₁' s₂'))

  module _ where
    ‵index- : {Γ₁ Γ₂ : Tree T} (σ : Γ₁ ≅ Γ₂)
            → ∀{a} → (ix : a ∈ Γ₁)
            → Match[ σ ] (site ix) (site (‵index σ ix))
    ‵index- (‵cong σ₁ σ₂) (thereˡ _ ix)
      = Match-congₗ _ _ _ (‵index- σ₁ _)
    ‵index- (‵cong σ₁ σ₂) (thereʳ _ ix)
      = Match-congᵣ _ _ _ (‵index- σ₂ _)
    ‵index- (‵trans σ₁ σ₂) _
      = Match-trans (‵index- σ₁ _) (‵index- σ₂ _)
    ‵index- (‵refl _) _
      = Match-refl _
    ‵index- (‵swap _ _) (thereˡ _ ix)
      = Match-swapₗ _ ix
    ‵index- (‵swap _ _) (thereʳ _ ix)
      = Match-swapᵣ _ ix
    ‵index- (‵assoc _ _ _) (thereˡ _ (thereˡ _ ix))
      = Match-assoc₁ _ ix
    ‵index- (‵assoc _ _ _) (thereˡ _ (thereʳ _ ix))
      = Match-assoc₂ _ ix
    ‵index- (‵assoc _ _ _) (thereʳ _           ix )
      = Match-assoc₃ _ ix

  -- Tree is a monad.
  module _ where
    map : (T' : Type) → (T → T') → (Tree T → Tree T')
    map _ f ∅ = ∅
    map _ f (leaf x) = leaf (f x)
    map _ f (x ∗ y) = (map _ f x) ∗ (map _ f y)

    pure : T → Tree T
    pure = leaf

    flatten : Tree (Tree T) → Tree T
    flatten ∅ = ∅
    flatten (leaf Γ) = Γ
    flatten (Γ₁ ∗ Γ₂) = flatten Γ₁ ∗ flatten Γ₂

    -- The natural transformations on the Tree monad
    -- extend to operations on sites.
    ‵map : {Γ : Tree T} {a : T}
         → (T' : Type) → (f : T → T')
         → ((a ∈ Γ) → (f a ∈ map _ f Γ))
    ‵map _ f here = here
    ‵map _ f (thereˡ _ x) = thereˡ _ (‵map _ f x)
    ‵map _ f (thereʳ _ x) = thereʳ _ (‵map _ f x)

    ‵pure : (a : T) → (a ∈ pure a)
    ‵pure a = here

    ‵flatten : ∀{a : T} {Γ₁ Γ₂}
             → (Γ₂ ∈ Γ₁)
             → (a ∈ Γ₂)
             → (a ∈ flatten Γ₁)
    ‵flatten here x = x
    ‵flatten (thereˡ r x) x₁ = thereˡ (flatten r) (‵flatten x x₁)
    ‵flatten (thereʳ l x) x₁ = thereʳ (flatten l) (‵flatten x x₁)
```
