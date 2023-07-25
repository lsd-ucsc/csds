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
  open import Data.Unit
    using (⊤)
  open import Data.Product
    using (Σ-syntax; ∃-syntax; _×_)
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
  data Tree : Type where
    ∅   : Tree
    ■   : Tree
    _∗_ : Tree → Tree → Tree

  data Site : Tree → Type where
    here   : Site ■
    thereˡ : ({Γ₁} Γ₂  : Tree) → Site Γ₁ → Site (Γ₁ ∗ Γ₂)
    thereʳ : ( Γ₁ {Γ₂} : Tree) → Site Γ₂ → Site (Γ₁ ∗ Γ₂)


  data _⇶_ : Tree → Tree → Type where
    noop : (Γ : Tree) → (Γ ⇶ Γ)

    -- Composition
    _∥_ : {Γ₁ Γ₂ Γ₃ Γ₄ : Tree}
        → ( Γ₁       ⇶  Γ₃      )
        → (      Γ₂  ⇶       Γ₄ )
        → ((Γ₁ ∗ Γ₂) ⇶ (Γ₃ ∗ Γ₄))
    _;_ : {Γ₁ Γ₂ Γ₃ : Tree}
        → (Γ₁ ⇶ Γ₂)
        →      (Γ₂ ⇶ Γ₃)
        → (Γ₁   ⇶    Γ₃)

    -- Local transformations
    tick :    ■    ⇶    ■
    fork :    ■    ⇶ (■ ∗ ■)
    join : (■ ∗ ■) ⇶    ■
    init :    ∅    ⇶    ■
    term :    ■    ⇶    ∅

    -- Permutations
    emp₁ :    ■    ⇶ (■ ∗ ∅)
    emp₂ : (■ ∗ ∅) ⇶    ■
    swap : (■ ∗ ■) ⇶ (■ ∗ ■)
    rota : ((■ ∗  ■) ∗ ■ )
         ⇶ ( ■ ∗ (■  ∗ ■))

  initial[_] : ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂) → Tree
  initial[_] {Γ₁ = Γ₁} _ = Γ₁

  final[_] : ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂) → Tree
  final[_] {Γ₂ = Γ₂} _ = Γ₂


  data Tick : ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂) → Type where
    here : Tick tick
    thereˡ : ∀{Γ₁ Γ₂ Γ₁' Γ₂'}
           → {left  : Γ₁  ⇶ Γ₂ }
           → (right : Γ₁' ⇶ Γ₂')
           → Tick left
           → Tick (left ∥ right)
    thereʳ : ∀{Γ₁ Γ₂ Γ₁' Γ₂'}
           → (left  : Γ₁  ⇶ Γ₂ )
           → {right : Γ₁' ⇶ Γ₂'}
           → Tick right
           → Tick (left ∥ right)
    thenᵇ : ∀{Γ₁ Γᵢ Γ₂}
          → {prefix : Γ₁ ⇶ Γᵢ}
          → (suffix : Γᵢ ⇶ Γ₂)
          → Tick prefix
          → Tick (prefix ; suffix)
    thenᶠ : ∀{Γ₁ Γᵢ Γ₂}
          → (prefix : Γ₁ ⇶ Γᵢ)
          → {suffix : Γᵢ ⇶ Γ₂}
          → Tick suffix
          → Tick (prefix ; suffix)

  data Layer : Type where
    Par Seq : Layer

  -- A foliation is a sequential list of concurrent steps.
  -- That is, it is a diagram in which concurrent composition only appears
  -- under sequential composition, with all sequential compositions
  -- fully left-associated, with an initial `noop` to start the sequence.
  IsFoliation[_] : (k : Layer) → ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂) → Type
  -- A sequential composition is a foliation at the Seq layer,
  -- as long as its constituents are as well.
  IsFoliation[ k ] (x ; y)  = (k ≡ Seq) × IsFoliation[ Seq ] x × IsFoliation[ Par ] y
  -- A concurrent composition is a foliation at the Par layer,
  -- as long as its constituents are as well.
  IsFoliation[ k ] (x ∥ y)  = (k ≡ Par) × IsFoliation[ Par ] x × IsFoliation[ Par ] y
  -- The `noop` diagrams is a foliation at either Seq or Par layer.
  IsFoliation[ k ] (noop _) = (      ⊤)
  -- All other atomic diagrams are foliations only at Par.
  IsFoliation[ k ] tick     = (k ≡ Par)
  IsFoliation[ k ] fork     = (k ≡ Par)
  IsFoliation[ k ] join     = (k ≡ Par)
  IsFoliation[ k ] init     = (k ≡ Par)
  IsFoliation[ k ] term     = (k ≡ Par)
  IsFoliation[ k ] emp₁     = (k ≡ Par)
  IsFoliation[ k ] emp₂     = (k ≡ Par)
  IsFoliation[ k ] swap     = (k ≡ Par)
  IsFoliation[ k ] rota     = (k ≡ Par)

  IsFoliation : ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂) → Type
  IsFoliation = IsFoliation[ Seq ]

  -- !!! this isn't actually sufficient to define Event unless `exec` is a foliation !!!
  -- for instance, we'll miss the initial cut if the diagram doesn't begin on a `noop`.
  -- and we'll *definitely* miss events on cuts along a `;` buried under a `∥`.
  --
  -- consider instead defining interior cuts first, then tacking on the terminal cuts.
  -- an interior cut is anywhere along a `;`, and cuts in a `∥` are a pair of cuts.
  --
  -- alternatively, just require that `exec` be a foliation,
  -- and prove that events in subdiagrams lift uniquely to events in larger diagrams.
  data Cut {Γ₁ Γ₂} : (exec : Γ₁ ⇶ Γ₂) → Type where
    now  : (exec : Γ₁ ⇶ Γ₂)
         → Cut exec
    back : ∀{Γᵢ} {prefix : Γ₁ ⇶ Γᵢ} (suffix : Γᵢ ⇶ Γ₂)
         → Cut prefix
         → Cut (prefix ; suffix)

  cut : ∀{Γ₁ Γ₂} {exec : Γ₁ ⇶ Γ₂} → Cut exec → Tree
  cut (now exec) = final[ exec ]
  cut (back _ c) = cut c

  Event : ∀{Γ₁ Γ₂} → (Γ₁ ⇶ Γ₂) → Type
  Event exec = Σ[ c ∈ Cut exec ] Site (cut c)


{-
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
-}
```
