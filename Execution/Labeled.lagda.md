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
    using (_⊎_)
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
  record Cat' (O : Type) (Hom : O → O → Type) : Type where
    field _;_ : {a b c : O} → Hom a b → Hom b c → Hom a c
    field id  : (a : O) → Hom a a

    field _⊗_    : O → O → O
    field proj₁  : (a b : O) → Hom (a ⊗ b) a
    field proj₂  : (a b : O) → Hom (a ⊗ b) b
    field ⟨_,_⟩  : {a b a' b' : O} → Hom a b → Hom a' b' → Hom (a ⊗ a') (b ⊗ b')
    field ⊗-swap : (a a' : O) → Hom (a ⊗ a') (a' ⊗ a)

    field _⊕_   : O → O → O
    field inj₁  : (a b : O) → Hom a (a ⊕ b)
    field inj₂  : (a b : O) → Hom b (a ⊕ b)
    field [_,_] : {a b a' b' : O} → Hom a b → Hom a' b' → Hom (a ⊕ a') (b ⊕ b')
    field ⊕-swap : (a a' : O) → Hom (a ⊕ a') (a' ⊕ a)

    field distribute : (a b c : O) → Hom ((a ⊕ b) ⊗ c) ((a ⊗ c) ⊕ (b ⊗ c))
    field factor     : (a b c : O) → Hom ((a ⊗ c) ⊕ (b ⊗ c))((a ⊕ b) ⊗ c)

    field 𝟘      : O
    field 𝟘-init : (a : O) → Hom 𝟘 a

    field 𝟙      : O
    field 𝟙-term : (a : O) → Hom a 𝟙

    field ;-idˡ : (a b : O) → (f : Hom a b) → (id a ; f) ≡ f
    field ;-idʳ : (a b : O) → (f : Hom a b) → (f ; id b) ≡ f
    field ;-assoc : (a b c d : O) → (f : Hom a b) (g : Hom b c) (h : Hom c d)
                  → (f ; (g ; h)) ≡ ((f ; g) ; h)

    field ⊗-id : (a a' : O) → ⟨ id a , id a' ⟩ ≡ id (a ⊗ a')
    field ⊗-seq : {a b a' b' a'' b'' : O} → (f : Hom a a') (g : Hom b b') (f' : Hom a' a'') (g' : Hom b' b'')
                → ⟨ f , g ⟩ ; ⟨ f' , g' ⟩ ≡ ⟨ (f ; f') , (g ; g') ⟩
    field ⊗-swap² : (a a' : O) → (⊗-swap a a' ; ⊗-swap a' a) ≡ id (a ⊗ a')
    field 𝟙-uniq : (a : O) → (f g : Hom a 𝟙) → f ≡ g

    field ⊕-id : (a a' : O) → [ id a , id a' ] ≡ id (a ⊕ a')
    field ⊕-seq : {a b a' b' a'' b'' : O} → (f : Hom a a') (g : Hom b b') (f' : Hom a' a'') (g' : Hom b' b'')
                → [ f , g ] ; [ f' , g' ] ≡ [ (f ; f') , (g ; g') ]
    field ⊕-swap² : (a a' : O) → (⊕-swap a a' ; ⊕-swap a' a) ≡ id (a ⊕ a')
    field 𝟘-uniq : (a : O) → (f g : Hom 𝟘 a) → f ≡ g

  module _ (T : Type) (Π : {Γ : Tree} → Tree[ Γ ] T → T) {- (_≤_ : T → T → Type) -} where
    _⊗_ : T → T → T
    l ⊗ l' = Π (l , l')

    𝟙 : T
    𝟙 = Π tt

    Foo : ∀{Γ₁ Γ₂} → (exec : Γ₁ ⇶ Γ₂)
         → (l₁ : Tree[ Γ₁ ] T) (l₂ : Tree[ Γ₂ ] T) → Type
    Foo (x  ∥ x') (l₁ , l₁') (l₂ , l₂') = Foo x l₁ l₂ × Foo x' l₁' l₂'
    Foo (x₁ ⟫ x₂) l₁ l₂ = ∃[ lₘ ] (Foo x₁ l₁ lₘ × Foo x₂ lₘ l₂)
    Foo tick l₁ l₂ = ⊤ -- l₁ ≤ l₂
    Foo fork l₁ (l₂ , l₂') = (l₁ ≡ l₂ ⊗ l₂') -- (l₂ ⊗ l₂' ≤ l₁) × (l₁ ≤ l₂) × (l₁ ≤ l₂')
    Foo join (l₁ , l₁') l₂ = (l₁ ⊗ l₁' ≡ l₂) -- (l₂ ≤ l₁ ⊗ l₁') × (l₁ ≤ l₂) × (l₁' ≤ l₂)
    Foo init _ l₂ = 𝟙 ≡ l₂
    Foo term l₁ _ = l₁ ≡ 𝟙
    Foo (perm σ) l₁ l₂ = l₁ ≡ permute σ l₂
```
