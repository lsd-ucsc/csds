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
    using (⊤; tt)
  open import Data.Product
    using (_×_; _,_)
  open import Data.Nat
    as ℕ
    using (ℕ)
  open import Data.Nat.Properties
    as ℕ-Prop
    using ()
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)
    renaming (trans to infixl 20 _∙_)

  infix 6 _∗_
```

</details>

```agda
  data Tree : Type where
    ∅    :               Tree
    site :               Tree
    _∗_  : Tree → Tree → Tree

  -- Equivalence of trees up to balance and order,
  -- establishing ⟨Tree T / _≅_ , _∗_⟩ as a semigroup.
  data _≅_ : (_ _ : Tree) → Type where
    _‵∗_     : ∀{a₁ a₂ b₁ b₂} → (a₁ ≅ a₂) → (b₁ ≅ b₂) → ((a₁ ∗ b₁) ≅ (a₂ ∗ b₂))

    ‵trans   : ∀{a b c} → (a ≅ b) → (b ≅ c) → (a ≅ c)
    ‵refl    : ∀ a      → (a ≅ a)
    ‵swap    : ∀ a b    → (a ∗ b) ≅ (b ∗ a)

    ‵assoc   : ∀ a b c  → ((a ∗  b) ∗ c ) ≅ ( a ∗ (b  ∗ c))
    ‵assoc⁻¹ : ∀ a b c  → ( a ∗ (b  ∗ c)) ≅ ((a ∗  b) ∗ c )

    -- These rules additionally make ⟨Tree T / _≅_ , ∅ , _∗_⟩ a monoid.
    ‵unitₗ   : ∀ a → (∅ ∗ a) ≅      a
    ‵unitₗ⁻¹ : ∀ a →      a  ≅ (∅ ∗ a)

  syntax ‵trans s₁ s₂ = s₁ ∘≅ s₂

  ‵unitᵣ : ∀ a → (a ∗ ∅) ≅  a
  ‵unitᵣ a = ‵trans (‵swap a ∅) (‵unitₗ a)

  ‵unitᵣ⁻¹ : ∀ a →  a ≅ (a ∗ ∅)
  ‵unitᵣ⁻¹ a = ‵trans (‵unitₗ⁻¹ a) (‵swap ∅ a)

  ‵sym : ∀{a b} → (a ≅ b) → (b ≅ a)
  ‵sym (p ‵∗ q)         = ‵sym p ‵∗ ‵sym q
  ‵sym (‵trans   p q)   = ‵trans (‵sym q) (‵sym p)
  ‵sym (‵refl    _)     = ‵refl _
  ‵sym (‵swap    a b)   = ‵swap b a
  ‵sym (‵assoc   a b c) = ‵assoc⁻¹ a b c
  ‵sym (‵assoc⁻¹ a b c) = ‵assoc a b c
  ‵sym (‵unitₗ   a)     = ‵unitₗ⁻¹ a
  ‵sym (‵unitₗ⁻¹ a)     = ‵unitₗ a

  ‶sym : ∀{a b} → (p : a ≅ b) → ‵sym (‵sym p) ≡ p
  ‶sym (p ‵∗ q)         = Eq.cong₂ _‵∗_   (‶sym p) (‶sym q)
  ‶sym (‵trans   p q)   = Eq.cong₂ ‵trans (‶sym p) (‶sym q)
  ‶sym (‵refl    _)     = Eq.refl
  ‶sym (‵swap    a b)   = Eq.refl
  ‶sym (‵assoc   a b c) = Eq.refl
  ‶sym (‵assoc⁻¹ a b c) = Eq.refl
  ‶sym (‵unitₗ   a)     = Eq.refl
  ‶sym (‵unitₗ⁻¹ a)     = Eq.refl

  size : Tree → ℕ
  size ∅       = 0
  size site    = 1
  size (a ∗ b) = size a ℕ.+ size b

  ‵size : ∀{a b} → (a ≅ b) → (size a ≡ size b)
  ‵size (p ‵∗ q)         = Eq.cong₂ ℕ._+_ (‵size p) (‵size q)
  ‵size (‵trans   p q)   = Eq.trans (‵size p) (‵size q)
  ‵size (‵refl    _)     = Eq.refl
  ‵size (‵swap    a b)   = ℕ-Prop.+-comm (size a) (size b)
  ‵size (‵assoc   a b c) =         ℕ-Prop.+-assoc (size a) (size b) (size c)
  ‵size (‵assoc⁻¹ a b c) = Eq.sym (ℕ-Prop.+-assoc (size a) (size b) (size c))
  ‵size (‵unitₗ   a)     = Eq.refl
  ‵size (‵unitₗ⁻¹ a)     = Eq.refl


  Tree[_] : Tree → Type → Type
  Tree[ ∅       ] L = ⊤
  Tree[ site    ] L = L
  Tree[ Γ₁ ∗ Γ₂ ] L = Tree[ Γ₁ ] L × Tree[ Γ₂ ] L

  permute : ∀{L Γ₁ Γ₂} → (Γ₁ ≅ Γ₂) → (Tree[ Γ₂ ] L → Tree[ Γ₁ ] L)
  permute (σ₁ ‵∗ σ₂)        (l₁ , l₂)        = (permute σ₁ l₁ , permute σ₂ l₂)
  permute (‵trans   σ₁ σ₂)  l                = (permute σ₁ ∘ permute σ₂) l
  permute (‵refl    _)      l                = l
  permute (‵swap    _ _)    (l₁ , l₂)        = (l₂ , l₁)
  permute (‵assoc   _ _ _)  (l₁ , (l₂ , l₃)) = ((l₁ , l₂) , l₃)
  permute (‵assoc⁻¹ _ _ _)  ((l₁ , l₂) , l₃) = (l₁ , (l₂ , l₃))
  permute (‵unitₗ   _)      l                = (tt , l)
  permute (‵unitₗ⁻¹ _)      (tt , l)         = l

  map : ∀{L₁ L₂ Γ} → (f : L₁ → L₂) → (Tree[ Γ ] L₁ → Tree[ Γ ] L₂)
  map {Γ = ∅}       f l         = tt
  map {Γ = site}    f l         = f l
  map {Γ = Γ₁ ∗ Γ₂} f (l₁ , l₂) = (map f l₁ , map f l₂)


  data Site : Tree → Type where
    here   :                            Site site
    thereˡ : ∀{l} r  → (ixˡ : Site l) → Site (l ∗ r)
    thereʳ : ∀ l {r} → (ixʳ : Site r) → Site (l ∗ r)

  lookup : {L : Type} {Γ : Tree} → Tree[ Γ ] L → (Site Γ → L)
  lookup {Γ = site}    l       s            = l
  lookup {Γ = Γ₁ ∗ Γ₂} (l , _) (thereˡ _ s) = lookup l s
  lookup {Γ = Γ₁ ∗ Γ₂} (_ , l) (thereʳ _ s) = lookup l s

  tabulate : ∀{L} Γ → (Site Γ → L) → Tree[ Γ ] L
  tabulate ∅         f = tt
  tabulate site      f = f here
  tabulate (Γ₁ ∗ Γ₂) f = (tabulate Γ₁ (f ∘ thereˡ _) , tabulate Γ₂ (f ∘ thereʳ _))

  eigentree : ∀ Γ → Tree[ Γ ] (Site Γ)
  eigentree Γ = tabulate Γ (λ s → s)

  repeat : ∀{L} Γ → (l : L) → Tree[ Γ ] L
  repeat Γ l = tabulate Γ (λ _ → l)

  forward : {Γ₁ Γ₂ : Tree}
          → (Γ₁ ≅ Γ₂)
          → Site Γ₁ → Site Γ₂
  forward σ = lookup (permute σ (eigentree _))


  permute-sym : ∀{L Γ₁ Γ₂} → (σ : Γ₁ ≅ Γ₂) → (l : Tree[ Γ₁ ] L)
              → permute (‵trans σ (‵sym σ)) l ≡ l
  permute-sym (σ₁ ‵∗ σ₂)       (l₁ , l₂) =
    Eq.cong₂ _,_ (permute-sym σ₁ l₁) (permute-sym σ₂ l₂)
  permute-sym (‵trans σ₁ σ₂)   l =
    ( Eq.cong (permute σ₁) (permute-sym σ₂ (permute (‵sym σ₁) l))
    ∙ permute-sym σ₁ l )
  permute-sym (‵refl    _)     _ = Eq.refl
  permute-sym (‵swap    _ _)   _ = Eq.refl
  permute-sym (‵assoc   _ _ _) _ = Eq.refl
  permute-sym (‵assoc⁻¹ _ _ _) _ = Eq.refl
  permute-sym (‵unitₗ   _)     _ = Eq.refl
  permute-sym (‵unitₗ⁻¹ _)     _ = Eq.refl

  permute-sym' : ∀{L Γ₁ Γ₂} → (σ : Γ₁ ≅ Γ₂) → (l : Tree[ Γ₂ ] L)
              → permute (‵trans (‵sym σ) σ) l ≡ l
  permute-sym' (σ₁ ‵∗ σ₂)       (l₁ , l₂) =
    Eq.cong₂ _,_ (permute-sym' σ₁ l₁) (permute-sym' σ₂ l₂)
  permute-sym' (‵trans σ₁ σ₂)   l =
    ( Eq.cong (permute (‵sym σ₂)) (permute-sym' σ₁ (permute σ₂ l))
    ∙ permute-sym' σ₂ l )
  permute-sym' (‵refl    _)     _ = Eq.refl
  permute-sym' (‵swap    _ _)   _ = Eq.refl
  permute-sym' (‵assoc   _ _ _) _ = Eq.refl
  permute-sym' (‵assoc⁻¹ _ _ _) _ = Eq.refl
  permute-sym' (‵unitₗ   _)     _ = Eq.refl
  permute-sym' (‵unitₗ⁻¹ _)     _ = Eq.refl

  lookup-tabulate : ∀{L Γ} → (f : Site Γ → L)
                  → ∀ s → lookup (tabulate Γ f) s ≡ f s
  lookup-tabulate f here         = Eq.refl
  lookup-tabulate f (thereˡ _ s) = lookup-tabulate (f ∘ thereˡ _) s
  lookup-tabulate f (thereʳ _ s) = lookup-tabulate (f ∘ thereʳ _) s

  tabulate-lookup : ∀{L Γ} → (l : Tree[ Γ ] L)
                  → tabulate Γ (lookup {Γ = Γ} l) ≡ l
  tabulate-lookup {Γ = ∅}       tt        = Eq.refl
  tabulate-lookup {Γ = site}    l         = Eq.refl
  tabulate-lookup {Γ = Γ₁ ∗ Γ₂} (l₁ , l₂) =
    Eq.cong₂ _,_
      (tabulate-lookup {Γ = Γ₁} l₁)
      (tabulate-lookup {Γ = Γ₂} l₂)

  map-permute : ∀{L₁ L₂ Γ₁ Γ₂} (σ : Γ₁ ≅ Γ₂) (l : Tree[ Γ₂ ] L₁) (f : L₁ → L₂)
              → map f (permute σ l) ≡ permute σ (map f l)
  map-permute (σ₁ ‵∗ σ₂) (l₁ , l₂) f = Eq.cong₂ _,_ (map-permute σ₁ l₁ f) (map-permute σ₂ l₂ f)
  map-permute (‵trans σ₁ σ₂) l f = Eq.trans (map-permute σ₁ (permute σ₂ l) f) (Eq.cong (permute σ₁) (map-permute σ₂ l f))
  map-permute (‵refl _) l f = Eq.refl
  map-permute (‵swap a b) l f = Eq.refl
  map-permute (‵assoc a b c) l f = Eq.refl
  map-permute (‵assoc⁻¹ a b c) l f = Eq.refl
  map-permute (‵unitₗ _) l f = Eq.refl
  map-permute (‵unitₗ⁻¹ _) l f = Eq.refl

  map-tabulate : ∀{L₁ L₂ : Type} {Γ} → (f : Site Γ → L₁) → (g : L₁ → L₂)
               → map g (tabulate Γ f) ≡ tabulate Γ (g ∘ f)
  map-tabulate {Γ = ∅}       f g = Eq.refl
  map-tabulate {Γ = site}    f g = Eq.refl
  map-tabulate {Γ = Γ₁ ∗ Γ₂} f g = Eq.cong₂ _,_ (map-tabulate (f ∘ thereˡ _) g) (map-tabulate (f ∘ thereʳ _) g)

  map-lookup : ∀{L₁ L₂ : Type} {Γ} → (f : L₁ → L₂) → (l : Tree[ Γ ] L₁)
             → ∀ s → f (lookup l s) ≡ lookup (map f l) s
  map-lookup f l       here         = Eq.refl
  map-lookup f (l , _) (thereˡ _ s) = map-lookup f l s
  map-lookup f (_ , l) (thereʳ _ s) = map-lookup f l s

  tabulate-eta : ∀{L} Γ → (f g : Site Γ → L)
               → (∀ s → f s ≡ g s)
               → tabulate Γ f ≡ tabulate Γ g
  tabulate-eta ∅         f g p = Eq.refl
  tabulate-eta site      f g p = p here
  tabulate-eta (Γ₁ ∗ Γ₂) f g p = Eq.cong₂ _,_ (tabulate-eta Γ₁ _ _ (p ∘ thereˡ _)) (tabulate-eta Γ₂ _ _ (p ∘ thereʳ _))

  permute-tabulate : ∀{L Γ₁ Γ₂} (σ : Γ₁ ≅ Γ₂) (f : Site Γ₂ → L)
                   → tabulate Γ₁ (f ∘ forward σ) ≡ permute σ (tabulate Γ₂ f)
  permute-tabulate {Γ₁ = Γ₁} {Γ₂ = Γ₂} σ f =
    ( tabulate-eta Γ₁ _ _ (map-lookup f (permute σ (tabulate Γ₂ (λ s → s))))
    ∙ tabulate-lookup {Γ = Γ₁} (map f (permute σ (tabulate Γ₂ (λ s → s))))
    ∙ map-permute σ (tabulate Γ₂ (λ s → s)) f
    ∙ Eq.cong (permute σ) (map-tabulate (λ s → s) f) )

  forward-sym : {Γ₁ Γ₂ : Tree} (σ : Γ₁ ≅ Γ₂)
              → (s : Site Γ₁)
              → (forward (‵sym σ) ∘ forward σ) s ≡ s
  forward-sym {Γ₁ = Γ₁} {Γ₂} σ s =
    ( map-lookup (forward (‵sym σ)) (permute σ (tabulate Γ₂ (λ ■ → ■))) s
    ∙ Eq.cong (λ ▢ → lookup ▢ s)
      ( map-permute σ (tabulate Γ₂ (λ ■ → ■)) (map (lookup (permute (‵sym σ) (tabulate Γ₁ (λ ■ → ■)))))
      ∙ Eq.cong (permute σ)
        ( map-tabulate (λ ■ → ■) (lookup {Γ = Γ₂} (permute (‵sym σ) (tabulate Γ₁ (λ s₁ → s₁))))
        ∙ tabulate-lookup {Γ = Γ₂} (permute (‵sym σ) (tabulate Γ₁ (λ ■ → ■))) )
      ∙ permute-sym σ (tabulate Γ₁ λ ■ → ■) )
    ∙ lookup-tabulate (λ ■ → ■) s )

  lookup-forward : {L : Type} {Γ₁ Γ₂ : Tree} (σ : Γ₁ ≅ Γ₂)
                 → (l : Tree[ Γ₂ ] L)
                 → (s : Site Γ₁)
                 → lookup l (forward σ s) ≡ lookup (permute σ l) s
  lookup-forward {Γ₁ = Γ₁} {Γ₂ = Γ₂} σ l s =
    ( map-lookup (lookup l) (permute σ (tabulate Γ₂ (λ ■ → ■))) s
    ∙ Eq.cong (λ ▢ → lookup ▢ s)
      ( map-permute σ (tabulate Γ₂ (λ ■ → ■)) (lookup l)
      ∙ Eq.cong (permute σ)
        ( map-tabulate {Γ = Γ₂} (λ ■ → ■) (lookup l)
        ∙ tabulate-lookup {Γ = Γ₂} l ) ) )
```
