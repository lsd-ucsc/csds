<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
open import Data.Bool using (Bool)

module Choreographies.Foo {Loc : Type} {_≟_ : (_ _ : Loc) → Bool} where
```

<details>
<summary>Imports, variables, and fixity</summary>

```agda
  open import Function
    using (_∘_)
  open import Data.Unit
    using (⊤; tt)
  open import Data.Bool
    using (Bool; true; false)
    using (if_then_else_)
  open import Data.Product
    using (_×_; _,_; ∃-syntax; proj₁; proj₂)
  open import Data.Sum
    using (_⊎_)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)
  open import Execution.Core
    using (_⇶_; perm; tick; fork; join; init; term; _∥_; _⟫_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; site; _∗_; Tree[_])
    using (_≅_; _‵∗_; ‵trans; ‵refl; ‵swap; ‵assoc; ‵assoc⁻¹; ‵unitₗ; ‵unitₗ⁻¹)

  variable
    Γ  Γ₁ Γ₂ : Tree
```
</details>

```agda
  data Ty : Type where
    𝟙 : Ty
    _∗_ : Ty → Ty → Ty

  ⟦_⟧ : Ty → Type
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ τ₁ ∗ τ₂ ⟧ = ⟦ τ₁ ⟧ × ⟦ τ₂ ⟧

  _⟶_ : Ty → Ty → Type
  τ₁ ⟶ τ₂ = ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧

  Located : Type → Type
  Located T = T × Loc

  _＠_ : {T : Type} → T → Loc → Located T
  t ＠ l = (t , l)

  -- The type of choreographic actions.
  data _⇒_ : (τ₁ τ₂ : (Ty × Loc)) → Type where
    locally  : ∀ l {τ₁ τ₂} → (τ₁ ⟶  τ₂) → (τ₁ ＠ l)   ⇒ (τ₂ ＠ l)
    transmit : ∀ {τ} → (src dst : Loc)   → (τ  ＠ src) ⇒ (τ  ＠ dst)

  Actions : (Γ₁ ⇶ Γ₂) → Tree[ Γ₁ ] (Located Ty) → Tree[ Γ₂ ] (Located Ty) → Type
  Actions (x ∥ y) (τ₁ , τ₁') (τ₂ , τ₂') = Actions x τ₁ τ₂ × Actions y τ₁' τ₂'
  Actions (x ⟫ y) τ₁ τ₂ = ∃[ τₘ ] Actions x τ₁ τₘ × Actions y τₘ τ₂
  Actions tick τ₁ τ₂ = τ₁ ⇒ τ₂
  Actions (perm σ) τ₁ τ₂ = τ₁ ≡ Sites.permute σ τ₂
  Actions fork (τ₁ , l₁) ((τ₂ , l₂) , (τ₂' , l₂')) = (τ₁ ≡ τ₂ ∗ τ₂') × (l₁ ≡ l₂) × (l₁ ≡ l₂')
  Actions join ((τ₁ , l₁) , (τ₁' , l₁')) (τ₂ , l₂) = (τ₂ ≡ τ₁ ∗ τ₁') × (l₁ ≡ l₂) × (l₁' ≡ l₂)
  Actions init _ (τ₂ , l₂) = 𝟙 ≡ τ₂
  Actions term (τ₁ , l₁) _ = τ₁ ≡ 𝟙

  module CentralizedSemantics where
    Localize : Tree[ Γ ] (Located Ty) → Ty
    Localize {Γ = ∅} _ = 𝟙
    Localize {Γ = site} (τ , l) = τ
    Localize {Γ = Γ₁ ∗ Γ₂} (τ₁ , τ₂) = Localize τ₁ ∗ Localize τ₂

    localize' : (σ : Γ₁ ≅ Γ₂) (τ₂ : Tree[ Γ₂ ] (Located Ty)) → (Localize (Sites.permute σ τ₂) ⟶ Localize τ₂)
    localize' (σ₁ ‵∗ σ₂)       (τ₂ , τ₂') = λ(x , y) → (localize' σ₁ τ₂ x , localize' σ₂ τ₂' y)
    localize' (‵trans   σ₁ σ₂) τ₂ = (localize' σ₂ τ₂ ∘ localize' σ₁ _)
    localize' (‵refl    _    ) τ₂ = λ x → x
    localize' (‵swap    _ _  ) τ₂ = λ(x , y) → (y , x)
    localize' (‵assoc   _ _ _) τ₂ = λ((x , y) , z) → (x , (y , z))
    localize' (‵assoc⁻¹ _ _ _) τ₂ = λ(x , (y , z)) → ((x , y) , z)
    localize' (‵unitₗ   _    ) τ₂ = λ(tt , y) → y
    localize' (‵unitₗ⁻¹ _    ) τ₂ = λ y → (tt , y)

    localize : ∀{Γ₁ Γ₂} → (exec : Γ₁ ⇶ Γ₂)
             → (τ₁ : Tree[ Γ₁ ] (Located Ty)) → (τ₂ : Tree[ Γ₂ ] (Located Ty)) → (m : Actions exec τ₁ τ₂)
             → (Localize τ₁ ⟶ Localize τ₂)
    localize tick _ _ (locally _ act) = act
    localize tick _ _ (transmit _ _) = λ z → z
    localize (perm σ) _ τ₂ Eq.refl = localize' σ τ₂
    localize fork _ _ (Eq.refl , _ , _) = λ x → x
    localize join _ _ (Eq.refl , _ , _) = λ x → x
    localize init _ _ Eq.refl = λ x → x
    localize term _ _ Eq.refl = λ x → x
    localize (f ∥ g) (τ₁ , τ₁') (τ₂ , τ₂') (act₁ , act₂) = λ(x , y) →
      ( localize f τ₁  τ₂  act₁ x
      , localize g τ₁' τ₂' act₂ y )
    localize (f ⟫ g) τ₁ τ₂ (τₘ , act₁ , act₂) =
      ( localize g τₘ τ₂ act₂
      ∘ localize f τ₁ τₘ act₁ )

  module DistributedSemantics where
    -- The type of network programs.
    data _⇒'_ : (_ _ : Ty) → Type where
      locally : ∀ {τ₁ τ₂} → (τ₁ ⟶ τ₂) → τ₁ ⇒' τ₂
      send    : ∀ {τ} → (dst : Loc) → (τ ⇒' 𝟙)
      recv    : ∀ {τ} → (src : Loc) → (𝟙 ⇒' τ)

    Actions' : (Γ₁ ⇶ Γ₂) → Tree[ Γ₁ ] Ty → Tree[ Γ₂ ] Ty → Type
    Actions' (x ∥ y) (τ₁ , τ₁') (τ₂ , τ₂') = Actions' x τ₁ τ₂ × Actions' y τ₁' τ₂'
    Actions' (x ⟫ y) τ₁ τ₂ = ∃[ τₘ ] Actions' x τ₁ τₘ × Actions' y τₘ τ₂
    Actions' tick τ₁ τ₂ = τ₁ ⇒' τ₂
    Actions' (perm σ) τ₁ τ₂ = τ₁ ≡ Sites.permute σ τ₂
    Actions' fork τ₁ (τ₂ , τ₂') = (τ₁ ≡ τ₂ ∗ τ₂')
    Actions' join (τ₁ , τ₁') τ₂ = (τ₁ ∗ τ₁' ≡ τ₂)
    Actions' init _ τ₂ = 𝟙 ≡ τ₂
    Actions' term τ₁ _ = τ₁ ≡ 𝟙

    Epp-Γ : Tree[ Γ ] (Located Ty)
          → (Loc → Tree)
    Epp-Γ {Γ = ∅} _ self = ∅
    Epp-Γ {Γ = site} (τ , l) self = if self ≟ l then site else ∅
    Epp-Γ {Γ = Γ₁ ∗ Γ₂} (τ₁ , τ₂) self = Epp-Γ τ₁ self ∗ Epp-Γ τ₂ self

    Epp : (τ : Tree[ Γ ] (Located Ty))
        → ((self : Loc) → Tree[ Epp-Γ τ self ] Ty)
    Epp {Γ = ∅}       τ         self = τ
    Epp {Γ = site}    (τ , l)   self with self ≟ l
    ... | true  = τ
    ... | false = tt
    Epp {Γ = Γ₁ ∗ Γ₂} (τ₁ , τ₂) self = (Epp τ₁ self , Epp τ₂ self)

    epp-σ : (σ : Γ₁ ≅ Γ₂) (τ : Tree[ Γ₂ ] (Located Ty))
          → ((self : Loc) → (Epp-Γ (Sites.permute σ τ) self ≅ Epp-Γ τ self))
    epp-σ (‵refl _)        _ _ = ‵refl _
    epp-σ (‵swap _ _)      _ _ = ‵swap _ _
    epp-σ (‵assoc   _ _ _) _ _ = ‵assoc   _ _ _
    epp-σ (‵assoc⁻¹ _ _ _) _ _ = ‵assoc⁻¹ _ _ _
    epp-σ (‵unitₗ   _)     _ _ = ‵unitₗ   _
    epp-σ (‵unitₗ⁻¹ _)     _ _ = ‵unitₗ⁻¹ _
    epp-σ (σ ‵∗ σ') (τ , τ') self =
      (  epp-σ σ  τ  self
      ‵∗ epp-σ σ' τ' self )
    epp-σ (‵trans σ₁ σ₂) τ self =
      ‵trans
        (epp-σ σ₁ _ self)
        (epp-σ σ₂ τ self)

    epp : (exec : Γ₁ ⇶ Γ₂) (τ₁ : Tree[ Γ₁ ] (Located Ty)) (τ₂ : Tree[ Γ₂ ] (Located Ty)) (acts : Actions exec τ₁ τ₂)
        → ((self : Loc) → (Epp-Γ τ₁ self ⇶ Epp-Γ τ₂ self))
    epp tick _ _ (locally l act) self with self ≟ l
    ... | true  = tick -- locally act
    ... | false = perm (‵refl _)
    epp tick _ _ (transmit src dst) self with self ≟ src | self ≟ dst
    ... | true  | true  = perm (‵refl _)
    ... | false | false = perm (‵refl _)
    ... | true  | false = tick ⟫ term -- send dst
    ... | false | true  = init ⟫ tick -- recv src
    epp fork (_ , l₁) _ (p₁ , Eq.refl , Eq.refl) self with self ≟ l₁
    ... | true  = fork
    ... | false = perm (‵unitₗ⁻¹ ∅)
    epp join _ (_ , l₂) (p₁ , Eq.refl , Eq.refl) self with self ≟ l₂
    ... | true  = join
    ... | false = perm (‵unitₗ ∅)
    epp init _ (_ , l₂) acts self with self ≟ l₂
    ... | true  = init
    ... | false = perm (‵refl _)
    epp term (_ , l₁) _ acts self with self ≟ l₁
    ... | true  = term
    ... | false = perm (‵refl _)
    epp (perm σ) _ _ Eq.refl _ = perm (epp-σ σ _ _)
    epp (x  ∥ x') (τ₁ , τ₁') (τ₂ , τ₂') (acts₁ , acts₂) self =
      ( epp x  τ₁  τ₂  acts₁ self
      ∥ epp x' τ₁' τ₂' acts₂ self )
    epp (x₁ ⟫ x₂) τ₁ τ₂ (τₘ , acts₁ , acts₂) self =
      ( epp x₁ τ₁ τₘ acts₁ self
      ⟫ epp x₂ τₘ τ₂ acts₂ self )

    foo : (σ : Γ₁ ≅ Γ₂) (τ : Tree[ Γ₂ ] (Located Ty)) (self : Loc)
        → Epp (Sites.permute σ τ) self ≡ Sites.permute (epp-σ σ τ self) (Epp τ self)
    foo (‵refl _) τ self = Eq.refl
    foo (‵swap a b) τ self = Eq.refl
    foo (‵assoc a b c) τ self = Eq.refl
    foo (‵assoc⁻¹ a b c) τ self = Eq.refl
    foo (‵unitₗ _) τ self = Eq.refl
    foo (‵unitₗ⁻¹ _) τ self = Eq.refl
    foo (σ ‵∗ σ') (τ , τ') self =
      Eq.cong₂ _,_
        (foo σ τ self)
        (foo σ' τ' self)
    foo (‵trans σ₁ σ₂) τ self =
      Eq.trans
        (foo σ₁ (Sites.permute σ₂ τ) self)
        (Eq.cong (Sites.permute (epp-σ σ₁ (Sites.permute σ₂ τ) self)) (foo σ₂ τ self))

    -- TODO: Generate unique IDs for each `transmi`, so that every pair of `send` and `recv` can be matched up
    -- correctly over the network. If Alice sends two messages in sequence, then Bob needs to be able to receive
    -- those messages in the same order. (Order doesn't really matter, but the point is, each `send` needs to be
    -- matched with exactly one `recv`, and vice versa.)
    epp-acts : (exec : Γ₁ ⇶ Γ₂) (τ₁ : Tree[ Γ₁ ] (Located Ty)) (τ₂ : Tree[ Γ₂ ] (Located Ty)) (acts : Actions exec τ₁ τ₂)
             → ((self : Loc) → Actions' (epp exec τ₁ τ₂ acts self) (Epp τ₁ self) (Epp τ₂ self))
    epp-acts tick _ _ (locally l act) self with self ≟ l
    ... | true  = locally act
    ... | false = Eq.refl
    epp-acts tick _ _ (transmit src dst) self with self ≟ src | self ≟ dst
    ... | true  | true  = Eq.refl
    ... | false | false = Eq.refl
    ... | true  | false = (𝟙 , send dst , Eq.refl)
    ... | false | true  = (𝟙 , Eq.refl , recv src)
    epp-acts fork (_ , l₁) _ (Eq.refl , Eq.refl , Eq.refl) self with self ≟ l₁
    ... | true  = Eq.refl
    ... | false = Eq.refl
    epp-acts join _ (_ , l₂) (Eq.refl , Eq.refl , Eq.refl) self with self ≟ l₂
    ... | true  = Eq.refl
    ... | false = Eq.refl
    epp-acts init _ (_ , l₂) m self with self ≟ l₂
    ... | true  = m
    ... | false = Eq.refl
    epp-acts term (_ , l₁) _ m self with self ≟ l₁
    ... | true  = m
    ... | false = Eq.refl
    epp-acts (perm σ) τ₁ τ₂ Eq.refl self
      = foo σ τ₂ self
    epp-acts (x  ∥ x') (τ₁ , τ₁') (τ₂ , τ₂') (acts₁ , acts₂) self =
      ( epp-acts x  τ₁  τ₂  acts₁ self
      , epp-acts x' τ₁' τ₂' acts₂ self )
    epp-acts (x₁ ⟫ x₂) τ₁ τ₂ (τₘ , acts₁ , acts₂) self =
      ( Epp τₘ self
      , epp-acts x₁ τ₁ τₘ acts₁ self
      , epp-acts x₂ τₘ τ₂ acts₂ self )
```
