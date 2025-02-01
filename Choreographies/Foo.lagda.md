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
    using (_≡_)
  open import Execution.Core
    using (_⇶[_]_; _⇶_; id; perm; tick; fork; join; _∥_; _⟫_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; leaf; _∗_)
    using (_≅_; _‵∗_; ‵trans; ‵refl; ‵swap; ‵assoc; ‵assoc⁻¹)
```

</details>

```agda
  data Ty : Type where
    𝟙 : Ty

  ⟦_⟧ : Tree Ty → Type
  ⟦ ∅ ⟧ = ⊤
  ⟦ leaf 𝟙  ⟧ = ⊤
  ⟦ τ₁ ∗ τ₂ ⟧ = ⟦ τ₁ ⟧ × ⟦ τ₂ ⟧

  _⟶_ : (_ _ : Tree Ty) → Type
  τ₁ ⟶ τ₂ = ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧

  -- The type of choreographic actions.
  data _⇒_ : (_ _ : Tree Ty) → Type where
    locally  : ∀ {τ₁ τ₂} → (τ₁ ⟶ τ₂)  → τ₁ ⇒ τ₂
    transmit : ∀ {τ} → (src dst : Loc) → τ  ⇒ τ

  Actions : ∀{k} {Γ₁ Γ₂ : Tree (Tree Ty)} → (Γ₁ ⇶[ k ] Γ₂) → Type
  Actions (x ∥ y) = Actions x × Actions y
  Actions (x ⟫ y) = Actions x × Actions y
  Actions (tick {a} {b}) = a ⇒ b
  Actions (perm σ) = ⊤
  Actions fork = ⊤
  Actions join = ⊤
  Actions id = ⊤

  module CentralizedSemantics where
    Localize : Tree (Tree Ty) → Tree Ty
    Localize ∅ = ∅
    Localize (Γ₁ ∗ Γ₂) = Localize Γ₁ ∗ Localize Γ₂
    Localize (leaf Γ) = Γ

    localize' : ∀{Γ₁ Γ₂} → (σ : Γ₁ ≅ Γ₂) → (Localize Γ₁ ⟶ Localize Γ₂)
    localize' (σ₁ ‵∗ σ₂)       = λ(x , y) → (localize' σ₁ x , localize' σ₂ y)
    localize' (‵trans   σ₁ σ₂) = (localize' σ₂ ∘ localize' σ₁)
    localize' (‵refl    _    ) = λ x → x
    localize' (‵swap    _ _  ) = λ(x , y) → (y , x)
    localize' (‵assoc   _ _ _) = λ((x , y) , z) → (x , (y , z))
    localize' (‵assoc⁻¹ _ _ _) = λ(x , (y , z)) → ((x , y) , z)

    localize : ∀{k Γ₁ Γ₂} → (exec : Γ₁ ⇶[ k ] Γ₂) → Actions exec
             → (Localize Γ₁ ⟶ Localize Γ₂)
    localize tick (locally  act) = act
    localize tick (transmit _ _) = λ z → z
    localize (perm σ)  _ = localize' σ
    localize id        _ = λ x → x
    localize fork      _ = λ x → x
    localize join      _ = λ x → x
    localize (f ∥ g) (act₁ , act₂) = λ(x , y) →
      ( localize f act₁ x
      , localize g act₂ y )
    localize (f ⟫ g) (act₁ , act₂) =
      ( localize g act₂
      ∘ localize f act₁ )

  module DistributedSemantics where
    -- The type of network programs.
    data _⇒'_ : (_ _ : Tree Ty) → Type where
      locally : ∀ {τ₁ τ₂} → (τ₁ ⟶ τ₂) → τ₁ ⇒' τ₂
      send    : ∀ {τ} → (dst : Loc) → (τ ⇒' ∅)
      recv    : ∀ {τ} → (src : Loc) → (∅ ⇒' τ)

      seq'    : ∀ {τ₁ τ₂ τ₃} → (τ₁ ⇒' τ₂) → (τ₂ ⇒' τ₃) → (τ₁ ⇒' τ₃)
      par'    : ∀ {τ₁ τ₁' τ₂ τ₂'} → (τ₁ ⇒' τ₂) → (τ₁' ⇒' τ₂') → ((τ₁ ∗ τ₁') ⇒' (τ₂ ∗ τ₂'))

    Actions' : ∀{k} {Γ₁ Γ₂ : Tree (Tree Ty)} → (Γ₁ ⇶[ k ] Γ₂) → Type
    Actions' (x ∥ y) = Actions' x × Actions' y
    Actions' (x ⟫ y) = Actions' x × Actions' y
    Actions' (tick {a} {b}) = a ⇒' b
    Actions' (perm σ) = ⊤
    Actions' fork = ⊤
    Actions' join = ⊤
    Actions' id = ⊤

    Located : ∀{T} → (Γ : Tree (Tree T)) → Type
    Located ∅ = ⊤
    Located (leaf Γ) = Loc
    Located (Γ₁ ∗ Γ₂) = Located Γ₁ × Located Γ₂

    WellLocated' : ∀{Γ₁ Γ₂ : Tree (Tree Ty)} (σ : Γ₁ ≅ Γ₂) → (Located Γ₁ → Located Γ₂ → Type)
    WellLocated' (σ₁ ‵∗ σ₂) (l₁ˡ , l₁ʳ) (l₂ˡ , l₂ʳ) =
      ( WellLocated' σ₁ l₁ˡ l₂ˡ
      × WellLocated' σ₂ l₁ʳ l₂ʳ )
    WellLocated' (‵trans σ₁ σ₂) l₁ l₂ =
      ∃[ l' ] (WellLocated' σ₁ l₁ l' × WellLocated' σ₂ l' l₂)
    WellLocated' (‵refl _) l₁ l₂ =
      l₁ ≡ l₂
    WellLocated' (‵swap a b) (l₁ˡ , l₁ʳ) (l₂ˡ , l₂ʳ) =
      ( (l₁ˡ ≡ l₂ʳ)
      × (l₁ʳ ≡ l₂ˡ) )
    WellLocated' (‵assoc a b c) ((l₁ˡˡ , l₁ˡʳ) , l₁ʳ) (l₂ˡ , (l₂ʳˡ , l₂ʳʳ)) =
      ( (l₁ˡˡ ≡ l₂ˡ)
      × (l₁ˡʳ ≡ l₂ʳˡ)
      × (l₁ʳ  ≡ l₂ʳʳ) )
    WellLocated' (‵assoc⁻¹ a b c) (l₁ˡ , (l₁ʳˡ , l₁ʳʳ)) ((l₂ˡˡ , l₂ˡʳ) , l₂ʳ) =
      ( (l₁ˡ  ≡ l₂ˡˡ)
      × (l₁ʳˡ ≡ l₂ˡʳ)
      × (l₁ʳʳ ≡ l₂ʳ ) )

    -- The only reason this can't be a function `Located Γ₁ → Located Γ₂` is because it would have to be partial.
    -- Specifically, when `join`ing two sites, the sites must be colocated for the join to be valid.
    -- (Likewise, if we were to write the function backwards, as `Located Γ₂ → Located Γ₁`, then when `fork`ing, the
    -- two forked sites must be colocated.)
    WellLocated : ∀{k} {Γ₁ Γ₂ : Tree (Tree Ty)} → (exec : Γ₁ ⇶[ k ] Γ₂) → Actions exec
                → (Located Γ₁ → Located Γ₂ → Type)
    WellLocated id _ l₁ l₂ =
      l₁ ≡ l₂
    WellLocated (perm σ) _ l₁ l₂ =
      WellLocated' σ l₁ l₂
    WellLocated tick (locally _) l₁ l₂ =
      l₁ ≡ l₂
    WellLocated tick (transmit src dst) l₁ l₂ =
      (l₁ ≡ src) × (l₂ ≡ dst)
    WellLocated fork _ l₁ (l₂ˡ , l₂ʳ) =
      ( (l₂ˡ ≡ l₁)
      × (l₂ʳ ≡ l₁) )
    WellLocated join _ (l₁ˡ , l₁ʳ) l₂ =
      ( (l₁ˡ ≡ l₂)
      × (l₁ʳ ≡ l₂) )
    WellLocated (f ∥ g) (actsˡ , actsʳ) (l₁ˡ , l₁ʳ) (l₂ˡ , l₂ʳ) =
      ( WellLocated f actsˡ l₁ˡ l₂ˡ
      × WellLocated g actsʳ l₁ʳ l₂ʳ )
    WellLocated (f ⟫ g) (acts₁ , acts₂) l₁ l₂ =
      ∃[ lₘ ] ( WellLocated f acts₁ l₁ lₘ
              × WellLocated g acts₂ lₘ l₂ )

    -- Even though `fork` and `join` are restricted, the category of (specialized) CSDs and the underlying category
    -- of local actions are both still symmetric monoidal categories. It's just that `fork` and `join` are no longer
    -- lossless converters between those categories' respective products! Only *some* products can be transferred.
    -- This is *deeply fascinating*, because it makes an even more suggestive case that the isomorphism between local
    -- and global products used in concurrent separation logic is faulty. Up until now we've only had the idea that
    -- `join ; fork` is not equal to `id` (an equality that CSLs still morally expect). Cool!!!
    -- (In fact, local products can always be transformed into global products, but global products *cannot* always be
    -- transformed into local products.)

    Epp : (Γ : Tree (Tree Ty)) → Located Γ
        → (Loc → Tree Ty)
    Epp ∅         l self = ∅
    Epp (leaf τ)  l self = if self ≟ l then τ else ∅
    Epp (Γ₁ ∗ Γ₂) (lˡ , lʳ) self = (Epp Γ₁ lˡ self ∗ Epp Γ₂ lʳ self)

    epp-σ : ∀{Γ₁ Γ₂ : Tree (Tree Ty)} → (σ : Γ₁ ≅ Γ₂) → {l₁ : Located Γ₁} → {l₂ : Located Γ₂} → WellLocated' σ l₁ l₂
         → ((self : Loc) → (Epp Γ₁ l₁ self ⇒' Epp Γ₂ l₂ self))
    epp-σ (σˡ ‵∗ σʳ) (wlˡ , wlʳ) self =
      par'
        (epp-σ σˡ wlˡ self)
        (epp-σ σʳ wlʳ self)
    epp-σ (‵trans σ₁ σ₂) (_ , (wl₁ , wl₂)) self =
      seq'
        (epp-σ σ₁ wl₁ self)
        (epp-σ σ₂ wl₂ self)
    epp-σ (‵refl _) wl self rewrite wl =
      locally λ x → x
    epp-σ (‵swap _ _) (wlˡ , wlʳ) self rewrite wlˡ | wlʳ =
      locally λ (x , y) → (y , x)
    epp-σ (‵assoc   _ _ _) (wlₗ , wlₘ , wlᵣ) self rewrite wlₗ | wlₘ | wlᵣ =
      locally λ ((x , y) , z) → (x , (y , z))
    epp-σ (‵assoc⁻¹ a b c) (wlₗ , wlₘ , wlᵣ) self rewrite wlₗ | wlₘ | wlᵣ =
      locally λ (x , (y , z)) → ((x , y) , z)

    epp : ∀{k} {Γ₁ Γ₂ : Tree (Tree Ty)} → {l₁ : Located Γ₁} → {l₂ : Located Γ₂}
        → (exec : Γ₁ ⇶[ k ] Γ₂) → (acts : Actions exec) → WellLocated exec acts l₁ l₂
        → ((self : Loc) → (Epp Γ₁ l₁ self ⇒' Epp Γ₂ l₂ self))
    epp {l₂ = l₂} tick (locally act) wl self rewrite wl with self ≟ l₂
    ... | true  = locally act
    ... | false = locally λ x → x
    epp tick (transmit src dst) (wl₁ , wl₂) self rewrite wl₁ | wl₂ with self ≟ src | self ≟ dst
    ... | true  | true  = locally λ x → x
    ... | false | false = locally λ x → x
    ... | true  | false = send dst
    ... | false | true  = recv src
    epp {l₁ = l₁} fork acts (wl₁ , wl₂) self rewrite wl₁ | wl₂ with self ≟ l₁
    ... | true  = locally λ x → x
    ... | false = locally λ x → (x , x)
    epp {l₂ = l₂} join acts (wl₁ , wl₂) self rewrite wl₁ | wl₂ with self ≟ l₂
    ... | true  = locally λ x → x
    ... | false = locally λ (x , y) → tt
    epp id acts wl self rewrite wl =
      locally λ x → x
    epp (perm σ) acts wl self =
      epp-σ σ wl self
    epp (x₁ ∥ x₂) (acts₁ , acts₂) (wl₁ , wl₂) self =
      par'
        (epp x₁ acts₁ wl₁ self)
        (epp x₂ acts₂ wl₂ self)
    epp (x₁ ⟫ x₂) (acts₁ , acts₂) (_ , (wl₁ , wl₂)) self =
      seq'
        (epp x₁ acts₁ wl₁ self)
        (epp x₂ acts₂ wl₂ self)
```
