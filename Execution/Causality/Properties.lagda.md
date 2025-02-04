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
  open import Data.Unit
    using (⊤; tt)
  open import Relation.Nullary
    using (¬_)
  open import Data.Sum
    using (inj₁; inj₂)
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
    using (_⇶_; Event; Cut; _;_)
    using (perm; tick; fork; join; init; term; id; _∥_; _⟫_)
  open import Execution.Causality
    using (Arr[_]; _↝_)
    using (LeadingEvent[_,_]; TrailingEvent[_,_])

  variable
    T : Type
    Γ₁ Γ₂ Γ₃ Γ₄ Γᵢ : Tree (Tree T)
```

</details>

```agda
  ↝-refl : {exec : Γ₁ ⇶ Γ₂} → (e : Event exec) → (e ↝ e)
  ↝-refl {exec = x₁ ∥ x₂} (inj₁ s) = ↝-refl s
  ↝-refl {exec = x₁ ∥ x₂} (inj₂ s) = ↝-refl s
  ↝-refl {exec = x₁ ⟫ x₂} (inj₁ s) = ↝-refl s
  ↝-refl {exec = x₁ ⟫ x₂} (inj₂ s) = ↝-refl s
  ↝-refl {exec = tick}    (inj₁ s) = Eq.refl
  ↝-refl {exec = tick}    (inj₂ s) = Eq.refl
  ↝-refl {exec = fork}    (inj₁ s) = Eq.refl
  ↝-refl {exec = fork}    (inj₂ s) = Eq.refl
  ↝-refl {exec = join}    (inj₁ s) = Eq.refl
  ↝-refl {exec = join}    (inj₂ s) = Eq.refl
  ↝-refl {exec = init}    (inj₁ s) = Eq.refl
  ↝-refl {exec = init}    (inj₂ s) = Eq.refl
  ↝-refl {exec = term}    (inj₁ s) = Eq.refl
  ↝-refl {exec = term}    (inj₂ s) = Eq.refl
  ↝-refl {exec = perm _}  (inj₁ s) = Eq.refl
  ↝-refl {exec = perm _}  (inj₂ s) = Eq.refl

  ↝-trans : {exec : Γ₁ ⇶ Γ₂} → (e₁ e₂ e₃ : Event exec)
          → (e₁ ↝ e₂) → (e₂ ↝ e₃) → (e₁ ↝ e₃)
  -- Parallel composition
  ↝-trans {exec = x₁ ∥ x₂} (inj₁ e₁) (inj₁ e₂) (inj₁ e₃) p₁₂ p₂₃ =
    ↝-trans e₁ e₂ e₃ p₁₂ p₂₃
  ↝-trans {exec = x₁ ∥ x₂} (inj₂ e₁) (inj₂ e₂) (inj₂ e₃) p₁₂ p₂₃ =
    ↝-trans e₁ e₂ e₃ p₁₂ p₂₃
  -- Sequential composition
  ↝-trans {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₁ e₂) (inj₁ e₃) p₁₂ p₂₃ =
    ↝-trans e₁ e₂ e₃ p₁₂ p₂₃
  ↝-trans {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₁ e₂) (inj₂ e₃) p₁₂ (sₓ , p₂ₓ , pₓ₃) =
    (sₓ , ↝-trans e₁ e₂ LeadingEvent[ x₁ , sₓ ] p₁₂ p₂ₓ , pₓ₃)
  ↝-trans {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₂ e₂) (inj₂ e₃) (sₓ , p₁ₓ , pₓ₂) p₂₃ =
    (sₓ , p₁ₓ , ↝-trans TrailingEvent[ x₂ , sₓ ] e₂ e₃ pₓ₂ p₂₃)
  ↝-trans {exec = x₁ ⟫ x₂} (inj₂ e₁) (inj₂ e₂) (inj₂ e₃) p₁₂ p₂₃ =
    ↝-trans e₁ e₂ e₃ p₁₂ p₂₃
  -- Atomic actions
  ↝-trans {exec = tick} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  ↝-trans {exec = tick} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) p₁₂ p₂₃ = tt
  ↝-trans {exec = tick} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = tt
  ↝-trans {exec = tick} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  --
  ↝-trans {exec = fork} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  ↝-trans {exec = fork} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) p₁₂ p₂₃ = tt
  ↝-trans {exec = fork} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = tt
  ↝-trans {exec = fork} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  --
  ↝-trans {exec = join} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  ↝-trans {exec = join} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) p₁₂ p₂₃ = tt
  ↝-trans {exec = join} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = tt
  ↝-trans {exec = join} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  --
  ↝-trans {exec = init} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  --
  ↝-trans {exec = term} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  --
  ↝-trans {exec = perm σ} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  ↝-trans {exec = perm σ} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans (Eq.cong (Tree.‵index σ) p₁₂) p₂₃
  ↝-trans {exec = perm σ} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃
  ↝-trans {exec = perm σ} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) p₁₂ p₂₃ = Eq.trans p₁₂ p₂₃

  ↝-antisym : {exec : Γ₁ ⇶ Γ₂} → (e₁ e₂ : Event exec)
            → (e₁ ↝ e₂) → (e₂ ↝ e₁) → (e₁ ≡ e₂)
  ↝-antisym {exec = x₁ ∥ x₂} (inj₁ e₁) (inj₁ e₂) p₁₂ p₂₁ = Eq.cong inj₁ (↝-antisym e₁ e₂ p₁₂ p₂₁)
  ↝-antisym {exec = x₁ ∥ x₂} (inj₂ e₁) (inj₂ e₂) p₁₂ p₂₁ = Eq.cong inj₂ (↝-antisym e₁ e₂ p₁₂ p₂₁)
  ↝-antisym {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₁ e₂) p₁₂ p₂₁ = Eq.cong inj₁ (↝-antisym e₁ e₂ p₁₂ p₂₁)
  ↝-antisym {exec = x₁ ⟫ x₂} (inj₂ e₁) (inj₂ e₂) p₁₂ p₂₁ = Eq.cong inj₂ (↝-antisym e₁ e₂ p₁₂ p₂₁)
  ↝-antisym {exec = tick}   (inj₁ _) (inj₁ _) p₁₂ p₂₁ = Eq.cong inj₁ p₁₂
  ↝-antisym {exec = tick}   (inj₂ _) (inj₂ _) p₁₂ p₂₁ = Eq.cong inj₂ p₁₂
  ↝-antisym {exec = fork}   (inj₁ _) (inj₁ _) p₁₂ p₂₁ = Eq.cong inj₁ p₁₂
  ↝-antisym {exec = fork}   (inj₂ _) (inj₂ _) p₁₂ p₂₁ = Eq.cong inj₂ p₁₂
  ↝-antisym {exec = join}   (inj₁ _) (inj₁ _) p₁₂ p₂₁ = Eq.cong inj₁ p₁₂
  ↝-antisym {exec = join}   (inj₂ _) (inj₂ _) p₁₂ p₂₁ = Eq.cong inj₂ p₁₂
  ↝-antisym {exec = term}   (inj₁ _) (inj₁ _) p₁₂ p₂₁ = Eq.cong inj₁ p₁₂
  ↝-antisym {exec = init}   (inj₂ _) (inj₂ _) p₁₂ p₂₁ = Eq.cong inj₂ p₁₂
  ↝-antisym {exec = perm σ} (inj₁ _) (inj₁ _) p₁₂ p₂₁ = Eq.cong inj₁ p₁₂
  ↝-antisym {exec = perm σ} (inj₂ _) (inj₂ _) p₁₂ p₂₁ = Eq.cong inj₂ p₁₂

  _↝∘_ : {exec : Γ₁ ⇶ Γ₂} {e₁ e₂ e₃ : Event exec}
       → (e₁ ↝ e₂) → (e₂ ↝ e₃) → (e₁ ↝ e₃)
  _↝∘_ {exec = exec} = ↝-trans {exec = exec} _ _ _

  ↝∘-assoc : {exec : Γ₁ ⇶ Γ₂}
           → (e₁ e₂ e₃ e₄ : Event exec)
           → (p₁₂ : e₁ ↝ e₂)
           → (p₂₃ : e₂ ↝ e₃)
           → (p₃₄ : e₃ ↝ e₄)
           → (↝-trans e₁ e₃ e₄ (↝-trans e₁ e₂ e₃ p₁₂ p₂₃) p₃₄)
           ≡ (↝-trans e₁ e₂ e₄ p₁₂ (↝-trans e₂ e₃ e₄ p₂₃ p₃₄))
  ↝∘-assoc {exec = x₁ ∥ x₂} (inj₁ e₁) (inj₁ e₂) (inj₁ e₃) (inj₁ e₄) p₁₂ p₂₃ p₃₄ =
    ↝∘-assoc e₁ e₂ e₃ e₄ p₁₂ p₂₃ p₃₄
  ↝∘-assoc {exec = x₁ ∥ x₂} (inj₂ e₁) (inj₂ e₂) (inj₂ e₃) (inj₂ e₄) p₁₂ p₂₃ p₃₄ =
    ↝∘-assoc e₁ e₂ e₃ e₄ p₁₂ p₂₃ p₃₄
  --
  ↝∘-assoc {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₁ e₂) (inj₁ e₃) (inj₁ e₄) p₁₂ p₂₃ p₃₄ =
   ↝∘-assoc e₁ e₂ e₃ e₄ p₁₂ p₂₃ p₃₄
  ↝∘-assoc {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₁ e₂) (inj₁ e₃) (inj₂ e₄) p₁₂ p₂₃ (sₘ , p₃ₘ , pₘ₄) =
    Eq.cong (λ ▢ → (_ , ▢ , _))
      (↝∘-assoc e₁ e₂ e₃ _ p₁₂ p₂₃ p₃ₘ)
  ↝∘-assoc {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₁ e₂) (inj₂ e₃) (inj₂ e₄) p₁₂ p₂₃ p₃₄ =
    Eq.refl
  ↝∘-assoc {exec = x₁ ⟫ x₂} (inj₁ e₁) (inj₂ e₂) (inj₂ e₃) (inj₂ e₄) (sₘ , p₁ₘ , pₘ₂) p₂₃ p₃₄ =
    Eq.cong (λ ▢ → _ , _ , ▢)
      (↝∘-assoc _ e₂ e₃ e₄ pₘ₂ p₂₃ p₃₄)
  ↝∘-assoc {exec = x₁ ⟫ x₂} (inj₂ e₁) (inj₂ e₂) (inj₂ e₃) (inj₂ e₄) p₁₂ p₂₃ p₃₄ =
    ↝∘-assoc e₁ e₂ e₃ e₄ p₁₂ p₂₃ p₃₄
  --
  ↝∘-assoc {exec = tick} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₁ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  ↝∘-assoc {exec = tick} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = tick} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = tick} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = tick} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  --
  ↝∘-assoc {exec = fork} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₁ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  ↝∘-assoc {exec = fork} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = fork} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = fork} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = fork} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  --
  ↝∘-assoc {exec = join} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₁ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  ↝∘-assoc {exec = join} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = join} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = join} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.refl
  ↝∘-assoc {exec = join} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  --
  ↝∘-assoc {exec = init} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  ↝∘-assoc {exec = term} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₁ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂ {p₂₃} {p₃₄}
  --
  ↝∘-assoc {exec = perm σ} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₁ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂
  ↝∘-assoc {exec = perm σ} (inj₁ s₁) (inj₁ s₂) (inj₁ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ =
    Eq.trans (Eq.cong (λ ▢ → Eq.trans ▢ p₃₄) (Eq.sym (Eq.trans-cong p₁₂)))
    (Eq.trans-assoc (Eq.cong (Tree.‵index σ) p₁₂))
  ↝∘-assoc {exec = perm σ} (inj₁ s₁) (inj₁ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ =
    Eq.trans-assoc (Eq.cong (Tree.‵index σ) p₁₂)
  ↝∘-assoc {exec = perm σ} (inj₁ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂
  ↝∘-assoc {exec = perm σ} (inj₂ s₁) (inj₂ s₂) (inj₂ s₃) (inj₂ s₄) p₁₂ p₂₃ p₃₄ = Eq.trans-assoc p₁₂
```
