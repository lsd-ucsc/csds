<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
module Execution.Cut where
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
    using (_×_; _,_; ∃-syntax; ∃₂)
  open import Data.Bool
    using (Bool; true; false)
  open import Function
    as Function
    using (_∘_)
  open import Execution.Sites
    as Sites
    using (Tree; ∅; site; _∗_)
    using (Tree[_]; lookup; permute; repeat; lookup-forward)
  open import Execution.Core
    using (_⇶_; _∥_; _⟫_; tick; fork; join; init; term; perm; Event)
  open import Execution.Causality
    using (_↝_; LeadingEvent[_,_]; TrailingEvent[_,_])
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)
    renaming (trans to infixl 20 _∙_)

  variable
    T : Type
    -- Sets of sites over which executions act
    Γ Γ₁ Γ₂ Γ₃ Γ₄ : Tree
```

</details>

```agda
  module MonotoneMap (T : Type) (_≤_ : T → T → Type) where
    -- The causal lifting of _≤_ to whole diagrams
    Map' : (Γ₁ ⇶ Γ₂) → (Tree[ Γ₁ ] T → Tree[ Γ₂ ] T → Type)
    Map' (x₁ ∥ x₂) (l₁₁ , l₂₁) (l₁₂ , l₂₂) = Map' x₁ l₁₁ l₁₂ × Map' x₂ l₂₁ l₂₂
    Map' (x₁ ⟫ x₂) l₁          l₂          = ∃[ lₘ ] (Map' x₁ l₁ lₘ × Map' x₂ lₘ l₂)
    Map' tick      l₁          l₂          = l₁  ≤ l₂
    Map' fork      l₁          (l₂₁ , l₂₂) = l₁  ≤ l₂₁ × l₁  ≤ l₂₂ -- l₁ ≤ (l₂₁ ⊓ l₂₂)
    Map' join      (l₁₁ , l₁₂) l₂          = l₁₁ ≤ l₂  × l₁₂ ≤ l₂  -- (l₁₁ ⊔ l₁₂) ≤ l₂
    Map' init      _           _           = ⊤                     -- 𝟙 ≤ l₂
    Map' term      _           _           = ⊤                     -- l₁ ≤ 𝟘
    Map' (perm σ)  l₁          l₂          = l₁ ≡ permute σ l₂

    Map : (Γ₁ ⇶ Γ₂) → Type
    Map exec = ∃₂ (Map' exec)

    map' : (exec : Γ₁ ⇶ Γ₂) (l₁ : Tree[ Γ₁ ] T) (l₂ : Tree[ Γ₂ ] T)
         → (m : Map' exec l₁ l₂)
         → (Event exec → T)
    map' (x  ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') = Sum.[ map' x l₁ l₂ m , map' x' l₁' l₂' m' ]
    map' (x₁ ⟫ x₂) l₁ l₂ (lₘ , m₁ , m₂) = Sum.[ map' x₁ l₁ lₘ m₁ , map' x₂ lₘ l₂ m₂ ]
    map' tick     l₁ l₂ _ = Sum.[ lookup l₁ , lookup l₂ ]
    map' fork     l₁ l₂ _ = Sum.[ lookup l₁ , lookup l₂ ]
    map' join     l₁ l₂ _ = Sum.[ lookup l₁ , lookup l₂ ]
    map' init     l₁ l₂ _ = Sum.[ lookup l₁ , lookup l₂ ]
    map' term     l₁ l₂ _ = Sum.[ lookup l₁ , lookup l₂ ]
    map' (perm σ) l₁ l₂ _ = Sum.[ lookup l₁ , lookup l₂ ]

    -- TODO: show that `map m e₁ ≡ map m e₂` whenever `e₁ ∼ e₂`.
    --   (∀ c → cut c e₁ ≡ cut c e₂) → (∀ m → map m e₁ ≡ map m e₂)
    -- Notice that if we have a monotone projection `T → Label`,
    -- then the implication above goes opposite the projection,
    -- in a way reminiscent of continuous functions and open sets.
    map : {exec : Γ₁ ⇶ Γ₂} → Map exec → (Event exec → T)
    map (l₁ , l₂ , m) = map' _ l₁ l₂ m

    _⊑_ : {exec : Γ₁ ⇶ Γ₂} (_ _ : Map exec) → Type
    _⊑_ {exec = exec} m₁ m₂ = (e : Event exec) → map m₁ e ≤ map m₂ e

    -- There's a kind of continuous-function thing happening here:
    -- if I have a monotone function `f : A → B` and a map `m : Map[ A ] exec`,
    -- I can construct a map `f m : Map[ B ] exec`.
    -- But for `m, m'` we have that `(f m ⊑ f m') → (m ⊑ m')`, i.e. the implication
    -- goes opposite the direction of `f`.


    map'-leading : (exec : Γ₁ ⇶ Γ₂) (l₁ : Tree[ Γ₁ ] T) (l₂ : Tree[ Γ₂ ] T) → (m : Map' exec l₁ l₂)
                 → ∀ s → map' exec l₁ l₂ m LeadingEvent[ exec , s ] ≡ lookup l₂ s
    map'-leading (x  ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') (Sites.thereˡ _ s) = map'-leading x l₁ l₂ m s
    map'-leading (x  ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') (Sites.thereʳ _ s) = map'-leading x' l₁' l₂' m' s
    map'-leading (x₁ ⟫ x₂) l₁ l₂ (lₘ , m₁ , m₂) s = map'-leading x₂ lₘ l₂ m₂ s
    map'-leading tick l₁ l₂ m s = Eq.refl
    map'-leading fork l₁ l₂ m s = Eq.refl
    map'-leading join l₁ l₂ m s = Eq.refl
    map'-leading init l₁ l₂ m s = Eq.refl
    map'-leading (perm σ) l₁ l₂ m s = Eq.refl

    map'-trailing : (exec : Γ₁ ⇶ Γ₂) (l₁ : Tree[ Γ₁ ] T) (l₂ : Tree[ Γ₂ ] T) → (m : Map' exec l₁ l₂)
                  → ∀ s → lookup l₁ s ≡ map' exec l₁ l₂ m TrailingEvent[ exec , s ]
    map'-trailing (x  ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') (Sites.thereˡ _ s) = map'-trailing x l₁ l₂ m s
    map'-trailing (x  ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') (Sites.thereʳ _ s) = map'-trailing x' l₁' l₂' m' s
    map'-trailing (x₁ ⟫ x₂) l₁ l₂ (lₘ , m₁ , m₂) s = map'-trailing x₁ l₁ lₘ m₁ s
    map'-trailing tick l₁ l₂ m s = Eq.refl
    map'-trailing fork l₁ l₂ m s = Eq.refl
    map'-trailing join l₁ l₂ m s = Eq.refl
    map'-trailing term l₁ l₂ m s = Eq.refl
    map'-trailing (perm σ) l₁ l₂ m s = Eq.refl

    _≤'[_]_ : {exec : Γ₁ ⇶ Γ₂} {l₁ : Tree[ Γ₁ ] T} {l₂ : Tree[ Γ₂ ] T}
           → (e₁ : Event exec) → (m : Map' exec l₁ l₂) → (e₂ : Event exec) → Type
    e₁ ≤'[ m ] e₂ = (map' _ _ _ m e₁ ≤ map' _ _ _ m e₂)

    _≤[_]_ : {exec : Γ₁ ⇶ Γ₂}
           → (e₁ : Event exec) → (m : Map exec) → (e₂ : Event exec) → Type
    e₁ ≤[ _ , _ , m ] e₂ = e₁ ≤'[ m ] e₂

    module _ (≤-refl : ∀ a → (a ≤ a)) (_≤∘_ : ∀{a b c} → (a ≤ b) → (b ≤ c) → (a ≤ c)) (let infixl 20 _≤∘_; _≤∘_ = _≤∘_) where
      ≤-reflexive : ∀{a b} → (a ≡ b) → a ≤ b
      ≤-reflexive Eq.refl = ≤-refl _

      map'-monotone : (exec : Γ₁ ⇶ Γ₂) (l₁ : Tree[ Γ₁ ] T) (l₂ : Tree[ Γ₂ ] T)
                    → (m : Map' exec l₁ l₂)
                    → (e₁ e₂ : Event exec) → (e₁ ↝ e₂) → (e₁ ≤'[ m ] e₂)
      map'-monotone (x ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') (inj₁ e₁) (inj₁ e₂) p₁₂ = map'-monotone x l₁ l₂ m e₁ e₂ p₁₂
      map'-monotone (x ∥ x') (l₁ , l₁') (l₂ , l₂') (m , m') (inj₂ e₁) (inj₂ e₂) p₁₂ = map'-monotone x' l₁' l₂' m' e₁ e₂ p₁₂
      map'-monotone (x₁ ⟫ x₂) l₁ l₂ (lₘ , m₁ , m₂) (inj₁ e₁) (inj₁ e₂) p₁₂ = map'-monotone x₁ l₁ lₘ m₁ e₁ e₂ p₁₂
      map'-monotone (x₁ ⟫ x₂) l₁ l₂ (lₘ , m₁ , m₂) (inj₂ e₁) (inj₂ e₂) p₁₂ = map'-monotone x₂ lₘ l₂ m₂ e₁ e₂ p₁₂
      map'-monotone (x₁ ⟫ x₂) l₁ l₂ (lₘ , m₁ , m₂) (inj₁ e₁) (inj₂ e₂) (sₘ , p₁ₘ , pₘ₂) =
        (  (map'-monotone x₁ l₁ lₘ m₁ e₁ LeadingEvent[ x₁ , sₘ ] p₁ₘ)
        ≤∘ ≤-reflexive (map'-leading x₁ l₁ lₘ m₁ sₘ)
        ≤∘ ≤-reflexive (map'-trailing x₂ lₘ l₂ m₂ sₘ)
        ≤∘ map'-monotone x₂ lₘ l₂ m₂ TrailingEvent[ x₂ , sₘ ] e₂ pₘ₂ )
      map'-monotone tick l₁ l₂ m (inj₁ e₁) (inj₁ e₂) p₁₂ = ≤-refl l₁
      map'-monotone tick l₁ l₂ m (inj₂ e₁) (inj₂ e₂) p₁₂ = ≤-refl l₂
      map'-monotone tick l₁ l₂ m (inj₁ e₁) (inj₂ e₂) p₁₂ = m
      map'-monotone fork l₁ l₂ m (inj₁ e₁) (inj₁ e₂) p₁₂ = ≤-refl l₁
      map'-monotone fork l₁ l₂ (m₁ , m₂) (inj₁ e₁) (inj₂ (Sites.thereˡ _ e₂)) p₁₂ = m₁
      map'-monotone fork l₁ l₂ (m₁ , m₂) (inj₁ e₁) (inj₂ (Sites.thereʳ _ e₂)) p₁₂ = m₂
      map'-monotone fork l₁ l₂ m (inj₂ e₁) (inj₂ e₂) p₁₂ = ≤-reflexive (Eq.cong (lookup l₂) p₁₂)
      map'-monotone join l₁ l₂ m (inj₁ e₁) (inj₁ e₂) p₁₂ = ≤-reflexive (Eq.cong (lookup l₁) p₁₂)
      map'-monotone join l₁ l₂ (m₁ , m₂) (inj₁ (Sites.thereˡ _ e₁)) (inj₂ e₂) p₁₂ = m₁
      map'-monotone join l₁ l₂ (m₁ , m₂) (inj₁ (Sites.thereʳ _ e₁)) (inj₂ e₂) p₁₂ = m₂
      map'-monotone join l₁ l₂ m (inj₂ e₁) (inj₂ e₂) p₁₂ = ≤-refl l₂
      map'-monotone init l₁ l₂ m (inj₂ e₁) (inj₂ e₂) p₁₂ = ≤-refl l₂
      map'-monotone term l₁ l₂ m (inj₁ e₁) (inj₁ e₂) p₁₂ = ≤-refl l₁
      map'-monotone (perm σ) l₁ l₂ m (inj₁ e₁) (inj₁ e₂) p₁₂ = ≤-reflexive (Eq.cong (lookup l₁) p₁₂)
      map'-monotone (perm σ) l₁ l₂ m (inj₂ e₁) (inj₂ e₂) p₁₂ = ≤-reflexive (Eq.cong (lookup l₂) p₁₂)
      map'-monotone (perm σ) l₁ l₂ m (inj₁ e₁) (inj₂ e₂) p₁₂ = ≤-reflexive
        ( Eq.cong (λ ▢ → lookup ▢ e₁) m
        ∙ Eq.sym (lookup-forward σ l₂ e₁)
        ∙ Eq.cong (lookup l₂) p₁₂ )

      map-monotone : (exec : Γ₁ ⇶ Γ₂) (m : Map exec)
                   → ((e₁ e₂ : Event exec) → (e₁ ↝ e₂) → e₁ ≤[ m ] e₂)
      map-monotone exec (l₁ , l₂ , m) = map'-monotone exec l₁ l₂ m


  _≤_ : Bool → Bool → Type
  true  ≤ _     = ⊤
  false ≤ true  = ⊥
  false ≤ false = ⊤

  -- A cut is just any monotone labeling on booleans, where false ≤ true.
  -- If we instantiate on ℕ instead of on Label, we get a whole topographical atlas of cuts;
  -- and in general, we can extract cuts from a labeled CSD with just a monotone function on those labels.
  open MonotoneMap Bool _≤_
    using (_⊑_)
    renaming (Map' to Cut'; Map to Cut; map' to cut'; map to cut)

  -- Two events are identified if no cut distinguishes them.
  _∼_ : {exec : Γ₁ ⇶ Γ₂} → (_ _ : Event exec) → Type
  e₁ ∼ e₂ = ∀ c → cut c e₁ ≡ cut c e₂
  -- ...or if their downcuts are identical.
  -- e₁ ∼ e₂ = (past e₁ ⊑ past e₂) × (past e₂ ⊑ past e₁)
  -- ...or if they're before each others' downcuts.
  -- e₁ ∼ e₂ = (cut (past e₁) e₂ ≡ Before) × (cut (past e₂) e₁ ≡ Before)

{-
  cut-⊥ : {Γ₁ Γ₂ : Tree} (exec : Γ₁ ⇶ Γ₂) → Cut' exec (repeat _ false) (repeat _ false)
  cut-⊥ (x₁ ∥ x₂) = (cut-⊥ x₁ , cut-⊥ x₂)
  cut-⊥ (x₁ ⟫ x₂) = (repeat _ false , cut-⊥ x₁ , cut-⊥ x₂)
  cut-⊥ tick = tt
  cut-⊥ fork = (tt , tt)
  cut-⊥ join = (tt , tt)
  cut-⊥ init = tt
  cut-⊥ term = tt
  cut-⊥ (perm σ) = Sites.permute-tabulate σ (λ _ → false)

  cut-⊤ : {Γ₁ Γ₂ : Tree} (exec : Γ₁ ⇶ Γ₂) → Cut' exec (repeat _ true) (repeat _ true)
  cut-⊤ (x₁ ∥ x₂) = (cut-⊤ x₁ , cut-⊤ x₂)
  cut-⊤ (x₁ ⟫ x₂) = (repeat _ true , cut-⊤ x₁ , cut-⊤ x₂)
  cut-⊤ tick = tt
  cut-⊤ fork = (tt , tt)
  cut-⊤ join = (tt , tt)
  cut-⊤ init = tt
  cut-⊤ term = tt
  cut-⊤ (perm σ) = Sites.permute-tabulate σ (λ _ → true)

  -- (e₁ ↝ e₂) ⇔ (past e₁ ⊑ past e₂)
  past : {x : Γ₁ ⇶ Γ₂} → (Event x → Cut x)
  past {x = x ∥ x'} (inj₁ e) = let (l₁ , l₂ , c) = past e in ((l₁ , repeat _ false) , (l₂ , repeat _ false) , (c , cut-⊥ x'))
  past {x = x ∥ x'} (inj₂ e) = let (l₁ , l₂ , c) = past e in ((repeat _ false , l₁) , (repeat _ false , l₂) , (cut-⊥ x , c))
  past {x = x₁ ⟫ x₂} (inj₁ e) = let (l₁ , lₘ , c₁) = past e in {!!}
  past {x = x₁ ⟫ x₂} (inj₂ e) = {!!}
  past {x = tick} (inj₁ e) = (true , false , tt)
  past {x = tick} (inj₂ e) = (true , true , tt)
  past {x = fork} (inj₁ e) = (true , (false , false) , (tt , tt))
  past {x = fork} (inj₂ (Sites.thereˡ _ e)) = (true , (true , false) , (tt , tt))
  past {x = fork} (inj₂ (Sites.thereʳ _ e)) = (true , (false , true) , (tt , tt))
  past {x = join} (inj₁ (Sites.thereˡ _ e)) = ((true , false) , false , (tt , tt))
  past {x = join} (inj₁ (Sites.thereʳ _ e)) = ((false , true) , false , (tt , tt))
  past {x = join} (inj₂ e) = ((true , true) , true , (tt , tt))
  past {x = init} e = (tt , true , tt)
  past {x = term} e = (true , tt , tt)
  past {x = perm σ} (inj₁ e) = {!!}
  past {x = perm σ} (inj₂ e) = {!!}
-}
```
