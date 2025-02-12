{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock.Interpret where
  open import Data.Unit
    using (⊤; tt)
  open import Data.Product
    using (_×_; _,_; ∃-syntax)
  open import Execution.Sites
    as Sites
    using (Tree; Tree[_]; permute; forward; ‵sym; permute-sym)
  open import Execution.Core
    using (_⇶_; perm; tick; fork; join; init; term; _⟫_; _∥_)
    using (Event)
  open import Execution.Causality
    using (_↝_)
  open import Execution.Cut
    using (module MonotoneMap)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using ()

  variable
    Γ₁ Γ₂ : Tree

  data Step (Action State : Type) : Type where
    start :                  Step Action State
    act   : Action → State → Step Action State
    merge : State  → State → Step Action State

  module _ (Action : Type) where
    Stepped : (Γ₁ ⇶ Γ₂) → Type
    Stepped (x₁ ∥ x₂) = Stepped x₁ × Stepped x₂
    Stepped (x₁ ⟫ x₂) = Stepped x₁ × Stepped x₂
    Stepped tick = Action
    Stepped fork = ⊤
    Stepped join = ⊤
    Stepped init = ⊤
    Stepped term = ⊤
    Stepped (perm σ) = ⊤

  record Clock {Action State : Type}
               (alg : Step Action State → State)
               (_≤_ : State → State → Type)
             : Type where
    open Step using (act; merge)

    field ≤-refl      : ∀ s → s ≤ s
    field ≤-trans     : ∀ s₁ s₂ s₃ → (s₁ ≤ s₂) → (s₂ ≤ s₃) → (s₁ ≤ s₃)
    field act-mono    : ∀ p s → s ≤ alg (act p s)
    field merge-mono¹ : ∀ s₁ s₂ → s₁ ≤ alg (merge s₁ s₂)
    field merge-mono² : ∀ s₁ s₂ → s₂ ≤ alg (merge s₁ s₂)

  -- Given an algebra on steps, we can specify computations
  -- on replicas across spatially-distributed sites.
  module _ {Action State : Type} {alg : Step Action State → State}
           {_≤_ : State → State → Type} (clock : Clock alg _≤_)
           where
    open Clock clock
      using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

    timestamp' : (exec : Γ₁ ⇶ Γ₂) (acts : Stepped Action exec)
               → (l₁ : Tree[ Γ₁ ] State) → ∃[ l₂ ] MonotoneMap.Map' State _≤_ exec l₁ l₂
    timestamp' (x  ∥ x') (acts , acts') (l₁ , l₁') =
      let (l₂  , m ) = timestamp' x  acts  l₁  in
      let (l₂' , m') = timestamp' x' acts' l₁' in
      ((l₂ , l₂') , (m , m'))
    timestamp' (x₁ ⟫ x₂) (acts₁ , acts₂) l₁ =
      let (lₘ , m₁) = timestamp' x₁ acts₁ l₁ in
      let (l₂ , m₂) = timestamp' x₂ acts₂ lₘ in
      (l₂ , (lₘ , m₁ , m₂))
    timestamp' tick  acts l₁         = (alg (act acts l₁)   , act-mono acts l₁)
    timestamp' fork     _ l₁         = ((l₁ , l₁)           , (≤-refl _ , ≤-refl _))
    timestamp' join     _ (l₁ , l₁') = (alg (merge l₁ l₁')  , (merge-mono¹ l₁ l₁' , merge-mono² l₁ l₁'))
    timestamp' init     _ l₁         = (alg start           , tt)
    timestamp' term     _ l₁         = (tt                  , tt)
    timestamp' (perm σ) _ l₁         = (permute (‵sym σ) l₁ , Eq.sym (permute-sym σ l₁))

    timestamp : (exec : Γ₁ ⇶ Γ₂) (acts : Stepped Action exec)
              → (l₁ : Tree[ Γ₁ ] State) → (Event exec → State)
    timestamp exec acts l₁ = MonotoneMap.map State _≤_ (l₁ , timestamp' exec acts l₁)


    _⊑_ : {exec : Γ₁ ⇶ Γ₂} → Event exec → Event exec → Type
    _⊑_ {exec = exec} e₁ e₂ =
      ∀ actions input →
      let C[_] = timestamp exec actions input
      in C[ e₁ ] ≤ C[ e₂ ]

    timestamp-mono : (exec : Γ₁ ⇶ Γ₂)
                   → (e₁ e₂ : Event exec)
                   → e₁ ↝ e₂
                   → e₁ ⊑ e₂
    timestamp-mono exec e₁ e₂ p₁₂ acts l₁ =
      MonotoneMap.map-monotone State _≤_ ≤-refl (λ{_} → ≤-trans _ _ _) exec (l₁ , timestamp' exec acts l₁) e₁ e₂ p₁₂
