<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
open import Data.Nat using (ℕ)

module Choreographies.Bar {location-count : ℕ} where
```

<details>
<summary>Imports, variables, and fixity</summary>

```agda
  open import Function
    using (_∘_)
  open import Data.Unit
    using (⊤; tt)
  open import Data.Empty
    using (⊥)
  open import Data.Product
    as Prod
    using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
  open import Data.Sum
    as Sum
    using (_⊎_)
  open import Data.Nat
    using (ℕ)
  open import Data.Fin
    using (Fin; _≟_)
  open import Data.Bool
    using (Bool; true; false; if_then_else_)
  open import Data.Maybe
    as Maybe
    using (Maybe; fromMaybe)
    renaming (just to some; nothing to none)
  open import Data.These
    using (These; this; that; these)
  open import Data.List
    using (List; []; _∷_; [_]; _++_)
  open import Data.List.Relation.Unary.Any
    using (here; there)
  open import Relation.Nullary.Negation
    using (¬_)
  open import Relation.Nullary.Decidable
    using (Dec; does; _because_; yes; no; _⊎-dec_)
  open import Relation.Nullary.Reflects
    using (Reflects)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  infixl 25 _⊗_
  infixl 24 _⊕_
  infix  23 _＠_
  infixl 22 _∗_
  infixl 21 _+_
  infix  20 _⇶_
  infixl 20 _∥_
```
</details>

  Problem 1: To project a heap `Γ₁ + Γ₂` onto a choreographic role `self`,
we need to know whether `self` "knows about" the choice modeled by the sum.
If it doesn't, then the whole sum projects down to `none`: the absence of state,
rather than present state void of information (as `some 𝟙` would mean).
If it *does*, then the sum projects down to a `some _` of a (local) sum, which
may very well be `some (𝟙 ⊕ 𝟙)` if `self` owns no other state (or only owns `𝟙`s).
Thus, we need to keep track of which sites "know about" a choice.

  Problem 2: We need to get state from *outside* a sum, *into* that sum. We also
need to get state from *inside* a sum, *out of* that sum. This allows participants
who *don't* know about the choice to nonetheless interact with agents who *do*, so
long as those interactions are *structurally* independent of the choice. Getting
state out of a sum is easy: if you have two sites on either side of a choice, owned
by the same participant, with data of the same type, then you can "factor out" those
sites into a single site outside the choice. Getting state *into* a sum is harder:
the state needs to be on a site whose choreographic participant is aware of that choice.
If the site is not aware of that choice, then they cannot distribute over the choice.

  Problem 3: Communication under a choice can only occur between participants who are
*aware* of that choice. Otherwise, communication could happen that is not structurally
independent of the choice. Likewise, initiating a new site under a choice can only happen
if that site is owned by a participant who is aware of that choice.

  Problem 4: Sums "ought to be" associative, but operationalizing associativity is not
obvious. A sum like `(a + b) + c` indicates a choice X made in context of another choice Y;
there are then three possibilities: (X ∧ Y), (X ∧ ¬Y), and ¬X. Reassociating to `a + (b + c)`
implies reparametrizing against choices X' and Y', for which there are three possibilities:
X', (¬X' ∧ Y'), (¬X' ∧ ¬Y'). In other words: X' ≡ X ∧ Y, and Y' ≡ (X ⇒ ¬Y). Then knowledge
of the outer choice is given by a determination on X', for which truth pins down the original
values of both X and Y, and falsity still leaves both choices open (as well as the question of
whether choice Y was even made, given that it doesn't occur in the ¬X case). It is particularly
unclear what the sets of participants who know about each choice should be.

  Remark 1: It is clear that modeling the set of participants who "know about" a choice,
and modeling the dynamics of that set over time, is paramount. Moreover, this knowledge
is not only relevant at the interface between a choice and its environment, but also
deep within the body of the choice, where communication must be restricted to like-informed
participants. How is this set modeled? We could say that any participant *with state* under
the choice knows about the choice, but this appears to give too many responsibilities: bringing
state under the choice *simultaneously requires* that the participant be notified by someone
who is already present in the choice. Nonetheless, it is certainly true that, if a participant
has state under a choice, then they must know about it.

  Remark 2: It seems, then, that we must constrain leaf-level communication-like actions
(namely, `transmit` and `init`) to only those locations that are available within the surrounding
heap.

```agda
  data Ty : Type where
    𝟙 : Ty
    _⊗_ : Ty → Ty → Ty
    _⊕_ : Ty → Ty → Ty

  ⟦_⟧ : Ty → Type
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ τ₁ ⊗ τ₂ ⟧ = ⟦ τ₁ ⟧ × ⟦ τ₂ ⟧
  ⟦ τ₁ ⊕ τ₂ ⟧ = ⟦ τ₁ ⟧ ⊎ ⟦ τ₂ ⟧

  _⟶_ : Ty → Ty → Type
  τ₁ ⟶ τ₂ = ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧


  Loc : Type
  Loc = Fin location-count

  data ChoreoHeap : Type where
    -- an empty heap
    ∅        : ChoreoHeap
    -- a discrete site owned by some location
    _＠_     : Ty → (l : Loc) → ChoreoHeap
    -- a pair of separated heaps
    _∗_      : (_ _ : ChoreoHeap) → ChoreoHeap
    -- a choice between heaps
    _+_      : (_ _ : ChoreoHeap) → ChoreoHeap


  variable
    Γ  Γ₁  Γ₂  Γ₃  : ChoreoHeap
    Γ' Γ₁' Γ₂' Γ₃' : ChoreoHeap

  data _⇶_ : (_ _ : ChoreoHeap) → Type where
    id : ∀ Γ → Γ ⇶ Γ

    -- permutations on sites
    swap    : ∀ Γ₁ Γ₂    → (Γ₁ ∗ Γ₂) ⇶ (Γ₂ ∗ Γ₁)
    assoc   : ∀ Γ₁ Γ₂ Γ₃ → ((Γ₁ ∗  Γ₂) ∗ Γ₃ ) ⇶ ( Γ₁ ∗ (Γ₂  ∗ Γ₃))
    assoc⁻¹ : ∀ Γ₁ Γ₂ Γ₃ → ( Γ₁ ∗ (Γ₂  ∗ Γ₃)) ⇶ ((Γ₁ ∗  Γ₂) ∗ Γ₃ )
  --unitₗ   : ∀ Γ        →      Γ  ⇶ (∅ ∗ Γ)
  --unitₗ⁻¹ : ∀ Γ        → (∅ ∗ Γ) ⇶      Γ

    -- products can distribute over sums
    distrib   : ∀ Γ₁ Γ₂ Γ₃ → ((Γ₁ + Γ₂) ∗ Γ₃) ⇶ ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃))
    distrib⁻¹ : ∀ Γ₁ Γ₂ Γ₃ → ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃)) ⇶ ((Γ₁ + Γ₂) ∗ Γ₃)

    -- sequential composition
    _;_ : (x₁ : Γ₁ ⇶ Γ₂)
        → (x₂ : Γ₂ ⇶ Γ₃)
        → (Γ₁ ⇶ Γ₃)

    -- concurrent composition over products
    _∥_ : (Γ₁       ⇶ Γ₂      )
        → (     Γ₁' ⇶      Γ₂')
        → (Γ₁ ∗ Γ₁' ⇶ Γ₂ ∗ Γ₂')

    -- concurrent composition over sums
    _◇_ : (Γ₁       ⇶ Γ₂)
        → (     Γ₁' ⇶ Γ₂')
        → (Γ₁ + Γ₁' ⇶ Γ₂ + Γ₂')

    -- a local computation at a site
    locally : ∀{a b} l → (a ⟶ b) → ((a ＠ l) ⇶ (b ＠ l))
    -- transferrence of state between chroreographic locations
    transmit : ∀{a} l₁ l₂ → (a ＠ l₁) ⇶ (a ＠ l₂)

    -- the creation of a site
    init : ∀ l → ∅ ⇶ (𝟙 ＠ l)
    -- the destruction of a site
    term : ∀ l → (𝟙 ＠ l) ⇶ ∅

    -- the factorization of one site into two
    fork : ∀ l a b → (a ⊗ b ＠ l) ⇶ (a ＠ l ∗ b ＠ l)
    -- the assimilation of two sites into one
    join : ∀ l a b → (a ＠ l ∗ b ＠ l) ⇶ (a ⊗ b ＠ l)

    -- the externalization of two possibilities at one site
    branch   : ∀ l a b → (a ⊕ b ＠ l) ⇶ (a ＠ l + b ＠ l)
    -- the internalization of two possibilities at one site
    coalesce : ∀ l a b → (a ＠ l + b ＠ l) ⇶ (a ⊕ b ＠ l)

    -- TODO: add this operator: (a * b) + (c * d) ⇶ (a + c) * (b + d)
    --       so that `idem` is expressible

  Centralized : ChoreoHeap → Ty
  Centralized ∅         = 𝟙
  Centralized (τ ＠ l)  = τ
  Centralized (Γ₁ ∗ Γ₂) = Centralized Γ₁ ⊗ Centralized Γ₂
  Centralized (Γ₁ + Γ₂) = Centralized Γ₁ ⊕ Centralized Γ₂

  centralized : (Γ₁ ⇶ Γ₂) → (⟦ Centralized Γ₁ ⟧ → ⟦ Centralized Γ₂ ⟧)
  centralized (swap Γ₁ Γ₂) (fst , snd) = snd , fst
  centralized (assoc Γ₁ Γ₂ Γ₃) ((fst , snd₁) , snd) = fst , snd₁ , snd
  centralized (assoc⁻¹ Γ₁ Γ₂ Γ₃) (fst , fst₁ , snd) = (fst , fst₁) , snd
  centralized (distrib _ _ _) (_⊎_.inj₁ x , snd) = _⊎_.inj₁ (x , snd)
  centralized (distrib _ _ _) (_⊎_.inj₂ y , snd) = _⊎_.inj₂ (y , snd)
  centralized (distrib⁻¹ _ _ _) (_⊎_.inj₁ (fst , snd)) = _⊎_.inj₁ fst , snd
  centralized (distrib⁻¹ _ _ _) (_⊎_.inj₂ (fst , snd)) = _⊎_.inj₂ fst , snd
  centralized (x ; x') = centralized x' ∘ centralized x
  centralized (x ∥ x₁) (fst , snd) = centralized x fst , centralized x₁ snd
  centralized (x ◇ x₁) (_⊎_.inj₁ x₂) = _⊎_.inj₁ (centralized x x₂)
  centralized (x ◇ x₁) (_⊎_.inj₂ y) = _⊎_.inj₂ (centralized x₁ y)
  centralized (locally l f) = f
  --
  centralized (id _) = λ i → i
  centralized (transmit l₁ l₂) = λ i → i
  centralized (init l) = λ i → i
  centralized (term l) = λ i → i
  centralized (fork l a b) = λ i → i
  centralized (join l a b) = λ i → i
  centralized (branch l a b) = λ i → i
  centralized (coalesce l a b) = λ i → i

{-
  - [X] Centralized, functional semantics
  - [X] Distributed, procedural semantics
  - [ ] Centralized, procedural semantics
    -- TODO: this is just a rearrangement of the π-calculus term obtained
    --       by running all EPP'd terms in parallel, such that every tile
    --       of the cCSD maps to the all-parallel EPP of that tile.
-}

  Chan : Type
  Chan = ℕ

  ChanTree : ChoreoHeap → Type
  ChanTree ∅ = ⊤
  ChanTree (τ ＠ _) = Chan
  ChanTree (Γ₁ ∗ Γ₂) = ChanTree Γ₁ × ChanTree Γ₂
  ChanTree (Γ₁ + Γ₂) = (Loc → Chan) × (ChanTree Γ₁ × ChanTree Γ₂)

  -- Consider adding a nondeterministic choice operator _+_
  -- following https://era.ed.ac.uk/bitstream/handle/1842/6050/ECS-LFCS-91-180.pdf?sequence=2
  -- ("The Polyadic π-Calculus: A Tutorial")
  -- so that choreographic choice is modeled by receiving on one of two channels,
  -- the one activated eliminating the one left behind.
  -- This would avoid any squicky feelings about using `Sum.[_,_]` (or equivalent)
  -- in our semantics.
  data Pi : Type where
    halt  : Pi
    _∥_   : Pi → Pi → Pi
    ⟨_!_⟩ : Chan → (Σ[ τ ∈ Ty ] ⟦ τ ⟧) → Pi
    recv  : Chan → (τ : Ty) → (⟦ τ ⟧ → Pi) → Pi

  syntax recv ch τ (λ x → k) = ⟨ ch ¿ τ , x ⟩ k

  data _≅_ : (_ _ : Pi) → Type where
    π-refl   : (π : Pi) → π ≅ π
    π-trans  : {π₁ π₂ π₃ : Pi} → (π₁ ≅ π₂) → (π₂ ≅ π₃) → (π₁ ≅ π₃)
    π-cong   : {π₁ π₂ π₁' π₂' : Pi} → (π₁ ≅ π₂) → (π₁' ≅ π₂') → (π₁ ∥ π₁') ≅ (π₂ ∥ π₂')

    π-assoc  : (π₁ π₂ π₃ : Pi) → ((π₁ ∥ π₂) ∥ π₃) ≅ (π₁ ∥ (π₂ ∥ π₃))
    π-comm   : (π₁ π₂ : Pi) → (π₁ ∥ π₂) ≅ (π₂ ∥ π₁)
    π-unit   : (π : Pi) → (π ∥ halt) ≅ π
    π-unit⁻¹ : (π : Pi) → π ≅ (π ∥ halt)

  π-assoc⁻¹ : (π₁ π₂ π₃ : Pi) → (π₁ ∥ (π₂ ∥ π₃)) ≅ ((π₁ ∥ π₂) ∥ π₃)
  π-assoc⁻¹ _ _ _ =
    π-trans (π-trans (π-trans (π-trans
      (π-comm _ _)
      (π-cong (π-comm _ _) (π-refl _)) )
      (π-assoc _ _ _) )
      (π-cong (π-refl _) (π-comm _ _)) )
      (π-comm _ _)

  π-sym : {π₁ π₂ : Pi} → (π₁ ≅ π₂) → (π₂ ≅ π₁)
  π-sym (π-refl π) = π-refl π
  π-sym (π-trans σ₁ σ₂) = π-trans (π-sym σ₂) (π-sym σ₁)
  π-sym (π-cong σ₁ σ₂) = π-cong (π-sym σ₁) (π-sym σ₂)
  π-sym (π-assoc π₁ π₂ π₃) = π-assoc⁻¹ π₁ π₂ π₃
  π-sym (π-comm π₁ π₂) = π-comm π₂ π₁
  π-sym (π-unit π) = π-unit⁻¹ π
  π-sym (π-unit⁻¹ π) = π-unit π

  -- Big-step semantics
  data _⇓_ : (_ _ : Pi) → Type where
    -- TODO!

  -- Small-step semantics (instead?)
  data _⇒_ : (_ _ : Pi) → Type where
    -- TODO!


  -- TODO: Constrain all channel names to be distinct.
  ChanMap : (Γ₁ ⇶ Γ₂) → (ChanTree Γ₁ → ChanTree Γ₂ → Type)
  ChanMap (id _) i⃗ o⃗ = ⊤
  ChanMap (swap Γ₁ Γ₂) (i⃗₁ , i⃗₂) (o⃗₁ , o⃗₂) = ⊤
  ChanMap (assoc Γ₁ Γ₂ Γ₃) i⃗ o⃗ = ⊤
  ChanMap (assoc⁻¹ Γ₁ Γ₂ Γ₃) i⃗ o⃗ = ⊤
  ChanMap (distrib _ _ _) i⃗ o⃗ = ⊤
  ChanMap (distrib⁻¹ _ _ _) i⃗ o⃗ = ⊤
  ChanMap (x₁ ; x₂) i⃗ o⃗ = ∃[ m⃗ ] ChanMap x₁ i⃗ m⃗ × ChanMap x₂ m⃗ o⃗
  ChanMap (x  ∥ x') (i⃗₁ , i⃗₂) (o⃗₁ , o⃗₂) = ChanMap x i⃗₁ o⃗₁ × ChanMap x' i⃗₂ o⃗₂
  ChanMap (x  ◇ x') (i⃗₊ , i⃗₁ , i⃗₂) (o⃗₊ , o⃗₁ , o⃗₂) = ChanMap x i⃗₁ o⃗₁ × ChanMap x' i⃗₂ o⃗₂
  ChanMap (locally l x) i⃗ o⃗ = ⊤
  ChanMap (transmit l₁ l₂) i⃗ o⃗ = ⊤
  ChanMap (init l) i⃗ o⃗ = ⊤
  ChanMap (term l) i⃗ o⃗ = ⊤
  ChanMap (fork l a b) i⃗ o⃗ = ⊤
  ChanMap (join l a b) i⃗ o⃗ = ⊤
  ChanMap (branch l a b) i⃗ o⃗ = ⊤
  ChanMap (coalesce l a b) i⃗ o⃗ = ⊤

  foo : (len : ℕ) → (next : ℕ) → (ℕ × (Fin len → ℕ))
  foo ℕ.zero      next = next , λ()
  foo (ℕ.suc len) next =
    let (next' , f) = foo len next in
    (ℕ.suc next' , (λ{ Fin.zero → next' ; (Fin.suc l) → f l }))

  chans : (Γ : ChoreoHeap) → ℕ → (ℕ × ChanTree Γ)
  chans ∅ n = (n , tt)
  chans (τ ＠ l) n = (ℕ.suc n , n)
  chans (Γ₁ ∗ Γ₂) n =
    let (n'  , ch₁) = chans Γ₁ n  in
    let (n'' , ch₂) = chans Γ₂ n' in
    (n'' , (ch₁ , ch₂))
  chans (Γ₁ + Γ₂) n =
    let (n'  , ch₁) = chans Γ₁ n  in
    let (n'' , ch₂) = chans Γ₂ n' in
    let (n''' , ch₊) = foo location-count n'' in
    (ℕ.suc n''' , (ch₊ , ch₁ , ch₂))

  -- TODO: Consider assigning all sites along the same logical event the same channel.
  -- This would cut down on the number of forwarding processes that need to be emitted.
  chanmap : (x : Γ₁ ⇶ Γ₂) → ℕ → (m₁ : ChanTree Γ₁) → (ℕ × ∃[ m₂ ] ChanMap x m₁ m₂)
  chanmap (id Γ) next _ =
    let (next' , m₂) = chans Γ next in
    (next' , m₂ , tt)
  chanmap (swap Γ₁ Γ₂) next _ =
    let (next' , m₂) = chans (Γ₂ ∗ Γ₁) next in
    (next' , m₂ , tt)
  chanmap (assoc Γ₁ Γ₂ Γ₃) next _ =
    let (next' , m₂) = chans (Γ₁ ∗ (Γ₂ ∗ Γ₃)) next in
    (next' , m₂ , tt)
  chanmap (assoc⁻¹ Γ₁ Γ₂ Γ₃) next _ =
    let (next' , m₂) = chans ((Γ₁ ∗ Γ₂) ∗ Γ₃) next in
    (next' , m₂ , tt)
  chanmap (distrib Γ₁ Γ₂ Γ₃) next _ =
    let (next' , m₂) = chans ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃)) next in
    (next' , m₂ , tt)
  chanmap (distrib⁻¹ Γ₁ Γ₂ Γ₃) next m₁ =
    let (next' , m₂) = chans ((Γ₁ + Γ₂) ∗ Γ₃) next in
    (next' , m₂ , tt)
  chanmap (x₁ ; x₂) next m₁ =
    let (next' , m₂ , m') = chanmap x₁ next m₁ in
    let (next'' , m) = chans _ next' in
    let (next''' , m₃ , m'') = chanmap x₂ next'' m₂ in
    (next''' , m₃ , (m , m' , m''))
  chanmap (x ∥ x') next (m₁ , m₁') =
    let (next' , m₂ , m) = chanmap x next m₁ in
    let (next'' , m₂' , m') = chanmap x' next' m₁' in
    (next'' , (m₂ , m₂') , (m , m'))
  chanmap (x ◇ x') next (i₊ , i₁ , i₂) =
    let (next' , o₁ , m) = chanmap x next i₁ in
    let (next'' , o₂ , m') = chanmap x' next' i₂ in
    let (next''' , o₊) = foo location-count next'' in
    (next''' , (o₊ , o₁ , o₂) , (m , m'))
  chanmap (locally {τ₁} {τ₂} l f) next _ =
    let (next' , o) = chans (τ₂ ＠ l) next in
    (next' , o , tt)
  chanmap (transmit {τ} l₁ l₂) next _ =
    let (next' , o) = chans (τ ＠ l₂) next in
    (next' , o , tt)
  chanmap (init l) next _ =
    let o = next in
    let next' = ℕ.suc next in
    (next' , o , tt)
  chanmap (term l) next _ =
    (next , tt , tt)
  chanmap (fork l τ₁ τ₂) next _ =
    let (next' , o) = chans ((τ₁ ＠ l) ∗ (τ₂ ＠ l)) next in
    (next' , o , tt)
  chanmap (join l τ₁ τ₂) next _ =
    let (next' , o) = chans ((τ₁ ⊗ τ₂) ＠ l) next in
    (next' , o , tt)
  chanmap (branch l τ₁ τ₂) next i =
    let (next' , o) = chans ((τ₁ ＠ l) + (τ₂ ＠ l)) next in
    (next' , o , tt)
  chanmap (coalesce l τ₁ τ₂) next i =
    let (next' , o) = chans ((τ₁ ⊕ τ₂) ＠ l) next in
    (next' , o , tt)

  chanmap' : (x : Γ₁ ⇶ Γ₂) → ∃[ m₁ ] ∃[ m₂ ] ChanMap x m₁ m₂
  chanmap' {Γ₁ = Γ₁} {Γ₂ = Γ₂} x =
    let (n , m₁) = chans Γ₁ 0 in
    let (_ , m₂ , m) = chanmap x n m₁ in
    (m₁ , m₂ , m)

  par-all : (Loc → Pi) → Pi
  par-all f = helper location-count f
    where
      helper : (n : ℕ) → (Fin n → Pi) → Pi
      helper ℕ.zero    _ = halt
      helper (ℕ.suc n) f = f Fin.zero ∥ helper n (f ∘ Fin.suc)

  π-broadcast : (Loc → Chan) → ⟦ 𝟙 ⊕ 𝟙 ⟧ → Pi
  π-broadcast o⃗₊ b = par-all (λ l → ⟨ o⃗₊ l ! 𝟙 ⊕ 𝟙 , b ⟩)

  as : Loc → Pi → (Loc → Pi)
  as l π self = if does (self ≟ l) then π else halt

  _■_ : (Loc → Pi) → (Loc → Pi) → (Loc → Pi)
  (π₁ ■ π₂) self = π₁ self ∥ π₂ self

  infixl 20 _■_

  π-id : (Γ : ChoreoHeap) → (i⃗ : ChanTree Γ) → (o⃗ : ChanTree Γ) → Loc → Pi
  π-id ∅ i⃗ o⃗ self = halt
  π-id (τ ＠ l) i⃗ o⃗ = as l (⟨ i⃗ ¿ τ , x ⟩ ⟨ o⃗ ! τ , x ⟩)
  π-id (Γ₁ ∗ Γ₂) (i⃗₁ , i⃗₂) (o⃗₁ , o⃗₂) self = π-id Γ₁ i⃗₁ o⃗₁ self ∥ π-id Γ₂ i⃗₂ o⃗₂ self
  π-id (Γ₁ + Γ₂) (i⃗₊ , i⃗₁ , i⃗₂) (o₊ , o⃗₁ , o⃗₂) self =
    ⟨ i⃗₊ self ¿ 𝟙 ⊕ 𝟙 , b ⟩
    Sum.[ (λ _ → π-id Γ₁ i⃗₁ o⃗₁ self) , (λ _ → π-id Γ₂ i⃗₂ o⃗₂ self) ] b

  -- The type of input at a projected location.
  π-Input : (Γ : ChoreoHeap) → Loc → Ty
  π-Input ∅ self = 𝟙
  π-Input (τ ＠ l) self = if does (self ≟ l) then τ else 𝟙
  π-Input (Γ ∗ Γ') self = π-Input Γ self ⊗ π-Input Γ' self
  π-Input (Γ + Γ') self = π-Input Γ self ⊕ π-Input Γ' self

  -- The encoding of an input at a location as a π-calculus term.
  π-input : (Γ : ChoreoHeap) → ChanTree Γ → ⟦ Centralized Γ ⟧ → (self : Loc) → Pi
  π-input ∅ o⃗ v self = halt
  π-input (τ ＠ l) o v self with self ≟ l
  ... | yes _ = ⟨ o ! τ , v ⟩
  ... | no  _ = halt
  π-input (Γ ∗ Γ') (o⃗ , o⃗') (v , v') self = π-input Γ o⃗ v self ∥ π-input Γ' o⃗' v' self
  π-input (Γ + Γ') (o⃗₊ , o⃗ , o⃗') (_⊎_.inj₁ x ) self = ⟨ o⃗₊ self ! 𝟙 ⊕ 𝟙 , _⊎_.inj₁ tt ⟩ ∥ π-input Γ  o⃗  x  self
  π-input (Γ + Γ') (o⃗₊ , o⃗ , o⃗') (_⊎_.inj₂ x') self = ⟨ o⃗₊ self ! 𝟙 ⊕ 𝟙 , _⊎_.inj₁ tt ⟩ ∥ π-input Γ' o⃗' x' self

  -- TODO: Define the type (and encoding) of input for the centralized+procedural semantics,
  -- and show that it is related to `par-all (π-input Γ o⃗ v)` by a permutation of parallel proceses.

  π-epp : {Γ₁ Γ₂ : ChoreoHeap} → (x : Γ₁ ⇶ Γ₂)
        --^ For any cCSD
        → (i⃗ : ChanTree Γ₁) → (o⃗ : ChanTree Γ₂) → ChanMap x i⃗ o⃗
        --^ and an assignment of channel names to every site in the cCSD
        → Loc → Pi
        --^ we can produce a family of π-calculus programs, one for each choreographic language.
  π-epp (id _) i⃗ o⃗ m⃗ = π-id _ i⃗ o⃗
  π-epp (swap Γ₁ Γ₂) (i⃗₁ , i⃗₂) (o⃗₁ , o⃗₂) _ =
    ( π-id _ i⃗₁ o⃗₂
    ■ π-id _ i⃗₂ o⃗₁ )
  π-epp (assoc Γ₁ Γ₂ Γ₃) ((i⃗₁ , i⃗₂) , i⃗₃) (o⃗₁ , (o⃗₂ , o⃗₃)) _ =
    ( π-id _ i⃗₁ o⃗₁
    ■ π-id _ i⃗₂ o⃗₂
    ■ π-id _ i⃗₃ o⃗₃ )
  π-epp (assoc⁻¹ Γ₁ Γ₂ Γ₃) (i⃗₁ , (i⃗₂ , i⃗₃)) ((o⃗₁ , o⃗₂) , o⃗₃) _ =
    ( π-id _ i⃗₁ o⃗₁
    ■ π-id _ i⃗₂ o⃗₂
    ■ π-id _ i⃗₃ o⃗₃ )
  π-epp (distrib _ _ _) ((i⃗₊ , i⃗₁ , i⃗₂) , i⃗₃) (o⃗₊ , (o⃗₁ , o⃗₃) , (o⃗₂ , o⃗₃')) _ self =
    ⟨ i⃗₊ self ¿ 𝟙 ⊕ 𝟙 , b ⟩
    ( ⟨ o⃗₊ self ! 𝟙 ⊕ 𝟙 , b ⟩
    ∥ Sum.[ (λ _ →   π-id _ i⃗₁ o⃗₁  self
                   ∥ π-id _ i⃗₃ o⃗₃  self )
          , (λ _ →   π-id _ i⃗₂ o⃗₂  self
                   ∥ π-id _ i⃗₃ o⃗₃' self )
          ] b )
  π-epp (distrib⁻¹ _ _ _) (i⃗₊ , (i⃗₁ , i⃗₃) , (i⃗₂ , i⃗₃')) ((o⃗₊ , o⃗₁ , o⃗₂) , o⃗₃) _ self =
    ⟨ i⃗₊ self ¿ 𝟙 ⊕ 𝟙 , b ⟩
    ( ⟨ o⃗₊ self ! 𝟙 ⊕ 𝟙 , b ⟩
    ∥ Sum.[ (λ _ →   π-id _ i⃗₁  o⃗₁ self
                   ∥ π-id _ i⃗₃  o⃗₃ self )
          , (λ _ →   π-id _ i⃗₂  o⃗₂ self
                   ∥ π-id _ i⃗₃' o⃗₃ self )
          ] b )
  π-epp (x₁ ; x₂) i⃗ o⃗ (m⃗ , m⃗₁ , m⃗₂) = π-epp x₁ i⃗ m⃗ m⃗₁ ■ π-epp x₂ m⃗ o⃗ m⃗₂
  π-epp (x  ∥ x') (i⃗ , i⃗') (o⃗ , o⃗') (m⃗ , m⃗') = π-epp x i⃗ o⃗ m⃗ ■ π-epp x' i⃗' o⃗' m⃗'
  π-epp (x  ◇ x') (i⃗₊ , i⃗ , i⃗') (o⃗₊ , o⃗ , o⃗') (m⃗ , m⃗') self =
    ⟨ i⃗₊ self ¿ 𝟙 ⊕ 𝟙 , b ⟩
    ( ⟨ o⃗₊ self ! 𝟙 ⊕ 𝟙 , b ⟩
    ∥ Sum.[ (λ _ → π-epp x i⃗ o⃗ m⃗ self)
          , (λ _ → π-epp x' i⃗' o⃗' m⃗' self)
          ] b )
  π-epp (locally {τ₁} {τ₂} l f) i o m =
    as l
      ( ⟨ i ¿ τ₁ ,   x ⟩
        ⟨ o ! τ₂ , f x ⟩ )
  π-epp (transmit {τ} l₁ l₂) i o m =
    as l₁ (⟨ i ¿ τ , x ⟩ ⟨ o ! τ , x ⟩)
  π-epp (init l) _ o _ =
    as l ⟨ o ! 𝟙 , tt ⟩
  π-epp (term l) i _ _ =
    as l (⟨ i ¿ 𝟙 , _ ⟩ halt)
  π-epp (fork l τ₁ τ₂) i (o₁ , o₂) _ =
    as l
      ( ⟨ i ¿ (τ₁ ⊗ τ₂) , (x₁ , x₂) ⟩
        ( ⟨ o₁ ! τ₁ , x₁ ⟩
        ∥ ⟨ o₂ ! τ₂ , x₂ ⟩ ) )
  π-epp (join l τ₁ τ₂) (i₁ , i₂) o _ =
    as l (
      ⟨ i₁ ¿ τ₁ , x ⟩
      ⟨ i₂ ¿ τ₂ , y ⟩
      ⟨ o ! (τ₁ ⊗ τ₂) , (x , y) ⟩ )
  π-epp (branch l τ₁ τ₂) i (o⃗₊ , o₁ , o₂) _ =
    as l ( ⟨ i ¿ (τ₁ ⊕ τ₂) , x ⟩
           Sum.[ (λ a → π-broadcast o⃗₊ (_⊎_.inj₁ tt) ∥ ⟨ o₁ ! τ₁ , a ⟩)
               , (λ b → π-broadcast o⃗₊ (_⊎_.inj₂ tt) ∥ ⟨ o₂ ! τ₂ , b ⟩ ) ] x)
  π-epp (coalesce l τ₁ τ₂) (i₊ , i₁ , i₂) o _ self =
    as l ( ⟨ i₊ self ¿ 𝟙 ⊕ 𝟙 , b ⟩
           Sum.[ (λ _ → ⟨ i₁ ¿ τ₁ , x ⟩ ⟨ o ! (τ₁ ⊕ τ₂) , _⊎_.inj₁ x ⟩)
               , (λ _ → ⟨ i₂ ¿ τ₂ , x ⟩ ⟨ o ! (τ₁ ⊕ τ₂) , _⊎_.inj₂ x ⟩) ] b )
       self

  π-centralized : {Γ₁ Γ₂ : ChoreoHeap} → (x : Γ₁ ⇶ Γ₂)
                --^ For any cCSD
                → (i⃗ : ChanTree Γ₁) → (o⃗ : ChanTree Γ₂) → ChanMap x i⃗ o⃗
                --^ and an assignment of channel names to every site in the cCSD
                → Pi
                --^ we can produce a π-calculus program
  π-centralized (id Γ) i⃗ o⃗ m = par-all (π-epp (id Γ) i⃗ o⃗ m)
  π-centralized (swap Γ₁ Γ₂) i⃗ o⃗ m = par-all (π-epp (swap Γ₁ Γ₂) i⃗ o⃗ m)
  π-centralized (assoc Γ₁ Γ₂ Γ₃) i⃗ o⃗ _ = {!!}
  π-centralized (assoc⁻¹ Γ₁ Γ₂ Γ₃) i⃗ o⃗ _ = {!!}
  π-centralized (distrib _ _ _) i⃗ o⃗ _ = {!!}
  π-centralized (distrib⁻¹ _ _ _) i⃗ o⃗ _ = {!!}
  π-centralized (x ; x₁) i⃗ o⃗ _ = {!!}
  π-centralized (x ∥ x₁) i⃗ o⃗ _ = {!!}
  π-centralized (x ◇ x₁) i⃗ o⃗ _ = {!!}
  π-centralized (locally l x) i⃗ o⃗ _ = {!!}
  π-centralized (transmit l₁ l₂) i⃗ o⃗ _ = {!!}
  π-centralized (init l) i⃗ o⃗ _ = {!!}
  π-centralized (term l) i⃗ o⃗ _ = {!!}
  π-centralized (fork l a b) i⃗ o⃗ _ = {!!}
  π-centralized (join l a b) i⃗ o⃗ _ = {!!}
  π-centralized (branch l a b) i⃗ o⃗ _ = {!!}
  π-centralized (coalesce l a b) i⃗ o⃗ _ = {!!}

  π-centralized≅epp : {Γ₁ Γ₂ : ChoreoHeap} → (x : Γ₁ ⇶ Γ₂)
                    --^ For any cCSD
                    → (i⃗ : ChanTree Γ₁) → (o⃗ : ChanTree Γ₂) → (m : ChanMap x i⃗ o⃗)
                    --^ and an assignment of channel names to every site in the cCSD
                    → (π-centralized x i⃗ o⃗ m ≅ par-all (π-epp x i⃗ o⃗ m))
                    --^ we can produce a π-calculus program
  π-centralized≅epp (id _) i⃗ o⃗ m = π-refl _
  π-centralized≅epp (swap Γ₁ Γ₂) i⃗ o⃗ m = {!!}
  π-centralized≅epp (assoc Γ₁ Γ₂ Γ₃) i⃗ o⃗ m = {!!}
  π-centralized≅epp (assoc⁻¹ Γ₁ Γ₂ Γ₃) i⃗ o⃗ m = {!!}
  π-centralized≅epp (distrib _ _ _) i⃗ o⃗ m = {!!}
  π-centralized≅epp (distrib⁻¹ _ _ _) i⃗ o⃗ m = {!!}
  π-centralized≅epp (x ; x₁) i⃗ o⃗ m = {!!}
  π-centralized≅epp (x ∥ x₁) i⃗ o⃗ m = {!!}
  π-centralized≅epp (x ◇ x₁) i⃗ o⃗ m = {!!}
  π-centralized≅epp (locally l x) i⃗ o⃗ m = {!!}
  π-centralized≅epp (transmit l₁ l₂) i⃗ o⃗ m = {!!}
  π-centralized≅epp (init l) i⃗ o⃗ m = {!!}
  π-centralized≅epp (term l) i⃗ o⃗ m = {!!}
  π-centralized≅epp (fork l a b) i⃗ o⃗ m = {!!}
  π-centralized≅epp (join l a b) i⃗ o⃗ m = {!!}
  π-centralized≅epp (branch l a b) i⃗ o⃗ m = {!!}
  π-centralized≅epp (coalesce l a b) i⃗ o⃗ m = {!!}
```
