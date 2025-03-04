<!--
```agda
{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
```
-->

```agda
open import Relation.Binary using (DecidableEquality)

module Choreographies.Bar {Loc : Type} {_≟_ : DecidableEquality Loc} where
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
    using (_×_; _,_; ∃-syntax; proj₁; proj₂)
  open import Data.Sum
    using (_⊎_)
  open import Data.Nat
    using (ℕ)
  open import Data.Bool
    using (Bool; true; false; if_then_else_)
  open import Data.Maybe
    as Maybe
    using (Maybe; fromMaybe)
    renaming (just to some; nothing to none)
  open import Data.These
    using (These; this; that; these)
  open import Data.List
    using (List; []; _∷_; [_])
  open import Data.List.Relation.Unary.Any
    using (here; there)
  open import Relation.Nullary.Negation
    using (¬_)
  open import Relation.Nullary.Decidable
    using (Dec; does; _because_; yes; no; _⊎-dec_)
  open import Relation.Nullary.Reflects
    using (Reflects)
  open import Data.List.Membership.DecPropositional _≟_
    using (_∈_; _∈?_)
  open import Data.List.Relation.Binary.Subset.DecPropositional _≟_
    using (_⊆_; _⊆?_)
  open import Relation.Binary.PropositionalEquality
    as Eq
    using (_≡_)

  infixl 25 _⊗_
  infixl 24 _⊕_
  infix  23 _＠_
  infixl 22 _∗_
  infixl 21 _+_
  infix  20 _⇶_
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
    distrib   : ((Γ₁ + Γ₂) ∗ Γ₃) ⇶ ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃))
    distrib⁻¹ : ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃)) ⇶ ((Γ₁ + Γ₂) ∗ Γ₃)

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

  _⇒_ : Ty → Ty → Type
  data NetworkProgram : Type

  τ₁ ⇒ τ₂ = ⟦ τ₁ ⟧ → (⟦ τ₂ ⟧ → NetworkProgram) → NetworkProgram

  data NetworkProgram where
    {- F(X) = ( ((τ : Ty) × ⟦ τ ⟧)       -- pure
              + ((τ : Ty) × ℕ × ⟦ τ ⟧)   -- send
              + ((τ : Ty) × ℕ × X^⟦ τ ⟧) -- recv
              )
    -}
    -- (τ : Ty, ⟦ τ ⟧) ↝ ⊤
    pure : (τ : Ty) → ⟦ τ ⟧ → NetworkProgram
    -- (τ : Ty, ℕ, ⟦ τ ⟧) ↝ ⊤
    send : (τ : Ty) (id : Loc) (payload : ⟦ τ ⟧) → (⊤ → NetworkProgram) → NetworkProgram
    -- (τ : Ty, ℕ) ↝ ⟦ τ ⟧
    recv : (τ : Ty) (id : Loc) → (⟦ τ ⟧ → NetworkProgram) → NetworkProgram
    --
    broadcast : Bool → (⊤ → NetworkProgram) → NetworkProgram
    recvbcast : (Bool → NetworkProgram) → NetworkProgram
    -- TODO: come up with a `par` combinator that Agda would accept.
    -- TODO: uniquely identify messages (i.e. add a uniquely-generated ℕ)
    --       and maybe consider removing the id:Loc parameter (if it can be
    --       recovered from an id-to-receiver table)
    -- TODO: implement broadcast and recvbcast in terms of send and recv

{-
  fleh : (⟦ τ₁ ⟧ → NetworkProgram) → (⟦ τ₂ ⟧ → NetworkProgram) → (⟦ τ₁ ⊗ τ₂ ⟧ → NetworkProgram)
-}

    --par : (NetworkProgram × NetworkProgram) → NetworkProgram
-- (τ₁ τ₂ : Ty)
-- → ((⟦ τ₁ ⟧ → NetworkProgram) → NetworkProgram)
-- → ((⟦ τ₂ ⟧ → NetworkProgram) → NetworkProgram)
-- → (⟦ τ₂ ⟧ × ⟦ τ₂ ⟧ → NetworkProgram)


  _in:_ : Loc → ChoreoHeap → Type
  self in: ∅        = ⊥
  self in: (τ ＠ l) = l ≡ self
  self in: (Γ ∗ Γ') = self in: Γ ⊎ self in: Γ'
  self in: (Γ + Γ') = self in: Γ ⊎ self in: Γ'

  _in?_ : (l : Loc) → (Γ : ChoreoHeap) → Dec (l in: Γ)
  self in? ∅ = no λ ■ → ■
  self in? (τ ＠ l) = l ≟ self
  self in? (Γ ∗ Γ') = (self in? Γ) ⊎-dec (self in? Γ')
  self in? (Γ + Γ') = (self in? Γ) ⊎-dec (self in? Γ')

  _ddd:_ : ∀{ℓ} {T₁ T₂ : Type ℓ} → Maybe T₁ → Maybe T₂ → Maybe (These T₁ T₂)
  some s ddd: some s' = some (these s s')
  some s ddd: none    = some (this s)
  none   ddd: some s' = some (that s')
  none   ddd: none    = none

  Selector : ChoreoHeap → Type
  Selector ∅ = ⊥
  Selector (_ ＠ _) = ⊤
  Selector (Γ ∗ Γ') = These (Selector Γ) (Selector Γ')
  Selector (Γ + Γ') = These (Selector Γ) (Selector Γ')

  --   Maybe (These (Selector Γ₁) (Selector Γ₁')) × Maybe (These (Selector Γ₂) (Selector Γ₂'))
  -- → (Maybe (Selector Γ₁) × Maybe (Selector Γ₂)) × (Maybe (Selector Γ₁') × Maybe (Selector Γ₂'))
  --
  bbb : {A B : Type} → Maybe (These A B) → (Maybe A × Maybe B)
  bbb (some (this a)) = some a , none
  bbb (some (that b)) = none , some b
  bbb (some (these a b)) = some a , some b
  bbb none = none , none

{-
  Foo : (Γ₁ ⇶ Γ₂) → Maybe (Selector Γ₁) → Maybe (Selector Γ₂) → Type
  Foo (id _) s₁ s₂ = s₁ ≡ s₂
  Foo (x ∥ x') s₁ s₂ =
    let (s₁ , s₁') = bbb s₁ in
    let (s₂ , s₂') = bbb s₂ in
    Foo x s₁ s₂ × Foo x' s₁' s₂'
  Foo (x ◇ x') s₁ s₂ =
    let (s₁ , s₁') = bbb s₁ in
    Foo x s₁ s₂ × Foo x' s₁' s₂
  Foo (x₁ ; x₂) s₁ s₂ =
    ∃[ sₘ ] Foo x₁ s₁ sₘ × Foo x₂ sₘ s₂
  Foo (locally l x) (some s₁) (some s₂) = s₁ ≡ s₂
  Foo (locally l x) (some _) none = ⊥
  Foo (locally l x) none (some _) = ⊥
  Foo (locally l x) none none = ⊥
  Foo (transmit l₁ l₂) s₁ s₂ = ⊤
  Foo (fork l a b) (some s₁) (some s₂) = s₂ ≡ these s₁ s₁
  Foo (fork l a b) (some _) none = ⊥
  Foo (fork l a b) none (some _) = ⊥
  Foo (fork l a b) none none = ⊥
  Foo (join l a b) (some s₁) (some s₂) = s₁ ≡ these s₂ s₂
  Foo (join l a b) (some _) none = ⊥
  Foo (join l a b) none (some _) = ⊥
  Foo (join l a b) none none = ⊥
  Foo (branch l a b) (some s₁) (some s₂) = s₂ ≡ these s₁ s₁
  Foo (branch l a b) (some _) none = ⊥
  Foo (branch l a b) none (some _) = ⊥
  Foo (branch l a b) none none = ⊥
  Foo distrib (some s₁) (some s₂) = {!!}
  Foo distrib (some _) none = {!!}
  Foo distrib none (some _) = {!!}
  Foo distrib none none = {!!}
  Foo (swap Γ₁ Γ₂) s₁ s₂ = {!!}
  Foo (assoc Γ₁ Γ₂ Γ₃) s₁ s₂ = {!!}
  Foo (assoc⁻¹ Γ₁ Γ₂ Γ₃) s₁ s₂ = {!!}
-}

  select : (Γ : ChoreoHeap) → Loc → Maybe (Selector Γ)
  select ∅        self = none
  select (_ ＠ l) self = if does (l ≟ self) then some tt else none
  select (Γ ∗ Γ') self = select Γ self ddd: select Γ' self
  select (Γ + Γ') self = select Γ self ddd: select Γ' self

{-
  Epp : (Γ : ChoreoHeap) → Maybe (Selector Γ) → Ty
  Epp Γ = Maybe.fromMaybe 𝟙 ∘ Maybe.map (go Γ)
    where
      go : (Γ : ChoreoHeap) → Selector Γ → Ty
      go (τ ＠ _)        s     = τ
      go (Γ ∗ Γ') (this  s)    = go Γ s
      go (Γ ∗ Γ') (that    s') =          go Γ' s'
      go (Γ ∗ Γ') (these s s') = go Γ s ⊗ go Γ' s'
      go (Γ + Γ') (this  s)    = go Γ s ⊕ 𝟙
      go (Γ + Γ') (that    s') =      𝟙 ⊕ go Γ' s'
      go (Γ + Γ') (these s s') = go Γ s ⊕ go Γ' s'
-}

{-
  Epp : (Γ : ChoreoHeap) → Loc → Ty
  Epp ∅         self = 𝟙
  Epp (τ ＠ l)  self = if does (l ≟ self) then τ else 𝟙
  Epp (Γ₁ ∗ Γ₂) self with self in? Γ₁ | self in? Γ₂
  ... | true  because _ | true  because _ = Epp Γ₁ self ⊗ Epp Γ₂ self
  ... | true  because _ | false because _ = Epp Γ₁ self
  ... | false because _ | true because  _ = Epp Γ₂ self
  ... | false because _ | false because _ = 𝟙
  Epp (Γ₁ + Γ₂) self = Epp Γ₁ self ⊕ Epp Γ₂ self
-}

  Epp : (Γ : ChoreoHeap) → Loc → Ty
  Epp ∅         self = 𝟙
  Epp (τ ＠ l)  self = if does (l ≟ self) then τ else 𝟙
  Epp (Γ₁ ∗ Γ₂) self = Epp Γ₁ self ⊗ Epp Γ₂ self
  Epp (Γ₁ + Γ₂) self = Epp Γ₁ self ⊕ Epp Γ₂ self

  -- ⟦ Epp Γ₁ l ⟧ ⇒ ⟦ Epp Γ₂ l ⟧
  epp : (Γ₁ ⇶ Γ₂) → (l : Loc) → (Epp Γ₁ l ⇒ Epp Γ₂ l)
  epp (id _) self i k =
    k i
  epp (swap Γ₁ Γ₂) self (i₁ , i₂) k =
    k (i₂ , i₁)
  epp (assoc Γ₁ Γ₂ Γ₃) self ((i₁ , i₂) , i₃) k =
    k (i₁ , (i₂ , i₃))
  epp (assoc⁻¹ Γ₁ Γ₂ Γ₃) self (i₁ , (i₂ , i₃)) k =
    k ((i₁ , i₂) , i₃)
  epp distrib self (_⊎_.inj₁ x , z) k =
    k (_⊎_.inj₁ (x , z))
  epp distrib self (_⊎_.inj₂ y , z) k =
    k (_⊎_.inj₂ (y , z))
  epp distrib⁻¹ self (_⊎_.inj₁ (x , z)) k =
    k (_⊎_.inj₁ x , z)
  epp distrib⁻¹ self (_⊎_.inj₂ (y , z)) k =
    k (_⊎_.inj₂ y , z)
  --
  epp (x₁ ; x₂) self i k =
    epp x₁ self i  λ i'  →
    epp x₂ self i' λ i'' →
    k i''
  epp (x  ∥ x') self (i₁ , i₁') k =
    -- TODO: find some way to bind over both i₂ and i₂' without sequencing them?
    epp x  self i₁  λ i₂  →
    epp x' self i₁' λ i₂' →
    let _ = ? in
    k (i₂ , i₂')
  epp (x ◇ x') self (_⊎_.inj₁ i₁ ) k =
    epp x self i₁ λ i₂ →
    k (_⊎_.inj₁ i₂)
  epp (x ◇ x') self (_⊎_.inj₂ i₁') k =
    epp x' self i₁' λ i₂' →
    k (_⊎_.inj₂ i₂')
  epp (locally l f) self i k with l ≟ self
  ... | yes _ = k (f i)
  ... | no  _ = k i
  epp (transmit l₁ l₂) self i k with l₁ ≟ self | l₂ ≟ self
  ... | no  _ | no  _ = k i
  ... | no  _ | yes _ = recv _ l₁   k
  ... | yes _ | no  _ = send _ l₂ i k
  ... | yes _ | yes _ = k i
  epp (init l) self i k with l ≟ self
  ... | no  _ = k i
  ... | yes _ = k i
  epp (term l) self with l ≟ self
  ... | no  _ = λ i k → k i
  ... | yes _ = λ i k → k i
  epp (fork l a b) self with l ≟ self
  ... | no  _ = λ i        k → k (i , i)
  ... | yes _ = λ (i , i') k → k (i , i')
  epp (join l a b) self (i , i') k with l ≟ self
  ... | no  _ = k tt
  ... | yes _ = k (i , i')
  epp (branch l a b) self with l ≟ self
  ... | no  _ = λ i k →
    recvbcast λ
      { false → k (_⊎_.inj₁ i)
      ; true  → k (_⊎_.inj₂ i)
      }
  ... | yes _ = λ
    { (_⊎_.inj₁ x) k →
        broadcast false λ _ →
        k (_⊎_.inj₁ x)
    ; (_⊎_.inj₂ y) k →
        broadcast true λ _ →
        k (_⊎_.inj₂ y)
    }
  epp (coalesce l a b) self i k with l ≟ self
  ... | no  _ = k tt
  ... | yes _ = k i

  Centralized : ChoreoHeap → Ty
  Centralized ∅         = 𝟙
  Centralized (τ ＠ l)  = τ
  Centralized (Γ₁ ∗ Γ₂) = Centralized Γ₁ ⊗ Centralized Γ₂
  Centralized (Γ₁ + Γ₂) = Centralized Γ₁ ⊕ Centralized Γ₂

  centralized : (Γ₁ ⇶ Γ₂) → (⟦ Centralized Γ₁ ⟧ → ⟦ Centralized Γ₂ ⟧)
  centralized (id _) i = i
  centralized (swap Γ₁ Γ₂) (fst , snd) = snd , fst
  centralized (assoc Γ₁ Γ₂ Γ₃) ((fst , snd₁) , snd) = fst , snd₁ , snd
  centralized (assoc⁻¹ Γ₁ Γ₂ Γ₃) (fst , fst₁ , snd) = (fst , fst₁) , snd
  centralized distrib (_⊎_.inj₁ x , snd) = _⊎_.inj₁ (x , snd)
  centralized distrib (_⊎_.inj₂ y , snd) = _⊎_.inj₂ (y , snd)
  centralized distrib⁻¹ (_⊎_.inj₁ (fst , snd)) = _⊎_.inj₁ fst , snd
  centralized distrib⁻¹ (_⊎_.inj₂ (fst , snd)) = _⊎_.inj₂ fst , snd
  centralized (x ; x₁) i = centralized x₁ (centralized x i)
  centralized (x ∥ x₁) (fst , snd) = centralized x fst , centralized x₁ snd
  centralized (x ◇ x₁) (_⊎_.inj₁ x₂) = _⊎_.inj₁ (centralized x x₂)
  centralized (x ◇ x₁) (_⊎_.inj₂ y) = _⊎_.inj₂ (centralized x₁ y)
  centralized (locally l x) i = x i
  centralized (transmit l₁ l₂) i = i
  centralized (init l) i = tt
  centralized (term l) i = tt
  centralized (fork l a b) i = i
  centralized (join l a b) i = i
  centralized (branch l a b) i = i
  centralized (coalesce l a b) i = i
```
