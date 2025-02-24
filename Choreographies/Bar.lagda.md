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
    using (_×_; _,_; ∃-syntax)
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
  infix  20 Choreo

  syntax Choreo ls Γ Γ' = Γ ⇶[ ls ] Γ'
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


  data ChoreoHeap (ls : List Loc) : Type where
    -- an empty heap
    ∅        : ChoreoHeap ls
    -- a discrete site owned by one of the `ls`.
    _＠_     : Ty → (l : Loc) → {{Reflects (l ∈ ls) true}} → ChoreoHeap ls
    -- restrict knowledge of a heap to locations on an explicit allowlist
    restrict : ∀ ls' → {{Reflects (ls' ⊆ ls) true}} → ChoreoHeap ls' → ChoreoHeap ls
    -- a pair of separated heaps split among all `ls`.
    _∗_      : (_ _ : ChoreoHeap ls) → ChoreoHeap ls
    -- a choice between heaps whose determination is known to all `ls`
    _+_      : (_ _ : ChoreoHeap ls) → ChoreoHeap ls

  unrestrict : {ls' ls : List Loc} → ChoreoHeap ls' → {{Reflects (ls' ⊆ ls) true}} → ChoreoHeap ls
  unrestrict ∅ = ∅
  unrestrict ((x ＠ l) ⦃ Reflects.ofʸ p ⦄) ⦃ Reflects.ofʸ a ⦄ = (x ＠ l) ⦃ Reflects.ofʸ (a {l} p) ⦄
  unrestrict (restrict ls' ⦃ Reflects.ofʸ a ⦄ Γ) ⦃ Reflects.ofʸ b ⦄ = restrict ls' ⦃ Reflects.ofʸ (b ∘ a) ⦄ Γ
  unrestrict (Γ ∗ Γ') = unrestrict Γ ∗ unrestrict Γ'
  unrestrict (Γ + Γ') = unrestrict Γ + unrestrict Γ'


  variable
    Γ  Γ₁  Γ₂  Γ₃  : ChoreoHeap _
    Γ' Γ₁' Γ₂' Γ₃' : ChoreoHeap _

  data Choreo (ls : List Loc) : (_ _ : ChoreoHeap ls) → Type where
    id : ∀ Γ → Γ ⇶[ ls ] Γ

    -- permutations on sites
    swap    : ∀ Γ₁ Γ₂    → (Γ₁ ∗ Γ₂) ⇶[ ls ] (Γ₂ ∗ Γ₁)
    assoc   : ∀ Γ₁ Γ₂ Γ₃ → ((Γ₁ ∗  Γ₂) ∗ Γ₃ ) ⇶[ ls ] ( Γ₁ ∗ (Γ₂  ∗ Γ₃))
    assoc⁻¹ : ∀ Γ₁ Γ₂ Γ₃ → ( Γ₁ ∗ (Γ₂  ∗ Γ₃)) ⇶[ ls ] ((Γ₁ ∗  Γ₂) ∗ Γ₃ )
  --unitₗ   : ∀ Γ        → (∅ ∗ Γ) ⇶[ ls ]      Γ
  --unitₗ⁻¹ : ∀ Γ        →      Γ  ⇶[ ls ] (∅ ∗ Γ)

    -- products can distribute over sums
    distrib   : (Γ₁ + Γ₂ ∗ Γ₃) ⇶[ ls ] ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃))
    distrib⁻¹ : ((Γ₁ ∗ Γ₃) + (Γ₂ ∗ Γ₃)) ⇶[ ls ] (Γ₁ + Γ₂ ∗ Γ₃)

    -- sequential composition
    _;_ : (x₁ : Γ₁ ⇶[ ls ] Γ₂)
        → (x₂ : Γ₂ ⇶[ ls ] Γ₃)
        → (Γ₁ ⇶[ ls ] Γ₃)

    -- concurrent composition over products
    _∥_ : (Γ₁       ⇶[ ls ] Γ₂      )
        → (     Γ₁' ⇶[ ls ]      Γ₂')
        → (Γ₁ ∗ Γ₁' ⇶[ ls ] Γ₂ ∗ Γ₂')

    -- concurrent composition over sums
    _◇_ : (Γ₁       ⇶[ ls ] Γ₂)
        → (     Γ₁' ⇶[ ls ] Γ₂')
        → (Γ₁ + Γ₁' ⇶[ ls ] Γ₂ + Γ₂')

    -- a local computation at a site
    locally : ∀{a b} l {{_ : Reflects (l ∈ ls) true}} → (a ⟶ b) → ((a ＠ l) ⇶[ ls ] (b ＠ l))
    -- transferrence of state between chroreographic locations
    transmit : ∀{a} l₁ {{_ : Reflects (l₁ ∈ ls) true}} l₂ {{_ : Reflects (l₂ ∈ ls) true}} → (a ＠ l₁) ⇶[ ls ] (a ＠ l₂)

    -- the creation of a site
    init : ∀ l {{_ : Reflects (l ∈ ls) true}} → ∅ ⇶[ ls ] (𝟙 ＠ l)
    -- the destruction of a site
    term : ∀ l {{_ : Reflects (l ∈ ls) true}} → (𝟙 ＠ l) ⇶[ ls ] ∅

    -- the factorization of one site into two
    fork : ∀ l {{_ : Reflects (l ∈ ls) true}} a b → (a ⊗ b ＠ l) ⇶[ ls ] (a ＠ l ∗ b ＠ l)
    -- the assimilation of two sites into one
    join : ∀ l {{_ : Reflects (l ∈ ls) true}} a b → (a ＠ l ∗ b ＠ l) ⇶[ ls ] (a ⊗ b ＠ l)

    -- the externalization of two possibilities at one site
    branch   : ∀ l {{_ : Reflects (l ∈ ls) true}} a b → (a ⊕ b ＠ l) ⇶[ ls ] (a ＠ l + b ＠ l)
    -- the internalization of two possibilities at one site
    coalesce : ∀ l {{_ : Reflects (l ∈ ls) true}} a b → (a ＠ l + b ＠ l) ⇶[ ls ] (a ⊕ b ＠ l)

    notify : ∀ ls' {{_ : Reflects (ls' ⊆ ls) true}}
           → (Γ : ChoreoHeap ls')
           → restrict ls' Γ ⇶[ ls ] unrestrict Γ

    enclose : ∀ ls' {{_ : Reflects (ls' ⊆ ls) true}}
            → (Γ : ChoreoHeap ls')
            → unrestrict Γ ⇶[ ls ] restrict ls' Γ

    -- todo: `restrict` units, i.e. `restrict ls Γ ⇶[ ls ] Γ` (matching the outer)
    -- todo: `restrict` combinations, i.e. `restrict ls' (restrict ls'' Γ) ⇶[ ls ] restrict ls'' Γ` (matching the inner)
    -- todo: motion across `restrict`, i.e. `restrict ls' Γ ∗ Γ' ⇶[ ls ] restrict ls' (Γ ∗ Γ')`
    -- todo: `restrict` distribution, i.e. `restrict ls' (Γ ∗ Γ') ⇶[ ls ] restrict ls' Γ ∗ restrict ls' Γ'`

{-
  data NetworkProgram : Type where
    pure : (τ₁ : Ty) → ⟦ τ₁ ⟧ → NetworkProgram
    send : (τ : Ty) (id : ℕ) (payload : ⟦ τ ⟧) → (⊤ → NetworkProgram) → NetworkProgram
    recv : (τ : Ty) (id : ℕ) → (⟦ τ ⟧ → NetworkProgram) → NetworkProgram

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

  select : (Γ : ChoreoHeap) → Loc → Maybe (Selector Γ)
  select ∅        self = none
  select (_ ＠ l) self = if does (l ≟ self) then some tt else none
  select (Γ ∗ Γ') self = select Γ self ddd: select Γ' self
  select (Γ + Γ') self = select Γ self ddd: select Γ' self

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

{-
  Epp : (Γ : ChoreoHeap) → Loc → Ty
  Epp ∅         self = 𝟙
  Epp (τ ＠ l)  self = if does (l ≟ self) then τ else 𝟙
  Epp (Γ₁ ∗ Γ₂) self with self in? Γ₁ | self in? Γ₂
  ... | true  because _ | true  because _ = Epp Γ₁ self ⊗ Epp Γ₂ self
  ... | true  because _ | false because _ = Epp Γ₁ self
  ... | false because _ | true because  _ = Epp Γ₂ self
  ... | false because _ | false because _ = 𝟙
  Epp (Γ₁ + Γ₂) self = if does (self ∈? ls) then Epp Γ₁ self ⊕ Epp Γ₂ self else 𝟙

  epp : (Γ₁ ⇶ Γ₂) → (l : Loc) → ⟦ Epp Γ₁ l ⟧ → (⟦ Epp Γ₂ l ⟧ → NetworkProgram) → NetworkProgram
  epp (id _) self i k = k i
  epp {Γ₁ = Γ₁ ∗ Γ₁'} {Γ₂ = Γ₂ ∗ Γ₂'} (x  ∥ x') self (i , i') k =
    epp x  self i  λ o  →
    epp x' self i' λ o' →
    k (o , o')
  epp (x  ◇[ ls ] x') self i k with self ∈? ls | i
  ... | yes p | _ = {!!}
  ... | no ¬p | _ = {!!}
  epp (x₁ ; x') l i k = {!!}
  epp (locally l₁ x) l i k = {!!}
  epp (transmit l₁ l₂) l i k = {!!}
  epp (init l₁) l i k = {!!}
  epp (term l₁) l i k = {!!}
  epp (fork l₁ a b) l i k = {!!}
  epp (join l₁ a b) l i k = {!!}
  epp (branch l₁ a b) l i k = {!!}
  epp distrib l i k = {!!}
  epp (swap Γ₁ Γ₂) l i k = {!!}
  epp (assoc Γ₁ Γ₂ Γ₃) l i k = {!!}
  epp (assoc⁻¹ Γ₁ Γ₂ Γ₃) l i k = {!!}
  epp (unitₗ _) l i k = {!!}
  epp (unitₗ⁻¹ _) l i k = {!!}
-}
-}
```
