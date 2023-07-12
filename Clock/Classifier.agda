{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
open import Relation.Binary
  using (DecidableEquality)

{-
  A clock that classifies actions and tracks a lower bound on
  the number of actions occurring in each class.

  `Act` is the type of actions that can be performed.
  `Cls` is the type of action classes.
  Every `Act` is assigned to a `Cls` by the `cls` classification function.
  `_≟_` decides if two classes are the same.

  Special cases:
  - The scalar clock of Lamport, which has only one classification.
  - The vector clock of Mattern, and of Fidge, which classifies actions
    by who performed them.
  - The matrix clock of Sarin and Lynch, and of Raynal and Singhal, which
    classifies actions by a tuple of sender and recipient.
-}
module Clock.Classifier
    (Cls : Type) (_≟_ : DecidableEquality Cls)
    (Act : Type) (cls : Act → Cls)
  where
  open import Data.Bool
    using (true; false)
  open import Data.Nat
    using (ℕ; _+_; _⊔_; _≤_)
  open import Data.Nat.Properties
    as ℕ-Prop
    using ()
  open import Data.Bool
    using (if_then_else_)
  open import Relation.Nullary
    using (does; _because_)

  open import Clock.Interpret
    as Interpret
    using (Step; act; merge)
  open import Clock.Monotonicity
    as Monotonicity
    using (Clock)
  open Clock
    using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

  -- A timestamp is a count of actions for every action class.
  Time : Type
  Time = Cls → ℕ

  alg : Step Act Time → Time
  -- The increment operation adds one to the class of the associated action.
  alg (act a t) = λ c →
    if does (cls a ≟ c)
      then 1 + t c
      else 0 + t c
  -- The merge operation takes the pointwise least upper bound
  -- (i.e. separately for each class).
  -- Notice that we cannot simply *add* the counts, because some actions
  -- might then be double-counted. Instead, if one clock has observed
  -- five actions, and another has observed seven, all we know is that
  -- at least 7 actions have definitely occurred.
  alg (merge t₁ t₂) = λ c →
    t₁ c ⊔ t₂ c

  -- Timestamps are ordered pointwise (i.e. separately for each class).
  _⊑_ : Time → Time → Type
  t₁ ⊑ t₂ = ∀ c → t₁ c ≤ t₂ c

  clock : Clock alg _⊑_
  -- _⊑_ is a preorder:
  (≤-refl      clock) _ _   = ℕ-Prop.≤-refl
  (≤-trans     clock) _ _ _ t₁≤t₂ t₂≤t₃ = λ s → ℕ-Prop.≤-trans (t₁≤t₂ s) (t₂≤t₃ s)
  -- The clock operations are increasing on _⊑_:
  (act-mono    clock) a _ s with cls a ≟ s
  ... | false because _     = ℕ-Prop.≤-refl
  ... | true  because _     = ℕ-Prop.≤-step ℕ-Prop.≤-refl
  (merge-mono¹ clock) _ _ _ = ℕ-Prop.m≤m⊔n _ _
  (merge-mono² clock) _ _ _ = ℕ-Prop.m≤n⊔m _ _

  -- Obtain a global timestamping function for any execution.
  timestamp = Interpret.timestamp alg
  -- Obtain a proof of the clock condition for any execution and any initial timestamps.
  mono = Monotonicity.timestamp-mono clock
