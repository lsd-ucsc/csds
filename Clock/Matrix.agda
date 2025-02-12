{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
open import Relation.Binary
  using (DecidableEquality)

module Clock.Matrix (Pid : Type) (_≟_ : DecidableEquality Pid) where
  open import Data.Product
    using (_×_)
  open import Data.Product.Properties
    using (≡-dec)
  open import Data.Nat
    using (ℕ; _≤_)

  -- A Raynal-Schiper-Toueg matrix clock classifies actions by a tuple
  -- of sender and recipient. This forms a table of quantities, one for
  -- each sender-recipient pair.
  --
  -- This is *distinct* from a Wuu-Bernstein matrix clock, which has an extra
  -- step in its merge operation to propagate knowledge of observation.
  module RST where
    open import Clock.Classifier (Pid × Pid) (≡-dec _≟_ _≟_) public
      using (Time; _⊑_; alg; clock; timestamp; mono)

  -- A Wuu-Bernstein matrix clock classifies actions by actor and observer.
  -- If an action is observed by multiple actors, the action will be counted
  -- in multiple places in the matrix. This requires not only a pointwise merge,
  -- but also a merge of a sender's row into a receiver's row, to model that
  -- the receiver now observes anything that the sender observed at the time
  -- the message was sent.
  module WB (sum : (Pid → ℕ) → ℕ) (sum-pf : (t : Pid → ℕ) → (i : Pid) → t i ≤ sum t) where
    open import Function
      using (_∘_)
    open import Data.Unit
      using (⊤)
    open import Data.Product
      using (_,_)
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
      using (Step; start; act; merge)
      using (Clock)
    open Clock
      using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

    Time = (Pid × Pid) → ℕ

    _⊑_ : Time → Time → Type
    t₁ ⊑ t₂ = ∀ c → t₁ c ≤ t₂ c

    propagate-to : Pid → Time → Time
    propagate-to self t = λ (i , j) →
      if does (j ≟ self)
        then sum (t ∘ (i ,_))
        else (t ∘ (i ,_)) j

    alg : Step Pid Time → Time
    alg start = λ (_ , _) → 0
    alg (act self t) =
      let t' = propagate-to self t
      in λ c →
        if does ((≡-dec _≟_ _≟_) c (self , self))
          then 1 + t' c
          else 0 + t' c
    alg (merge t₁ t₂) = λ c →
      t₁ c ⊔ t₂ c


    propagate-to-mono : ∀ p t → (∀ c → t c ≤ propagate-to p t c)
    propagate-to-mono self t (i , j) with j ≟ self
    ... | false because _ = ℕ-Prop.≤-refl
    ... | true  because _ = sum-pf (t ∘ (i ,_)) j

    clock : Clock alg _⊑_
    ≤-refl clock _ _ = ℕ-Prop.≤-refl
    ≤-trans clock _ _ _ t₁≤t₂ t₂≤t₃ = λ s → ℕ-Prop.≤-trans (t₁≤t₂ s) (t₂≤t₃ s)
    act-mono clock self t c with (≡-dec _≟_ _≟_) c (self , self)
    ... | false because _ = propagate-to-mono self t c
    ... | true  because _ = ℕ-Prop.m≤n⇒m≤1+n (propagate-to-mono self t c)
    merge-mono¹ clock t₁ t₂ (i , j) = ℕ-Prop.m≤m⊔n _ _
    merge-mono² clock t₁ t₂ (i , j) = ℕ-Prop.m≤n⊔m _ _

    -- Obtain a global timestamping function for any execution.
    timestamp = Interpret.timestamp clock
    -- Obtain a proof of the clock condition for any execution and any initial timestamps.
    mono = Interpret.timestamp-mono clock
