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
  module WB where
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
      using (Step; act; merge)
    open import Clock.Monotonicity
      as Monotonicity
      using (Clock)
    open Clock
      using (≤-refl; ≤-trans; act-mono; merge-mono¹; merge-mono²)

    -- A local process ID, together with a timestamp.
    Time = Pid × ((Pid × Pid) → ℕ)

    -- Ignore the process ID when comparing.
    _⊑_ : Time → Time → Type
    (_ , t₁) ⊑ (_ , t₂) = ∀ c → t₁ c ≤ t₂ c

    alg : Step ⊤ Time → Time
    alg (act _ (self , t)) = self , λ c →
      if does ((≡-dec _≟_ _≟_) (self , self) c)
        then 1 + t c
        else 0 + t c
    alg (merge (s , t₁) (r , t₂)) = r ,  λ (i , j) →
      if does (j ≟ r)
        then t₁ (i , s) ⊔ (t₁ (i , j) ⊔ t₂ (i , j))
        else 0          ⊔ (t₁ (i , j) ⊔ t₂ (i , j))

    clock : Clock alg _⊑_
    ≤-refl clock _ _ = ℕ-Prop.≤-refl
    ≤-trans clock _ _ _ t₁≤t₂ t₂≤t₃ = λ s → ℕ-Prop.≤-trans (t₁≤t₂ s) (t₂≤t₃ s)
    act-mono clock _ (self , _) c with (≡-dec _≟_ _≟_) (self , self) c
    ... | false because _ = ℕ-Prop.≤-refl
    ... | true  because _ = ℕ-Prop.≤-step ℕ-Prop.≤-refl
    merge-mono¹ clock (s , t₁) (r , t₂) (i , j) with j ≟ r
    ... | false because _ = ℕ-Prop.m≤m⊔n _ _
    ... | true  because _ = ℕ-Prop.≤-trans (ℕ-Prop.m≤m⊔n _ _) (ℕ-Prop.m≤n⊔m (t₁ (i , s)) _)
    merge-mono² clock (s , t₁) (r , t₂) (i , j) with j ≟ r
    ... | false because _ = ℕ-Prop.m≤n⊔m _ _
    ... | true  because _ = ℕ-Prop.≤-trans (ℕ-Prop.m≤n⊔m _ _) (ℕ-Prop.m≤n⊔m (t₁ (i , s)) _)

    -- Obtain a global timestamping function for any execution.
    timestamp = Interpret.timestamp alg
    -- Obtain a proof of the clock condition for any execution and any initial timestamps.
    mono = Monotonicity.timestamp-mono clock
