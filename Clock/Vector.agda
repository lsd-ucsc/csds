{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)
open import Relation.Binary
  using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

module Clock.Vector (Pid : Type) (_≟_ : DecidableEquality Pid) where
  -- A Raynal-Singhal vector clock classifies actions by "who" performed the action.
  -- This forms a vector of quantities, one for each actor.
  open import Clock.Classifier Pid _≟_ public
    using (Time; _⊑_; alg; clock; timestamp; mono)
  -- (This framing shows that *all* indexed clocks are morally the vector clock.)
