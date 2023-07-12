{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

module Clock.Scalar where
  open import Data.Unit
    using (⊤; _≟_)

  -- A Lamport scalar clock classifies all actions into one undistinguished class.
  -- This yields a clock whose timestamps are single numbers, tracking a lower bound
  -- on the total number of actions overall.
  open import Clock.Classifier ⊤ _≟_ public
    using (Time; _⊑_; alg; clock; timestamp; mono)
