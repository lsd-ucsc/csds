{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

{-
# META

* [x] Next time: Read one or more of the papers (chandy-lamport and/or
  Dijkstra note).
* [x] Next-next time: Poke at the elements of an implementation and/or
  proof.
* [x] Figure out how to handle red-letter messages (tie up loose ends).
  * [ ] JMC: We may want to switch from a functional repr to a relational repr
        for local transitions (Reaction). B/C relational defns are easier to
        use for reasoning.

# Chandy Lamport algorithm

* Capture a snapshot of node state and inflight messages along some
  consistent cut.

* What is the algorithm?
  * One process arbitrarily "behaves as though it received a red letter".
    * On receipt of your first red letter, record your state, start
      recording the stream of messages from each buffer, and then send
      red letters to all the other processes.
    * On subsequent receipt of red letters, stop recording the
      messages from that buffer.
  * The now distributed snapshot of states and buffers can be examined
    to detect a stable (invariant going forward) property. Somenode
    either has to collect them, or otherwise, examine each of them.
  * No consensus required to choose the initiator of the snapshot, nor
    to choose an identifier for the snapshot itself.

* What is the property we want to verify?
  * Running the algorithm on some initial state, yields a CSD where
    one of the nodes has a snapshot (a piece of state at that node)
    that reflects the state at some consistent cut in the CSD.
  * Need to be able to describe all consistent cuts of a CSD possible,
    beyond those concretized by its current spine.
    * Need a set of "equivalance preserving" rules that can mutate a CSD.
    * A consistent cut of a CSD is a triple of a CSD', a proof
      CSD≡CSD', and a time index into CSD'.
    * "Every consistent cut of a CSD may be found in the spine of some
      equivalent CSD." -JMC

* Discussion of the alogrithm:
  * The algorithm evolves a bit like a series of almost-spanning trees
    expanding to cover the network.
  * JMC: I had a eureka moment, sort of. It's analogous to nodes
    having two copies of state, one of which they stop updating upon
    receipt of a red letter.
  * PLR: What is the property? JMC: The algorithm identifies a
    consistent cut.

-}
module Snapshot.ChandyLamport where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; lookup; replicate; _[_]≔_; _[_]%=_; zipWith) renaming (map to mapv)
open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_; _∷ʳ_; mapMaybe; _++_) renaming (map to mapl)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Execution.Core

-- | State at each node and in the network.
-- * Per node.
-- * Per channel.
-- * Fully connected. TODO: Not connected.
-- * `chans` vec index is sender then receiver.
record Conf (S M : Type) (n : ℕ) : Type where
  constructor conf
  field nodes : Vec S n
  field chans : Vec (Vec (List M) n) n

-- | Given a state, a message, and a sender, produce a new state and
-- vector of outgoing messages on each channel.
Reaction : Type → Type → Type → ℕ → Type
Reaction Stim S M n = Stim → S → S × Vec (List M) n

ConfRel : Type → Type → ℕ → Type₁
ConfRel S M n = (_ _ : Conf S M n) → Type

-- | There exists a sender and receiver and some messages such that
-- looking up the chan s→r finds a queue with m at the right.
Deliverable : ∀ {S M n} → M → Conf S M n → Type
Deliverable m (conf nodes chans) =
    ∃[ s ] ∃[ r ] ∃[ ms ] lookup (lookup chans s) r ≡ ms ∷ʳ m

-- | Selectively update the recipient's (of a deliverable message)
-- state and outbound messages by running its reaction function.
deliver : ∀ {S M n} {m : M} {Γ : Conf S M n} → Reaction (M × Fin n) S M n → Deliverable m Γ → Conf S M n
deliver {m = m} {Γ = conf nodes chans} a (s , r , ms , eq) =
  let (r' , out) = a (m , s) (lookup nodes r) in
  let nodes' = nodes  [ r ]≔ r' in
  let chans₁ = chans  [ s ]%= (_[ r ]≔ ms) in -- remove m from s→r
  let chans₂ = chans₁ [ r ]%= zipWith _++_ out in -- add new messages to r→*
  conf nodes' chans₂

data App (S M : Type) (n : ℕ) (a : Reaction (M × Fin n) S M n) : ConfRel S M n where
  delivered : (m : M) → (Γ : Conf S M n) → (d : Deliverable m Γ)
        → App S M n a Γ (deliver {_} {_} {_} {m} {Γ} a d)



-- * Chandy Lamport bits

data RecordingStatus : Type where
  active : RecordingStatus
  inactive : RecordingStatus

-- | Vec index is sender.
Recordings : Type → ℕ → Type
Recordings M n = Vec (RecordingStatus × List M) n

data CLS (S M : Type) (n : ℕ) : Type where
  live : S → CLS S M n
  snap : S → S × Recordings M n → CLS S M n

-- | Either an underlying message, or a red-letter-message.
data CLM (M : Type) : Type where
  msg : M → CLM M
  red : CLM M

stop-recording : ∀ {n} {M : Type} → Fin n → Recordings M n → Recordings M n
stop-recording zero ((status , rec) ∷ xs) = (inactive , rec) ∷ xs 
stop-recording (suc i) (x ∷ xs) = x ∷ stop-recording i xs

enqueue-message : ∀ {n M} → Fin n → M → Recordings M n → Recordings M n
enqueue-message zero m ((status , rec) ∷ xs) = (status , rec ∷ʳ m ) ∷ xs
enqueue-message (suc src) m (x ∷ xs) = x ∷ enqueue-message src m xs

-- | Lift underlying app reactions to CL-extended reactions.
lift : ∀ {S M n} → Reaction     (M × Fin n)      S           M  n
                 → Reaction (CLM M × Fin n) (CLS S M n) (CLM M) n
lift a (msg m , src) (live st) =
  -- in which we drive the underlying app with a message and wrap its output
  let st' , ms = a (m , src) st in
  ( live st' 
  , mapv (mapl msg) ms
  )
lift a (msg m , src) (snap st (st₀ , recs)) =
  -- in which we drive the underlying app as above, but also record the message
  let st' , ms = a (m , src) st in
  ( snap st' (st₀ , enqueue-message src m recs)
  , mapv (mapl msg) ms
  )
lift a (red , src) (live st) =
  -- in which we start a snapshot for everything but the channel from which we recv'd red
  ( snap st (st , stop-recording src (replicate _ (active , [])))
  , replicate _ (red ∷ [])
  )
lift a (red , src) (snap st (st₀ , recs)) =
  -- in which we stop recording a channel
  ( snap st (st₀ , stop-recording src recs)
  , replicate _ []
  )
