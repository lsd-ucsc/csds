{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

{-
# META

* [x] Next time: Read one or more of the papers (chandy-lamport and/or
  Dijkstra note).
* [x] Next-next time: Poke at the elements of an implementation and/or
  proof.
* [ ] Figure out how to handle red-letter messages (tie up loose ends).
  * [ ] JMC: We may want to switch from a functional repr to a relational repr
        for local transitions (Reaction). B/C relational defns are easier to
        use for reasoning.
* [ ] Change the boolean in Recordings to an ADT.

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
open import Data.Vec using (Vec; []; _∷_; map; replicate)
open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_; mapMaybe) renaming (map to mapl)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; zero; suc)

import Execution.Core

-- | State at each node and in the network.
-- * Per node.
-- * Per channel.
-- * Fully connected. TODO: Not connected.
record Conf (S M : Type) (n : ℕ) : Type where
  constructor conf
  field nodes : Vec S n
  field chans : Vec (Vec (List M) n) n

Recordings : Type → ℕ → Type
Recordings M n = Vec (Bool × List M) n

data CLS (S M : Type) (n : ℕ) : Type where
  live : S → CLS S M n
  snap : S → S × Recordings M n → CLS S M n
--done : S → (S × Vec (List M) n) → CLS S M n

CLS-proj : ∀ {S M n} → CLS S M n → S
CLS-proj (live s) = s
CLS-proj (snap s _) = s

-- | Either an underlying message, or a red-letter-message.
data CLM (M : Type) : Type where
  msg : M → CLM M
  red : CLM M

CLM-proj : ∀ {M} → CLM M → Maybe M
CLM-proj (msg m) = just m
CLM-proj red = nothing

-- CLC : Type → Type → ℕ → Type
-- CLC S M n = Conf (CLS S M n) (CLM M) n

Conf-proj : ∀ {S M n} → Conf (CLS S M n) (CLM M) n → Conf S M n
Conf.nodes (Conf-proj (conf nodes _)) = map CLS-proj nodes 
Conf.chans (Conf-proj (conf _ chans)) = map (map (mapMaybe CLM-proj)) chans

-- | Given a state and a message produce a new state and vector of
-- outgoing messages on each channel.
Reaction : Type → Type → ℕ → Type
Reaction S M n = S → M → Fin n → S × Vec (List M) n

ConfRel : Type → Type → ℕ → Type₁
ConfRel S M n = (_ _ : Conf S M n) → Type

Deliverable : ∀ {S M n} → M → Conf S M n → Type
Deliverable = _

deliver : ∀ {S M n} {m : M} {Γ : Conf S M n} → Reaction S M n → Deliverable m Γ → Conf S M n
deliver = _

data App (S M : Type) (n : ℕ) (a : Reaction S M n) : ConfRel S M n where
  drive : (m : M) → (Γ : Conf S M n) → (d : Deliverable m Γ)
        → App S M n a Γ (deliver {_} {_} {_} {m} {Γ} a d)

-- | response messages for initial snapshot: no red message at the
-- specified index and red messages eslewhere
init-reds : ∀ {M n} → Fin n → Vec (List (CLM M)) n
init-reds zero = [] ∷ replicate _ (red ∷ [])
init-reds (suc i) = (red ∷ []) ∷ init-reds i 

stop-recording : ∀ {n} {M : Type} → Fin n → Recordings M n → Recordings M n
stop-recording zero ((done-rec , rec) ∷ xs) = (true , rec) ∷ xs 
stop-recording (suc i) (x ∷ xs) = x ∷ stop-recording i xs

lift : ∀ {S M n} → Reaction S M n → Reaction (CLS S M n) (CLM M) n
lift a (live st) (msg m) src =
  -- in which we drive the underlying app with a message and wrap its output
  let st' , ms = a st m src in
  ( live st' 
  , map (mapl msg) ms
  )
lift a (snap st (st₀ , recs)) (msg m) src =
  -- in which we drive the underlying app as above, but also record the message
  let st' , ms = a st m src in
  ( snap st' (st₀ , {!!})
  , map (mapl msg) ms
  )
lift a (live st) red src =
  -- in which we start a snapshot for everything but the channel from which we rec'd red
  ( snap st (st , stop-recording src (replicate _ (false , [])))
  , init-reds src
  )
lift a (snap st (st₀ , recs)) red src =
  -- in which we stop recording a channel
  ( snap st (st₀ , stop-recording src recs)
  , replicate _ []
  )

-- | Relational model of transitions in a chandy lamport execution.
--
-- PLR explaining what JMC said: This is subtly wrong because CLM-proj
-- drops red-letter-messages, meaning that our use of Conf-proj in
-- CL.lift allows system transitions "under" red-letter-messages that
-- are next in line to be received.
--
-- JMC: This is fundamentally wrong because *both* levels of the
-- relation must handle delivered messages.
--
-- JMC: deliver-red, deliver-msg
--
-- PLR: i.e. Only our transitions lead to deliveries in the underlying transition.
--
-- JMC: Should all transitions be delivery transitions? I think
-- so. "Here, take a message, produce a bunch more messages, and
-- change your state." Everything is just that.
data CL (S M : Type) (n : ℕ) (_⇒_ : ConfRel S M n) : ConfRel (CLS S M n) (CLM M) n where
  -- possible transitions
--lift : ∀ Γ Γ' → (Conf-proj Γ ⇒ Conf-proj Γ') → CL S M n _⇒_ Γ Γ'
