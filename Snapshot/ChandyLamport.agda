{-# OPTIONS --safe --without-K --exact-split --no-import-sorts #-}
open import Agda.Primitive
  using () renaming (Set to Type)

{-
# META

* ~~Next time: Read one or more of the papers (chandy-lamport and/or
  Dijkstra note).~~
* Next-next time: Poke at the elements of an implementation and/or
  proof.

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
open import Data.Vec using (Vec; map)
open import Data.Bool using (Bool)
open import Data.List using (List; mapMaybe)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe; just; nothing)

import Execution.Core

-- | State at each node and in the network.
-- * Per node.
-- * Per channel.
-- * Fully connected. TODO: Not connected.
record Conf (S M : Type) (n : ℕ) : Type where
  constructor conf
  field nodes : Vec S n
  field chans : Vec (Vec (List M) n) n

data CLS (S M : Type) (n : ℕ) : Type where
  live : S → CLS S M n
  snap : S → (S × Vec (Bool × List M) n) → CLS S M n
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

ConfRel : Type → Type → ℕ → Type₁
ConfRel S M n = (_ _ : Conf S M n) → Type

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
  lift : ∀ Γ Γ' → (Conf-proj Γ ⇒ Conf-proj Γ') → CL S M n _⇒_ Γ Γ'
