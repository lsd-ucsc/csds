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

import Execution.Core

-- ...
