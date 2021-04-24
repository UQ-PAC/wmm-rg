# Weak Memory Rely/Guarantee Logic

This project contains the Isabelle/HOL formalisation and soundness proof for a rely/guarantee logic tailored to weak memory
models based on a notion of interfering local operation pairs.

## Layout
- State.thy
- Syntax.thy
- Atomics.thy
- Reordering.thy
- Semantics.thy: Weak memory small step semantics, based on Rob's reordering + forwarding
- Interference.thy: Abstract definition the thread-local interference analysis
- Rules.thy: Thread-local rely/guarantee reasoning
- Transition_Rules.thy
- Soundness.thy: Definition and proof of soundness
- SimAsm 
