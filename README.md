# Weak Memory Rely/Guarantee Logic

This project contains the Isabelle/HOL formalisation and soundness proof for a rely/guarantee logic tailored to weak memory
models based on a notion of interfering local operation pairs.

## Layout
- Semantics.thy: Weak memory small step semantics, based on Rob's reordering + forwarding
- Execution.thy: Couple semantics with evaluation of instructions and arbitrary environment steps
- Interference.thy: Abstract definition the thread-local interference analysis
- Local_Rules.thy: Thread-local rely/guarantee reasoning
- Global_Rules.thy: Parallel composition of thread-local reasoning
- Soundness.thy: Definition and proof of soundness

## TODO
- [x] Specialise semantics for ARMv8
- [ ] Finish verification of executable interference analysis
- [ ] Add WP + verify some examples using Nieto's automation
- [ ] State dependent reordering
- [ ] NMCA semantics + interference analysis
- [ ] Explore moving interference to sequential composition
- [ ] Explore completeness issues
