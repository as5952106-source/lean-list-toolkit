# Design and guarantees

`reverseOnto` implements accumulator-based reversal. The specification theorem
quantifies over every list and every suffix, so preservation of an existing
suffix is checked as well as ordinary reversal. Corollaries establish length
preservation and involution. `map` has an extensional specification, a length
proof, and a compatibility theorem for reversal.

Definitions are total and polymorphic. Tests exercise empty input, nonempty
input, suffix handling, and theorem usage. These are mathematical correctness
claims, not performance benchmarks or stack-size guarantees.
