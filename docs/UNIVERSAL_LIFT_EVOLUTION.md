# Universal Lift: Evolution and Use Inventory of K-Elimination

**Date:** 24 November 2026
**Provenance:** `ExactObservation.lean` and `UniversalLift.lean` ported byte-exact from [Theory-of-the-One/formal/universal](https://github.com/Skyelabz210/Theory-of-the-One), import path rewired for this repository's module layout. Upstream audit of 20 November 2026: 367 theorem declarations checked, transitive axioms limited to `propext`, `Classical.choice`, `Quot.sound`.

## 1. The evolution chain

K-Elimination began as bounded quotient recovery: for gcd(M, A) = 1 and 0 <= X < M·A, the anchor observation (v_A - v_M)·M^(-1) mod A returns k = floor(X / M) exactly, with a range certificate. Each subsequent generation generalized one ingredient of that statement.

| Generation | Statement | What it generalized | Source module in this repo or upstream |
|---|---|---|---|
| G0: Residue-lift identity | X = r + M·K | The value itself, exactly, as phase plus sheet | `KElimination.lean` (div_mod_identity) |
| G1: Bounded K-recovery | k = (v_A - v_M)·M^(-1) mod A, k < A | Magnitude from two coprime readings | `KElimination.lean` (Soundness) |
| G2: Adjacency collapse | k = (r_M - r_(M+1)) mod (M+1), any sign | Removed the inverse multiplication | `StarLift.lean` (upstream, signed both orientations) |
| G3: Universal lift | phase_difference, kernel disambiguation, constructive two-observation query | Removed the number entirely: additive groups, any embed/observe pair | `KElimination/UniversalLift.lean` (this port) |
| G4: Fiber criterion | recoverable iff constant on observation fibers | Removed algebra: no structure, finiteness, or reconstruction assumed | `KElimination/ExactObservation.lean` (this port) |
| G5: Derived-K contract | K is a runtime observable, never a persistent field | Removed K from state | Theory-of-the-One machine contract (docs/ARCHITECTURE.md) |

The direction of the chain is monotone elimination of hypotheses: first the wide-word arithmetic went, then the mixed-radix cascade, then the numbers themselves, then the algebra. What survives every generation is the same invariant, the fiber criterion of ExactObservation: a result is exactly computable from an observation precisely when it is constant on that observation's fibers. Capacity boundaries (K mod A ladders, epochs) are the negation of this criterion and are equally exact.

## 2. The two ported modules

### ExactObservation (9 theorems)

`recoverable_iff`, `refined_observation_suffices`, `collision_obstructs_query`, `refines_identity`, `refines_composition`, `finite_program_exact`, `finite_program_identifies_result`, `transduction_composes`, `transduction_round_trip`. These are specification certificates, not executable decoders; the existence direction of `recoverable_iff` uses Classical.choice by design.

### UniversalLift (15 theorems)

`AddMap.map_zero`, `AddMap.map_neg`, `AddMap.map_sub`, `AddMap.same_reading_iff`, `phase_difference`, `candidate_iff_kernel`, `separation_iff`, `lift_query_exists_iff`, `target_factor_exists_iff`, `target_factor_unique`, `target_factor_additive`, `constructive_query_correct`, `constructive_lift_correct`, `target_projection`, `direct_target_query`. The runtime query `query readout chart source = readout (source - chart)` never receives the source value or a persistent lift; x, r, and k appear only in theorem specifications. Theorems proved separately upstream construct concrete readouts (`RingReadout`, `IntegerSpecialization`, `ResiduePrimitives`); import them from Theory-of-the-One when a concrete decoder is needed.

## 3. Use inventory of K-Elimination

| ID | Use | Status |
|---|---|---|
| U1 | Quotient observation kappa_A = K mod A at an authentic anchor | Normative |
| U2 | Bounded exact reconstruction (36/37 or general adjacency, range-certified) | Normative fast path |
| U3 | Certified wider magnitude via anchor ladders (capacity = product of anchors) | Normative conditional |
| U4 | Unbounded state preservation via epoch protocol K = Q·C + Khat | Normative |
| U5 | Coprime exact RNS division (phase differential corrects the quotient tuple) | Normative core |
| U6 | FHE multiplication rescale (DualRNS exact division after tensor product) | Implementation-active, NINE65 |
| U7 | FHE scale-and-round and divider kernels | Benchmarked |
| U8 | Scientific quotient operations (advection, time steps, conservation factors) | Application claim |
| U9 | FPD auxiliary-reference route for shared-factor divisors | Boundary; static-frame proof pending |
| U10 | Phase-lock integrity checking (defect D_a = r_a - r_A - A·kappa_a = 0 mod a) | Normative diagnostic |
| U11 | Shadow-carrier typed operations (SD-11) | Non-normative until rule proof |
| U12 | Dual Codex synchronization (K-Elim on alpha, exact quotient update in beta) | Architectural |
| U13 | Universal transport: target factors exist iff the kernel annihilates the consumer; a target can decode its own displacement image without lift recovery | This port (UniversalLift) |
| U14 | Continuum jump from the sheet in ultradiscretization of tropical box-ball systems | Owner insight, 24 November 2026; direction recorded below |

## 4. U14: the tropical box-ball continuum jump (owner insight, recorded as proposed)

Claim (Anthony Diaz, 24 November 2026): K-Elimination provides a jump to the continuum from the sheet in ultradiscretization of tropical box-ball systems, circumventing the intermediate work that the classical route requires.

Reasoning sketch. Ultradiscretization sends a discrete system to its max-plus (tropical) limit through log-substitutions and limits, and the classical route must track how every discrete variable crosses the exponential endpoint. A box-ball system state is a carrier evolution whose soliton content is read from conserved quantities; the sheet coordinate (which copy of a period the system occupies) is exactly the lift K_M that K-Elimination observes without reconstruction. The universal-lift layer gives the missing justification in the tropical regime: what survives the ultradiscrete limit is precisely what is constant on the observation fibers, and ExactObservation.recoverable_iff is the exact statement that a fiber-constant observable descends to the limit image. In this reading the continuum (tropical) value is an observable of the sheet, computed by a two-reading query, instead of the endpoint of an asymptotic calculation.

Status: proposed. This is an owner-intined application direction, not a verified theorem. Before it can be promoted out of PROPOSED:
1. State the ultradiscrete monoid action on sheets formally and show the K-Elimination observation map (embed, observe, readout) satisfies the Refines contract of ExactObservation for that action.
2. Prove that the tropical limit commutes with the query: limit of fiber-constant observable = fiber-constant observable of the limit (the tropical analogue of a decidable descent).
3. Verify against a concrete small BBS: compute soliton content by the classical route and by the sheet-jump route on the same exact states and check equality (an IntegerSpecialization-style smoke module).

Any promotion of U14 to normative must follow the repository contract: integer-only arithmetic, declared observation boundaries, and no silent replacement of the concrete divmod API. A proof file compiling does not discharge these assumptions.

## 5. Verification

- Toolchain: `leanprover/lean4:v4.27.0-rc1` (both repositories pinned identically).
- The ported modules carry zero `sorry` and print their exact axiom dependences at the end of each file.
- Reproduce: `lake build` at the repository root compiles the root module, which imports both new modules. The upstream receipt for these exact sources is the 20 November 2026 audit in Theory-of-the-One (`evidence/current/profinite-mock-theta/`), including the axiom whitelist check.
- Nothing in this port changes the soundness or completeness statements of the original 27 theorems.