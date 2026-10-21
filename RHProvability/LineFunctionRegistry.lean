/-
# Registry successor for Gap 1 — **RETRACTED** (2026-10-19, after the upstream check)

## ⚠ Why the entry below must not be registered

`OpenSignChangingLineFunction` is **too strong**. Requiring a sign change across every zero forces
every critical-line zero of `ζ` to have **odd multiplicity**, i.e. it implies zero **simplicity** —
a famous open problem that is **not** implied by RH. A real function's zero of even multiplicity
does not change sign, so the sign clause is not a harmless sharpening; it smuggles in a conjecture.

## What the correct object is (upstream, verified at source)

Upstream Mathlib **master** already carries it:
`Mathlib/NumberTheory/LSeries/HardyZ.lean` (PR #42963, opened 2026-08-19, merged via bors):

```text
noncomputable def hardyZ (t : ℝ) : ℝ
theorem abs_hardyZ (t) : |hardyZ t| = ‖riemannZeta (1/2 + t*I)‖
theorem hardyZ_eq_zero_iff (t) : hardyZ t = 0 ↔ riemannZeta (1/2 + t*I) = 0
theorem continuous_hardyZ : Continuous hardyZ
theorem ofReal_hardyZ (t) : (hardyZ t : ℂ)
    = completedRiemannZeta (1/2 + t*I) / ‖Gammaℝ (1/2 + t*I)‖
```

Its docstring claims only that **sign changes of `Z` locate zeros** — deliberately not the converse,
exactly because the converse needs simplicity.

So the registered Gap 1 (`Overview.lean:339`) needs **wiring to `hardyZ`**, not tightening: once
Mathlib is bumped past the `v4.33.0` pin (where `hardyZ` has 0 hits), the registration follows in
three lines from `hardyZ`, `continuous_hardyZ`, `hardyZ_eq_zero_iff` — and the witness is then the
standard object rather than `infDist`, which carries no information.

`Mathlib/NumberTheory/LSeries/ZetaZeros.lean` additionally provides `riemannZetaZeros`,
`isClosed_riemannZetaZeros`, `isDiscrete_riemannZetaZeros`,
`IsCompact.inter_riemannZetaZeros_finite`, `tendsto_riemannZeta_cofinite_cocompact`, which bear
directly on the Backlund / counting route.

## Status of this file

Kept as the record of the mistake, **not** as a proposed registration. The implication proved at the
bottom is true, but its premise is not something we want to assume.

The original (also withdrawn) framing was: `LineFunction.lean` proves the loose registration with a
non-negative `Z` (distance to the closed zero set), which can never witness a sign change, while the
registration's comment says the object exists to make "sign-change counting" meaningful. That part of
the diagnosis stands; only the proposed replacement was wrong.
-/
import RHProvability.LineFunction

namespace RHProvability.Overview

open Metric

/-- **Withdrawn entry.** A real-valued continuous function whose zeros are exactly the critical-line
zeros of `ζ`, **and which changes sign across each of them.**

⚠ **Do not register this.** The sign clause implies that every critical-line zero of `ζ` has odd
multiplicity (zero simplicity), which is open and not implied by RH. See the file header. -/
def OpenSignChangingLineFunction : Prop :=
  ∃ Z : ℝ → ℝ, Continuous Z ∧
    (∀ t : ℝ, (Z t = 0 ↔ riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0)) ∧
      ∀ t : ℝ, Z t = 0 →
        ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, t - ε < a → a < t → t < b → b < t + ε → Z a * Z b < 0

/-- The withdrawn entry implies the original one. True — and it is what identifies the withdrawal as
a *strengthening*: the sign clause is additional content, and that content costs a conjecture. -/
theorem openSignChanging_implies_openRealValuedLineFunction
    (h : OpenSignChangingLineFunction) : OpenRealValuedLineFunction := by
  obtain ⟨Z, hZ, hiff, -⟩ := h
  exact ⟨Z, hZ, hiff⟩

end RHProvability.Overview
