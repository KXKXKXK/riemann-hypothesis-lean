/-
# Gap 1, wired to Mathlib's Hardy `Z` function (Mathlib ≥ v4.35.0)

`Overview.lean:339` registers

    def OpenRealValuedLineFunction : Prop :=
      ∃ Z : ℝ → ℝ, Continuous Z ∧ ∀ t, (Z t = 0 ↔ ζ (1/2 + i t) = 0)

`LineFunction.lean` proves it via the distance-to-a-closed-set trick, which works but produces a
**non-negative** witness carrying no information about sign changes.

Since **Mathlib v4.35.0** (Hardy `Z` merged 2026-10-10, PR #42963), the *standard* witness exists in
the library:

    hardyZ : ℝ → ℝ
    abs_hardyZ        : |hardyZ t| = ‖ζ (1/2 + t*I)‖
    hardyZ_eq_zero_iff: hardyZ t = 0 ↔ ζ (1/2 + t*I) = 0
    continuous_hardyZ : Continuous hardyZ

So the registration is literally three lines of wiring — this file is that wiring. It is **not** new
mathematics: it is the upstream object, and its docstring says only that *sign changes of `Z` locate
zeros*, deliberately not the converse (the converse needs zero simplicity, which is open).

This file supersedes the `infDist` witness of `LineFunction.lean` as the intended reading of Gap 1;
`LineFunction.lean` stays as the toolchain-independent proof (it needs nothing beyond v4.33.0).
-/
import RHProvability.Overview
import Mathlib.NumberTheory.LSeries.HardyZ

namespace RHProvability.Overview

/-- **Gap 1, witnessed by Hardy's `Z`.** Real-valued, continuous, with zeros exactly the
critical-line zeros of `ζ` — the object the registration actually has in mind. -/
theorem openRealValuedLineFunction_via_hardyZ : OpenRealValuedLineFunction := by
  refine ⟨hardyZ, continuous_hardyZ, fun t => ?_⟩
  -- `hardyZ_eq_zero_iff` writes `1/2` at type `ℂ`, while the registration writes
  -- `((1/2 : ℝ) : ℂ)`; the two are propositionally, not definitionally, equal.
  have hkey : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by norm_num
  rw [hkey]
  exact hardyZ_eq_zero_iff t

end RHProvability.Overview
