/-
# The Hardy-type zero engine: a sign change of `hardyZ` forces a zero of `ζ` on the line

`hardyZ` is Mathlib's real-valued Hardy `Z` function, with `|Z t| = ‖ζ (1/2 + i t)‖`
(`abs_hardyZ`) and zeros exactly at the critical-line zeros of `ζ` (`hardyZ_eq_zero_iff`), and it is
continuous (`continuous_hardyZ`).

This file records the elementary consequence that all Hardy-type arguments start from:

> if `hardyZ` takes opposite signs at two heights `a < b`, then `ζ` has a zero on the critical line
> with imaginary part strictly between `a` and `b`.

That is exactly the intermediate value theorem applied to `hardyZ`, transported across
`hardyZ_eq_zero_iff`.

## Honest status

This is **plumbing, not new mathematics**: the mathematical content is the intermediate value
theorem plus the fact that `Z` and `ζ` share their modulus. It is included because it is the engine
every quantitative statement about critical-line zeros plugs into, and because building it from
upstream `hardyZ` (rather than from scratch) is the point of the current toolchain.

What it explicitly does **not** give: *that* `hardyZ` changes sign anywhere. Hardy's theorem
(infinitely many zeros on the line) needs quantitative estimates on `Z` — which in turn need growth
estimates for `ζ` in the strip, absent from Mathlib as of v4.35 (see
`数学家-核验记录/RH-2026-10-19/05-Backlund工具可用性核查.md`). So this file moves the boundary
from "no engine" to "engine present, fuel missing".
-/
import RHProvability.HardyLineFunction

namespace RHProvability.Overview

open Set

/-- **A sign change of `hardyZ` yields a critical-line zero of `ζ` between the two heights.** -/
theorem exists_zetaZero_of_hardyZ_sign_change {a b : ℝ} (hab : a < b)
    (hsign : hardyZ a * hardyZ b < 0) :
    ∃ t : ℝ, t ∈ Ioo a b ∧
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  -- `hardyZ_eq_zero_iff` states the zero condition with `1/2` at type `ℂ`
  have hkey : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := fun t => by norm_num
  rcases mul_neg_iff.1 hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- `0 < hardyZ a`, `hardyZ b < 0`
    have h0 : (0 : ℝ) ∈ Icc (hardyZ b) (hardyZ a) := ⟨le_of_lt hb, le_of_lt ha⟩
    obtain ⟨t, ht, htz⟩ :=
      intermediate_value_Icc' hab.le (f := hardyZ) continuous_hardyZ.continuousOn h0
    have hta : t ≠ a := by
      intro h; rw [h] at htz; linarith
    have htb : t ≠ b := by
      intro h; rw [h] at htz; linarith
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩, ?_⟩
    rw [hkey t]
    exact (hardyZ_eq_zero_iff t).1 htz
  · -- `hardyZ a < 0`, `0 < hardyZ b`
    have h0 : (0 : ℝ) ∈ Icc (hardyZ a) (hardyZ b) := ⟨le_of_lt ha, le_of_lt hb⟩
    obtain ⟨t, ht, htz⟩ :=
      intermediate_value_Icc hab.le (f := hardyZ) continuous_hardyZ.continuousOn h0
    have hta : t ≠ a := by
      intro h; rw [h] at htz; linarith
    have htb : t ≠ b := by
      intro h; rw [h] at htz; linarith
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩, ?_⟩
    rw [hkey t]
    exact (hardyZ_eq_zero_iff t).1 htz

/-- The same statement landed in Mathlib's zero set `riemannZetaZeros`. -/
theorem exists_mem_riemannZetaZeros_of_hardyZ_sign_change {a b : ℝ} (hab : a < b)
    (hsign : hardyZ a * hardyZ b < 0) :
    ∃ t : ℝ, t ∈ Ioo a b ∧
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈ riemannZetaZeros := by
  obtain ⟨t, ht, hz⟩ := exists_zetaZero_of_hardyZ_sign_change hab hsign
  exact ⟨t, ht, mem_riemannZetaZeros.mpr hz⟩

end RHProvability.Overview
