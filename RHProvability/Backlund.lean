/-
# The Backlund route: what Mathlib already has, and the first comparison theorem

`StripCount.lean` defines `stripCount T` with **no upper bound of any kind**. Backlund's theorem
(`N(T) = (T/2π)·log(T/2π) − T/2π + O(log T)`) is the missing analytic content. This file does two
things:

1. **A first comparison theorem** that connects our strip count to the disk count
   (`zeroCount` from `Counting.lean`), so that any disk-count bound transfers:
   `stripCount T ≤ zeroCount (1 + |T|)`.
2. **The register** `BacklundBound`, the exact statement we would need to build a certified counting
   check, together with its immediate use.

## What this does *not* do

No growth estimate for `stripCount` is proved. `BacklundBound` is a `Prop` with no proof; the analytic
work (Jensen/argument principle + explicit estimates for `ζ` and `Γ`) is not in this development.

**But see the registry note on `BacklundBound` below:** proving it would be filling a *library* hole,
not advancing towards RH. As a statement it is unconditional classical mathematics; it holds whether
or not RH does, and it gives only upper bounds on the two counts, while RH needs their equality.

## Inventory of what Mathlib *does* provide (checked 2026-10-18, file:line)

* `Mathlib/Analysis/Complex/JensenFormula.lean:209` —
  `circleAverage_re_herglotzRieszKernel_mul_log`: the Jensen kernel representation of
  `log ‖f‖` on a circle, i.e. the analytic engine behind Jensen's formula.
* `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean` —
  Nevanlinna counting: `logCounting` (`:274` for `ℝ → ℝ`), `toClosedBall` (`:57`),
  `toClosedBall_divisor` (`:72`, restricting the **divisor of a meromorphic function** to a ball).
  So Mathlib *does* have zeros counted **with multiplicity** (`divisor`), which our `stripCount`
  does not use.
* **Not present**: a formal "argument principle" (no `argument_principle`-named result), so the
  contour form used in Backlund's proof must be assembled from the Jensen kernel.

Consequence for the plan: the route is not "invent Jensen" (it exists) but
**(a)** convert box counts to disk counts *with multiplicity* and back,
**(b)** estimate `log ‖ζ‖` on the relevant circles — this is where Stirling for `Γ` and the
convexity bound for `ζ` are needed, and **that** is the real project.
-/
import RHProvability.LineCountClosed

namespace RHProvability

open Complex

/-! ## The register -/

/-- **Backlund's bound as a target.** There are constants `C > 0` and `T₀` with
`N_strip(T) ≤ C · T · log T` for all `T ≥ T₀`.

This is a `Prop` with **no proof** in this development. Note it is stated for our `stripCount`
(distinct zeros, closed box); the classical `N(T)` counts zeros with multiplicity, so a faithful
formalization would also need the multiplicity-aware count (see the header).

**Registry note (2026-10-18, iteration 12): this is a *library* gap, not an RH gap.**

As a mathematical statement, `∃ C > 0, ∃ T₀, ∀ T ≥ T₀, stripCount T ≤ C·T·log T` is a theorem of the
classical theory (the Riemann–von Mangoldt count is unconditional), so it holds with or without RH.
What is missing is *our* formalization of that count, not a step towards RH.

Its shape is also information-free: `TailShape.backlundShape_blind` exhibits a function satisfying it
identically zero, and `TailShape.backlund_gives_upper_bounds_only` records that it yields only *upper*
bounds, whereas the count-equality route needs `lineCount = stripCount`, which is RH-equivalent
(`countsEq_iff_riemannHypothesis`). So a proof of `BacklundBound` would fill a library hole and buy
**zero** progress towards RH. Do not count it as an advance. -/
def BacklundBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (stripCount T : ℝ) ≤ C * T * Real.log T

/-! ## The first comparison theorem -/

/-- The strip box at height `T` sits inside the closed disk of radius `1 + |T|`: for `z` in the box,
`|Re z| ≤ 1` and `|Im z| ≤ T ≤ |T|`. -/
theorem zerosInStripBox_subset_zerosInBall (T : ℝ) :
    zerosInStripBox T ⊆ zerosInBall (1 + |T|) := by
  rintro z ⟨hz, hbox⟩
  obtain ⟨him, h0, h1⟩ := hbox
  refine ⟨hz, ?_⟩
  have hre : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, h1⟩
  have him' : |z.im| ≤ |T| := le_trans him (le_abs_self T)
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  linarith

/-- **`N_strip(T) ≤ N_disk(1 + |T|)`.** The two counting functions of the development are comparable,
so any upper bound for the disk count transfers to the strip count. -/
theorem stripCount_le_zeroCount (T : ℝ) : stripCount T ≤ zeroCount (1 + |T|) := by
  unfold stripCount zeroCount
  exact Set.ncard_le_ncard (zerosInStripBox_subset_zerosInBall T) (finite_zerosInBall _)

/-- The same comparison with an arbitrary radius above `1 + |T|`, using monotonicity of `zeroCount`. -/
theorem stripCount_le_zeroCount_of {T R : ℝ} (hR : 1 + |T| ≤ R) :
    stripCount T ≤ zeroCount R :=
  le_trans (stripCount_le_zeroCount T) (zeroCount_mono hR)

/-! ## Two consequences that do compile -/

/-- For negative `T` the strip box is empty, so the count is `0`. This is the only place in the
development where `stripCount` is actually *evaluated*. -/
theorem stripCount_of_neg {T : ℝ} (hT : T < 0) : stripCount T = 0 := by
  have hempty : zerosInStripBox T = ∅ := by
    ext z
    refine ⟨?_, fun h => absurd h (by simp)⟩
    rintro ⟨-, hbox⟩
    have him : |z.im| ≤ T := hbox.1
    have h0 : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  unfold stripCount
  rw [hempty]
  simp

/-- **A bound for the line count follows from Backlund's bound**, since `N_line ≤ N_strip`.
So the registered `BacklundBound` would immediately bound both counting functions. -/
theorem lineCount_le_of_backlund (h : BacklundBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (lineCount T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀⟩ := h
  refine ⟨C, hC, T₀, fun T hT => ?_⟩
  have h1 : (lineCount T : ℝ) ≤ (stripCount T : ℝ) := by exact_mod_cast lineCount_le_stripCount T
  exact le_trans h1 (hT₀ T hT)

end RHProvability
