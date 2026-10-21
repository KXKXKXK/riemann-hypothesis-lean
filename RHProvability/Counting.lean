/-
# A counting function for the zeros, and RH as finitely many `Finset`-quantified statements

Route A asks for a countable, computable description of the check. This file takes the next step
after `FiniteHeight.lean`: it turns "a statement about a finite set" into "a statement about the
*elements of an explicit `Finset`*", and defines the counting function

`zeroCount R = #{z : ζ z = 0 ∧ ‖z‖ ≤ R}`,

which is the object a Turing/Backlund-type counting bound would be about.

Proved here:

* `zeroCount_mono` — the count is monotone in the radius;
* `zeroCount_two_pos` — the count is nonzero already at `R = 2` (the trivial zero `-2`);
* `riemannHypothesis_iff_finset` — RH is equivalent to: for every radius `R`, every root in the
  *`Finset`* of zeros of radius `≤ R` that lies in the strip is on the critical line;
* `not_riemannHypothesis_iff_exists_in_finset` — `¬RH` is equivalent to: some radius `R` and some
  *element* of that `Finset` lies in the strip off the critical line.

What is **not** here: computability of `zeroCount` (it is a `noncomputable` cardinality of a set
defined by a `Prop`), and no bound on `zeroCount R` in terms of `R` — that bound is the analytic
content of Route A step 2 and is not formalized.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RHProvability.FiniteHeight

namespace RHProvability

open Complex
open scoped Real

/-- Number of zeros of `ζ` in the closed ball of radius `R`. -/
noncomputable def zeroCount (R : ℝ) : ℕ := (zerosInBall R).ncard

/-- The count is monotone in the radius. -/
theorem zeroCount_mono {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) : zeroCount R₁ ≤ zeroCount R₂ := by
  refine Set.ncard_le_ncard ?_ (finite_zerosInBall R₂)
  intro z hz
  exact ⟨hz.1, le_trans hz.2 h⟩

/-- The count is already nonzero at `R = 2`: `-2` is a trivial zero with `‖-2‖ = 2`. -/
theorem zeroCount_two_pos : 0 < zeroCount 2 := by
  have hmem : (-2 : ℂ) ∈ zerosInBall 2 := by
    refine ⟨?_, ?_⟩
    · have := riemannZeta_neg_two_mul_nat_add_one 0
      simpa using this
    · norm_num
  have hfin : (zerosInBall 2).Finite := finite_zerosInBall 2
  have hmem' : (-2 : ℂ) ∈ hfin.toFinset := by simpa using hmem
  have hcard : 0 < hfin.toFinset.card := Finset.card_pos.mpr ⟨_, hmem'⟩
  simpa [zeroCount, Set.ncard_eq_toFinset_card _ hfin] using hcard

/-- **RH as `Finset`-quantified statements.** For every radius, every root in the explicit finite
set of zeros of radius `≤ R` which lies in the critical strip is on the critical line. -/
theorem riemannHypothesis_iff_finset :
    RiemannHypothesis ↔
      ∀ (R : ℝ), ∀ z ∈ (finite_zerosInBall R).toFinset,
        0 < z.re → z.re < 1 → z.re = 1 / 2 := by
  rw [riemannHypothesis_iff_ball]
  constructor
  · intro h R z hz h0 h1
    have hz' : z ∈ zerosInBall R := by simpa using hz
    exact h R z hz'.2 hz'.1 h0 h1
  · intro h R z hzR hz h0 h1
    refine h R z ?_ h0 h1
    simp [zerosInBall, hzR, hz]

/-- **The negation, indexed by a `Finset` element.** `¬RH` is equivalent to the existence of a
radius and an actual *element* of the finite zero set in that radius, lying in the strip and off
the critical line. -/
theorem not_riemannHypothesis_iff_exists_in_finset :
    ¬ RiemannHypothesis ↔
      ∃ (R : ℝ) (z : ℂ), z ∈ (finite_zerosInBall R).toFinset ∧
        0 < z.re ∧ z.re < 1 ∧ z.re ≠ 1 / 2 := by
  rw [not_riemannHypothesis_iff_exists_off_line]
  constructor
  · rintro ⟨z, h0, h1, hz, hoff⟩
    refine ⟨‖z‖, z, ?_, h0, h1, hoff⟩
    simp [zerosInBall, hz]
  · rintro ⟨R, z, hz, h0, h1, hoff⟩
    have hz' : z ∈ zerosInBall R := by simpa using hz
    exact ⟨z, h0, h1, hz'.1, hoff⟩

end RHProvability
