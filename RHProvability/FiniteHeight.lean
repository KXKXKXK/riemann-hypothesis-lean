/-
# RH as an infinite conjunction of finite checks (the Π⁰₁ skeleton)

Route A of the research plan asks for an explicit, computational form `RH ↔ ∀ n, check n = true`.
This file supplies the part of that reduction that is *provable now* without any new analysis:

* the zeros of `ζ` in a closed ball form a **finite** set (`finite_zerosInBall`), because the zero
  set is discrete (`isDiscrete_riemannZetaZeros`) and closed balls are compact;
* RH is equivalent to an infinite conjunction of statements, one per radius, each quantifying over
  that **finite** set (`riemannHypothesis_iff_ball`);
* the negation of RH is equivalent to the existence of a zero *inside the open critical strip* off
  the critical line (`not_riemannHypothesis_iff_exists_off_line`), hence to a witness of **finite
  height** (`not_riemannHypothesis_witness_finite`).

What is honestly *not* here: a *decidable* check. `check n` in the statement above is a decidable
predicate on rationals; this file gives the logical form of the reduction and the finiteness that
makes it finite, but the effective/interval-arithmetic content (Euler–Maclaurin remainders with
explicit error bounds) is not formalized. See NOTES-iteration6 for the exact gap.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RHProvability.BernoulliZeta
import RHProvability.Reflection

namespace RHProvability

open Complex
open scoped Real

/-- Zeros of `ζ` inside the closed ball of radius `R`. -/
def zerosInBall (R : ℝ) : Set ℂ := {z | riemannZeta z = 0 ∧ ‖z‖ ≤ R}

/-- **Finiteness.** For every radius, only finitely many zeros. This is what makes the "check at
height `R`" formulation a *finite* check at each stage. -/
theorem finite_zerosInBall (R : ℝ) : (zerosInBall R).Finite := by
  have hc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hfin : (Metric.closedBall (0 : ℂ) R ∩ riemannZetaZeros).Finite :=
    hc.inter_riemannZetaZeros_finite
  refine hfin.subset ?_
  intro z hz
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2, mem_riemannZetaZeros.mpr hz.1⟩

/-- A non-trivial zero which is not `1` lies in the open critical strip. Uses `trivialZerosOnLeft`
(the left half-plane) and `riemannZeta_ne_zero_of_one_le_re` (the closed right half-plane). -/
theorem zero_mem_strip_of_not_trivial {z : ℂ} (hz : riemannZeta z = 0)
    (htriv : ¬∃ n : ℕ, z = -2 * ((n : ℂ) + 1)) (hne1 : z ≠ 1) :
    0 < z.re ∧ z.re < 1 := by
  constructor
  · by_contra h
    push_neg at h
    exact htriv (trivialZerosOnLeft z hz h)
  · by_contra h
    push_neg at h
    exact (riemannZeta_ne_zero_of_one_le_re (by linarith : (1 : ℝ) ≤ z.re)) hz

/-- **RH as an infinite conjunction of finite checks.** For every radius `R`, every zero of `ζ`
inside the ball of radius `R` that lies in the critical strip must lie on the critical line.
By `finite_zerosInBall` each conjunct is a statement about a finite set. -/
theorem riemannHypothesis_iff_ball :
    RiemannHypothesis ↔
      ∀ (R : ℝ), ∀ z : ℂ, ‖z‖ ≤ R → riemannZeta z = 0 →
        0 < z.re → z.re < 1 → z.re = 1 / 2 := by
  constructor
  · intro h R z _ hz h0 h1
    exact riemannHypothesisStrip_unconditional h z h0 h1 hz
  · intro h z hz htriv hne1
    have hstrip := zero_mem_strip_of_not_trivial hz htriv hne1
    exact h ‖z‖ z le_rfl hz hstrip.1 hstrip.2

/-- **The negation, localized.** `¬RH` is exactly: some zero lies in the open critical strip and
off the critical line. (This is where `trivialZerosOnLeft` is load-bearing: without it, `¬RH`
could be witnessed by a "trivial" zero, which is not off the line at all.) -/
theorem not_riemannHypothesis_iff_exists_off_line :
    ¬ RiemannHypothesis ↔
      ∃ z : ℂ, 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0 ∧ z.re ≠ 1 / 2 := by
  constructor
  · intro h
    by_contra hno
    refine h fun z hz htriv hne1 => ?_
    have hstrip := zero_mem_strip_of_not_trivial hz htriv hne1
    by_contra hoff
    exact hno ⟨z, hstrip.1, hstrip.2, hz, hoff⟩
  · rintro ⟨z, h0, h1, hz, hoff⟩ hRH
    exact hoff (riemannHypothesisStrip_unconditional hRH z h0 h1 hz)

/-- **Finite-height witness.** If RH fails, a counterexample exists with *finite* height, in a ball
of finite radius. This is the mathematical content of "a finite counterexample would already refute
it"; what is not proved is that the check is *decidable* (see the file header). -/
theorem not_riemannHypothesis_witness_finite (h : ¬ RiemannHypothesis) :
    ∃ (R : ℝ) (z : ℂ), ‖z‖ ≤ R ∧ riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ z.re ≠ 1 / 2 := by
  obtain ⟨z, h0, h1, hz, hoff⟩ := not_riemannHypothesis_iff_exists_off_line.mp h
  exact ⟨‖z‖, z, le_rfl, hz, h0, h1, hoff⟩

/-- **Countably indexed form.** Same statement with the radius ranging over `ℕ` instead of `ℝ`.
This is the shape a `Π⁰₁` statement needs — a countable conjunction `∀ n : ℕ` — whereas the
real-radius version above is not countable as stated. -/
theorem riemannHypothesis_iff_ball_nat :
    RiemannHypothesis ↔
      ∀ (n : ℕ), ∀ z : ℂ, ‖z‖ ≤ n → riemannZeta z = 0 → 0 < z.re → z.re < 1 → z.re = 1 / 2 := by
  constructor
  · intro h n z _ hz h0 h1
    exact riemannHypothesisStrip_unconditional h z h0 h1 hz
  · intro h z hz htriv hne1
    have hstrip := zero_mem_strip_of_not_trivial hz htriv hne1
    exact h ⌈‖z‖⌉₊ z (Nat.le_ceil ‖z‖) hz hstrip.1 hstrip.2

end RHProvability
