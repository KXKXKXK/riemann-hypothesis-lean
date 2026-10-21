/-
# Mathlib's `RiemannHypothesis` versus the critical-strip formulation

`Mathlib.NumberTheory.LSeries.RiemannZeta` defines

`RiemannHypothesis : Prop := ∀ s, riemannZeta s = 0 → ¬∃ n, s = -2 * (n + 1) → s ≠ 1 → s.re = 1/2`

(zeros of ζ excluding the trivial zeros `-2, -4, -6, …` and excluding `s = 1`). The textbook
statement quantifies over the critical strip instead:

`RH_strip : ∀ s, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`.

These are *not* literally the same formula, and the difference is a proof obligation, not a
convention. This file discharges it and isolates exactly one analytic input.

Proved here (kernel-checked, no axioms):

* `riemannHypothesis_implies_strip` — the Mathlib form implies the strip form. No analytic input.
* `riemannHypothesis_without_ne_one` — the hypothesis `s ≠ 1` is **redundant**: it follows from
  `riemannZeta 1 ≠ 0`. So the extra hypothesis is harmless but unnecessary.
* `riemannHypothesis_of_strip` — conversely, the strip form gives the Mathlib form *provided*
  every zero in the closed left half-plane is a trivial zero (`TrivialZerosOnLeft`).
* `riemannHypothesis_iff_strip` — the two forms are equivalent given that input.

Not proved here: `TrivialZerosOnLeft`. It is a genuine analytic statement (the functional
equation plus the zeros of `Γ` and of `cos (π s / 2)`), and the point of isolating it is that
this is the *only* place where analysis enters the comparison. See NOTES-iteration2.md for the
lemma inventory that proves it.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace RHProvability

/-- Doctrinal form of RH: every zero in the critical strip lies on the critical line. -/
def RiemannHypothesisStrip : Prop :=
  ∀ (s : ℂ), 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- Every zero in the closed left half-plane is a trivial zero `-2, -4, -6, …`.

This is the analytic input that the two formulations of RH differ by. It is *not* proved here;
it follows from the functional equation `riemannZeta_one_sub` together with the location of the
zeros of `Γ` and of `cos (π s / 2)`. -/
def TrivialZerosOnLeft : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 → s.re ≤ 0 → ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

/-- Mathlib's formulation implies the critical-strip formulation. No analytic input needed:
a trivial zero has strictly negative real part, and `1` has real part `1`. -/
theorem riemannHypothesis_implies_strip (h : RiemannHypothesis) : RiemannHypothesisStrip := by
  intro s h0 h1 hzero
  refine h s hzero ?_ ?_
  · rintro ⟨n, hn⟩
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      simp
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [hre] at h0
    nlinarith
  · intro hse
    have hre : s.re = 1 := by rw [hse]; simp
    rw [hre] at h1
    norm_num at h1

/-- The hypothesis `s ≠ 1` in Mathlib's `RiemannHypothesis` is redundant: `ζ 1 ≠ 0`. -/
theorem riemannHypothesis_without_ne_one (h : RiemannHypothesis) :
    ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s.re = 1 / 2 := by
  intro s hzero htriv
  by_cases hs : s = 1
  · subst hs
    exact absurd hzero riemannZeta_one_ne_zero
  · exact h s hzero htriv hs

/-- Conversely: the strip form plus `TrivialZerosOnLeft` gives Mathlib's form. The right
half-plane is handled by `riemannZeta_ne_zero_of_one_le_re`; the left half-plane is exactly
the `TrivialZerosOnLeft` input. -/
theorem riemannHypothesis_of_strip (hstrip : RiemannHypothesisStrip)
    (hleft : TrivialZerosOnLeft) : RiemannHypothesis := by
  intro s hzero htriv _hne
  by_cases hge : 1 ≤ s.re
  · exact absurd hzero (riemannZeta_ne_zero_of_one_le_re hge)
  · push_neg at hge
    by_cases hpos : 0 < s.re
    · exact hstrip s hpos hge hzero
    · push_neg at hpos
      obtain ⟨n, hn⟩ := hleft s hzero hpos
      exact absurd ⟨n, hn⟩ htriv

/-- The two formulations agree, given the trivial-zeros input. -/
theorem riemannHypothesis_iff_strip (hleft : TrivialZerosOnLeft) :
    RiemannHypothesis ↔ RiemannHypothesisStrip :=
  ⟨riemannHypothesis_implies_strip, fun h => riemannHypothesis_of_strip h hleft⟩

end RHProvability
