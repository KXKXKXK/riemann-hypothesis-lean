/-
# Closing the boundary gap: `RH ⟹ the two counts agree`

`LineCount.lean` proved "counts agree at every height ⟹ RH". The converse was left open on the
grounds that a zero with `Re z = 0` in the box was not excluded. An external audit pointed out that
this boundary is a *small* lemma, not a genuine gap:

* if `z.re = 0` and `z ≠ 0`, then `Re(1 - z) = 1`, so the functional equation gives
  `ζ(1-z) = (factor) · ζ(z)`; if `ζ(z) = 0` then `ζ(1-z) = 0`, contradicting
  `riemannZeta_ne_zero_of_one_le_re`;
* `z = 0` is excluded by `ζ(0) = -1/2`.

That is done here, so `OpenCountsEqOfRH` is **closed** and the counting invariant becomes an
equivalence rather than a one-way implication.
-/
import RHProvability.LineCount
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace RHProvability

open Complex

/-- **No zeros on the boundary line `Re z = 0`.** The functional equation transfers a zero at
`Re z = 0` to a zero at `Re(1 - z) = 1`, where `ζ` is known not to vanish; `z = 0` is handled by
`ζ(0) = -1/2`.

Note the hypotheses of `riemannZeta_one_sub`: `z ≠ -n` for every `n : ℕ` (automatic here, since
`z.im ≠ 0` while `-(n : ℂ)` is real) and `z ≠ 1` (automatic since `z.re = 0`). -/
theorem riemannZeta_ne_zero_of_re_eq_zero {z : ℂ} (hz : z.re = 0) : riemannZeta z ≠ 0 := by
  rintro hzero
  by_cases hz0 : z = 0
  · subst hz0
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  · have him : z.im ≠ 0 := by
      intro him
      apply hz0
      apply Complex.ext
      · simpa using hz
      · simpa using him
    have hnotneg : ∀ n : ℕ, z ≠ -(n : ℂ) := by
      intro n h
      have hnull : z.im = 0 := by rw [h]; simp
      exact him hnull
    have hne1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hfe := riemannZeta_one_sub hnotneg hne1
    have hz1 : riemannZeta (1 - z) = 0 := by
      rw [hfe, hzero, mul_zero]
    have hre : (1 : ℝ) ≤ (1 - z).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hre hz1

/-- **The converse of the counting invariant.** Under RH every zero in the box lies on the critical
line, so the two counts coincide at every height. -/
theorem countsEq_of_riemannHypothesis (hRH : RiemannHypothesis) (T : ℝ) :
    lineCount T = stripCount T := by
  have hset : zerosOnLineBox T = zerosInStripBox T := by
    refine Set.Subset.antisymm (zerosOnLineBox_subset T) ?_
    rintro z ⟨hz, hbox⟩
    have h0 : 0 ≤ z.re := hbox.2.1
    have h1 : z.re ≤ 1 := hbox.2.2
    have hre : z.re = 1 / 2 := by
      rcases lt_or_eq_of_le h0 with hpos | hzero
      · rcases lt_or_eq_of_le h1 with hlt | hone
        · exact riemannHypothesisStrip_unconditional hRH z hpos hlt hz
        · have hne := riemannZeta_ne_zero_of_one_le_re (s := z) (by rw [hone])
          exact absurd hz hne
      · exact absurd hz (riemannZeta_ne_zero_of_re_eq_zero hzero.symm)
    exact ⟨hz, hbox, hre⟩
  unfold lineCount stripCount
  rw [hset]

/-- **The counting invariant is an equivalence**: the two zero counts agree at every height **iff**
RH holds. -/
theorem countsEq_iff_riemannHypothesis :
    (∀ T : ℝ, lineCount T = stripCount T) ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_counts_eq, fun h T => countsEq_of_riemannHypothesis h T⟩

end RHProvability
