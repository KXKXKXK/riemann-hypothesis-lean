/-
# "RH up to height `H`", and what it is worth

The committed positive target of this round is: state "RH holds up to height `H`" and connect it to the
principal object (`offLineCount`), so that a future explicit verification has a place to land.

## Honest label for this file

Most of it is **infrastructure, not progress**. `rhUpTo_mono` and
`riemannHypothesis_iff_forall_rhUpTo` hold automatically whenever RH holds, so by the round's own
reporting rule they do not count as progress. They are here because the *first non-trivial instance*
cannot be stated without them.

The one instance included, `rhUpTo_of_neg`, is **vacuous** (for `H < 0` the box is empty) and is
labelled as such: it is not a verification. The first genuine instance needs

1. the argument principle for a rectangle (absent from Mathlib: no `argument_principle` anywhere),
2. certified interval arithmetic for `ζ` and `ζ'` on the rectangle boundary (absent),
3. an explicit count upper bound (Riemann–von Mangoldt type, absent),

in that order; see `NOTES-iteration13-rh-up-to-height.md` for the block-by-block assessment.
-/
import RHProvability.OffLine

namespace RHProvability

/-- **RH holds up to height `H`**: every zero strictly inside the critical strip with `|Im| ≤ H` lies on
the critical line. Stated pointwise (no `Finset`, no counting) so that it is exactly what a boundary
argument would certify. -/
def RHUpTo (H : ℝ) : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 → |z.im| ≤ H → z.re = 1 / 2

/-- Raising the height weakens the statement; lowering it strengthens. -/
theorem rhUpTo_mono {H₁ H₂ : ℝ} (h : H₁ ≤ H₂) (h2 : RHUpTo H₂) : RHUpTo H₁ :=
  fun z hz h0 h1 him => h2 z hz h0 h1 (le_trans him h)

/-- **The programme's exact target.** RH is equivalent to the conjunction of all height-bounded
statements. (Infrastructure: automatic under RH, so not progress.) -/
theorem riemannHypothesis_iff_forall_rhUpTo : RiemannHypothesis ↔ ∀ H : ℝ, RHUpTo H := by
  constructor
  · intro h H z hz h0 h1 _
    by_contra hne
    exact absurd h ((not_riemannHypothesis_iff_exists_off_line).mpr ⟨z, h0, h1, hz, hne⟩)
  · intro h
    by_contra hnot
    obtain ⟨z, h0, h1, hz, hoff⟩ := (not_riemannHypothesis_iff_exists_off_line).mp hnot
    exact hoff (h |z.im| z hz h0 h1 le_rfl)

/-- **A vacuous instance, included to be labelled.** For `H < 0` there is no `z` with `|z.im| ≤ H`, so
the statement holds for free. This is **not** a verification of RH to any height, and is not counted as
progress. -/
theorem rhUpTo_of_neg {H : ℝ} (h : H < 0) : RHUpTo H := by
  intro z _ _ _ him
  exact absurd him (not_le.mpr (lt_of_lt_of_le h (abs_nonneg z.im)))

end RHProvability
