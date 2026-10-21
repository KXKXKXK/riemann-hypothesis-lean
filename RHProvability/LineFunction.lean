/-
# Gap 1 is not a gap: `OpenRealValuedLineFunction` is provable

`Overview.lean:339` registers

    def OpenRealValuedLineFunction : Prop :=
      ∃ Z : ℝ → ℝ, Continuous Z ∧
        ∀ t : ℝ, (Z t = 0 ↔ riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0)

as **Gap 1**, with the comment "This is what makes sign-change counting meaningful".
This file proves it, and explains why the *registration*, not the mathematics, is what is wrong.

## The proof

1. `S := {t | ζ (1/2 + i t) = 0}` is **closed**: ζ is differentiable at every point of the critical
   line (`differentiableAt_riemannZeta`, applicable because `1/2 + i t ≠ 1`), hence continuous there.
2. If `S = ∅`, take `Z ≡ 1`. Otherwise take `Z t := infDist t S`, using
   `continuous_infDist_pt` and `IsClosed.mem_iff_infDist_zero`.

## Why this is a registration error, not progress on RH

`infDist t S` is **non-negative everywhere**, so `Z` never changes sign. A non-negative function
whose zero set is `S` cannot witness a sign change across any zero, so it cannot support
"sign-change counting" — the statement as registered is satisfied by an object that is useless for
the purpose it was introduced for.

The correct action is therefore **not** to tick Gap 1 off, but to **restrict** the statement to a
real-valued function that actually changes sign at the zeros — e.g. the Riemann–Siegel `Z` function,
whose construction (`Z t := e^{i θ(t)} ζ(1/2 + it)` is real) *is* real analytic content. That
restricted statement is **not** proved here and must not be conflated with the theorem below.

The registry already has two precedents for "it was never a gap" (`OpenConjSymmetry`,
`OpenCountsEqOfRH`, see `Overview.lean:332–334`). This is the third, with the extra twist that the
statement is not merely over-specified: it is **too weak to serve its own stated purpose**.

## Status of this file

Proved with `lake env lean` against the project's pinned toolchain (Lean v4.33.0, Mathlib
`db584cd6`). Not yet wired into the root import list, so the project's `lake build` job count is
unchanged. Axioms: `[propext, Classical.choice, Quot.sound]` only.
-/
import RHProvability.Overview

namespace RHProvability.Overview

open Metric

/-- ζ restricted to the critical line is continuous as a function of `t`. -/
theorem continuous_zetaOnCriticalLine :
    Continuous (fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hζD : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hζc : ContinuousOn riemannZeta ({1}ᶜ : Set ℂ) := hζD.continuousOn
  have hinner : Continuous (fun u : ℝ => (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I)) := by
    fun_prop
  have hmaps : ∀ u : ℝ, (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∈ ({1}ᶜ : Set ℂ) := by
    intro u h
    have := congrArg Complex.re h
    simp at this
  exact hζc.comp_continuous hinner hmaps

/-- The zero set of ζ on the critical line is closed in `ℝ`. -/
theorem isClosed_zetaZeroSetOnCriticalLine :
    IsClosed {t : ℝ | riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0} :=
  isClosed_singleton.preimage continuous_zetaOnCriticalLine

/-- **Gap 1, proved.** A real-valued continuous function on `ℝ` whose zeros are exactly the zeros of
`ζ` on the critical line.

**Read the file header before citing this as progress on RH:** the constructed `Z` is non-negative,
so it never changes sign, and the registered statement is therefore a registration error rather than
an open problem. -/
theorem openRealValuedLineFunction : OpenRealValuedLineFunction := by
  classical
  set S : Set ℝ := {t : ℝ | riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0} with hS
  have hclosed : IsClosed S := isClosed_zetaZeroSetOnCriticalLine
  rcases S.eq_empty_or_nonempty with hemp | hne
  · -- no zeros: the constant `1` has the right zero set
    refine ⟨fun _ => 1, continuous_const, ?_⟩
    intro t
    have hz : riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have : t ∈ S := h
      rw [hemp] at this
      exact this
    constructor
    · intro h1; exact absurd h1 one_ne_zero
    · intro h2; exact absurd h2 hz
  · -- otherwise the distance to the (closed) zero set
    refine ⟨fun t => infDist t S, continuous_infDist_pt S, ?_⟩
    intro t
    have hiff : infDist t S = 0 ↔ t ∈ S := (hclosed.mem_iff_infDist_zero hne (x := t)).symm
    simpa [hS] using hiff

end RHProvability.Overview
