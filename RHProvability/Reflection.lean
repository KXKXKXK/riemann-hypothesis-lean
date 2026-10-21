/-
# Reflection symmetry of the zeros in the critical strip, and a second form of RH

Mathlib has the functional equation (`riemannZeta_one_sub`), `Gamma` nonvanishing for `Re s > 0`
(`Complex.Gamma_ne_zero_of_re_pos`, which is the weaker of the two available statements and the
only one used) and the zeros of complex `cos`. Those three facts make the functional equation
*invertible inside the critical strip*, where the prefactor `2 (2π)^{-s} Γ(s) cos(πs/2)` is nonzero:

`ζ(1 - s) = 0 ↔ ζ(s) = 0` for `0 < Re s < 1`.

Consequences proved here:

* `riemannZeta_zero_reflect` — the zeros in the open strip are symmetric about the critical line.
* `riemannHypothesisStrip_iff_no_right` — RH (strip form) is equivalent to "ζ has no zero with
  `1/2 < Re s < 1`". This is the form normally used when one says "RH says there is nothing to
  the right of the critical line".

Nothing about provability or independence is proved here; this is analysis only.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import RHProvability.RHFormulas
import RHProvability.BernoulliZeta

namespace RHProvability

open Complex
open scoped Real

/-- `ζ` has no zeros strictly to the right of the critical line **inside the strip**
(`1/2 < Re s < 1`). The name omits "inside the strip"; the definition does not.
(The unrestricted version, for `1 ≤ Re s`, is `riemannZeta_ne_zero_of_one_le_re`.) -/
def NoZerosRightOfCriticalLine : Prop :=
  ∀ (s : ℂ), 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- The prefactor of the functional equation is nonzero in the open critical strip:

`2 · (2π)^{-s} · Γ(s) · cos (πs/2) ≠ 0` for `0 < Re s < 1`.

Each factor: `2 ≠ 0`; `2π ≠ 0`; `Γ s ≠ 0` because `Re s > 0`; and `cos (πs/2) = 0` would force
`s = 2k+1`, an odd integer, which cannot have real part in `(0, 1)`. -/
theorem riemannZeta_funEq_prefactor_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (2 : ℂ) * (2 * (π : ℂ)) ^ (-s) * Gamma s * cos (π * s / 2) ≠ 0 := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (π : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hbase : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero htwo hpi
  have hpow : ((2 * (π : ℂ)) ^ (-s)) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hbase h.1
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h0
  have hcos : cos (π * s / 2) ≠ 0 := by
    intro h
    rw [Complex.cos_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    -- from `π * s / 2 = (2k+1) * π / 2` conclude `s = 2k + 1`
    have hmul : (π : ℂ) * s = (2 * (k : ℂ) + 1) * (π : ℂ) := by
      have h2 : (π : ℂ) * s * 2 = (2 * (k : ℂ) + 1) * (π : ℂ) * 2 := by
        have := (div_eq_div_iff (by norm_num : (2 : ℂ) ≠ 0) (by norm_num : (2 : ℂ) ≠ 0)).mp hk
        simpa using this
      exact mul_right_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
    have hs : s = 2 * (k : ℂ) + 1 := by
      have h2 : (π : ℂ) * s = (π : ℂ) * (2 * (k : ℂ) + 1) := by
        rw [hmul]; ring
      exact mul_left_cancel₀ hpi h2
    have hre : s.re = 2 * (k : ℝ) + 1 := by
      rw [hs]
      simp
    have hlt1 : (2 * (k : ℝ) + 1) < 1 := by linarith
    have hgt0 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by linarith
    have h1 : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast hgt0
    have h2 : 2 * k + 1 < (1 : ℤ) := by exact_mod_cast hlt1
    omega

  exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hpow) hG) hcos

/-- Inside the open critical strip, `ζ(1-s) = 0 ↔ ζ(s) = 0`: the functional equation is
invertible there. -/
theorem riemannZeta_zero_reflect {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  have hs : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    have hre : s.re = -(n : ℝ) := by
      rw [hn]
      simp
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre] at h0
    linarith
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have hc := riemannZeta_funEq_prefactor_ne_zero h0 h1
  rw [riemannZeta_one_sub hs hne1]
  constructor
  · intro h
    by_contra hz
    exact (mul_ne_zero hc hz) h
  · intro h
    rw [h, mul_zero]

/-- RH in strip form is equivalent to: no zero strictly to the right of the critical line
inside the strip. The forward direction is immediate; the reverse uses the reflection symmetry
to move a supposed zero with `Re s < 1/2` to one with `Re (1-s) > 1/2`. -/
theorem riemannHypothesisStrip_iff_no_right :
    RiemannHypothesisStrip ↔ NoZerosRightOfCriticalLine := by
  constructor
  · intro hstrip s hgt hlt hzero
    have := hstrip s (by linarith) hlt hzero
    linarith
  · intro hno s h0 h1 hzero
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `Re s < 1/2`: reflect to `1 - s`, which lies to the right of the line
      have hz : riemannZeta (1 - s) = 0 := (riemannZeta_zero_reflect h0 h1).mpr hzero
      have hre : ((1 : ℂ) - s).re = 1 - s.re := by
        simp
      apply hno (1 - s) ?_ ?_ hz
      · rw [hre]; linarith
      · rw [hre]; linarith
    · exact hno s hgt h1 hzero

/-- Mathlib's `RiemannHypothesis` is equivalent to the statement that `ζ` has no zero strictly to
the right of the critical line inside the strip. Obtained by composing the interface bridge
(`riemannHypothesis_iff_strip_unconditional`) with the reflection result.

**Read this as an equivalence between two *unproved* propositions, not as progress on either.**
Nothing here shows that `ζ` has no such zero; it shows that the two ways of saying it are the same
sentence. -/
theorem riemannHypothesis_iff_no_right :
    RiemannHypothesis ↔ NoZerosRightOfCriticalLine :=
  riemannHypothesis_iff_strip_unconditional.trans riemannHypothesisStrip_iff_no_right

end RHProvability
