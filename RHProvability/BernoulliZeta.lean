/-
# The missing Bernoulli ingredient, and `TrivialZerosOnLeft`

Mathlib has every piece of `TrivialZerosOnLeft` except one: even-index Bernoulli numbers are
not shown to be nonzero. This file supplies it — not by analysis, but by *reading the closed
formula for ζ(2k) backwards*:

`riemannZeta_two_mul_nat : ζ(2k) = (-1)^{k+1} · 2^{2k-1} · π^{2k} · B_{2k} / (2k)!`

Since `ζ(2k) ≠ 0` for `k ≥ 1` (`riemannZeta_ne_zero_of_one_lt_re`), every other factor is
nonzero, so `B_{2k} ≠ 0`. That is a genuine gap in Mathlib (no `bernoulli_ne_zero_of_even`
exists) closed with one line of algebra.

Then the assembly of `TrivialZerosOnLeft`, with the case split:

* `s = 0`: `ζ 0 = -1/2 ≠ 0`.
* `s = -k`, `k` odd: `ζ(-k) = (-1)^k B_{k+1}/(k+1)`, and `k+1` is even, so `B_{k+1} ≠ 0`.
* `s = -2m`: a trivial zero, so it is of the required form.
* `s ∉ -ℕ`: the functional equation turns `ζ s = 0` into `ζ(1-s) = 0`, but
  `Re (1-s) = 1 - Re s ≥ 1`, where `ζ` is nonzero.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RHProvability.RHFormulas

namespace RHProvability

/-- Even-index Bernoulli numbers `B_{2k}` (`k ≥ 1`) are nonzero.

Derived from `ζ(2k) ≠ 0` and the closed formula for `ζ(2k)`. This is the ingredient that is
missing from `Mathlib.NumberTheory.Bernoulli` (which has `bernoulli_eq_zero_of_odd` but no
nonvanishing statement for even indices). -/
theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro hB
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  have hgt : (1 : ℝ) < ((2 * k : ℕ) : ℝ) := by
    have : (1 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have hζ : riemannZeta ((2 * k : ℕ) : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hgt
  refine hζ ?_
  rw [show ((2 * k : ℕ) : ℂ) = 2 * (k : ℂ) by push_cast; ring,
    riemannZeta_two_mul_nat (k := k) hk, hB]
  simp

/-- `ζ(-k) ≠ 0` for odd `k`, via `ζ(-k) = (-1)^k B_{k+1}/(k+1)` with `k+1` even. -/
theorem riemannZeta_neg_nat_ne_zero_of_odd {k : ℕ} (hk : Odd k) :
    riemannZeta (-(k : ℂ)) ≠ 0 := by
  obtain ⟨m, hm⟩ := hk
  have hB : ((bernoulli (k + 1) : ℚ) : ℂ) ≠ 0 := by
    have h1 : k + 1 = 2 * (m + 1) := by omega
    have h2 : bernoulli (k + 1) ≠ 0 := by rw [h1]; exact bernoulli_two_mul_ne_zero (by omega)
    exact_mod_cast h2
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by
    have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact_mod_cast Nat.succ_ne_zero k
  rw [riemannZeta_neg_nat_eq_bernoulli]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB) hk1

/-- Every zero of `ζ` in the closed left half-plane is a trivial zero `-2, -4, -6, …`.

This closes the only gap between Mathlib's `RiemannHypothesis` and the textbook
critical-strip statement (see `riemannHypothesis_iff_strip`). -/
theorem trivialZerosOnLeft : TrivialZerosOnLeft := by
  intro s hzero hle
  by_cases hnat : ∃ k : ℕ, s = -(k : ℂ)
  · obtain ⟨k, rfl⟩ := hnat
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      simp only [Nat.cast_zero, neg_zero] at hzero
      rw [riemannZeta_zero] at hzero
      norm_num at hzero
    · rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- `k = 2m`, `m ≥ 1`: a trivial zero, of the required form with `n = m - 1`
        refine ⟨m - 1, ?_⟩
        have hm1 : 1 ≤ m := by omega
        rw [hm]
        have hcast : (((m - 1 : ℕ) : ℂ) + 1) = (m : ℂ) := by
          have h : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel hm1
          calc ((m - 1 : ℕ) : ℂ) + 1 = (((m - 1) + 1 : ℕ) : ℂ) := by push_cast; ring
            _ = (m : ℂ) := by rw [h]
        rw [hcast]
        push_cast
        ring
      · exact absurd hzero (riemannZeta_neg_nat_ne_zero_of_odd ⟨m, hm⟩)
  · have hs : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n hn => hnat ⟨n, hn⟩
    have hne1 : s ≠ 1 := by
      intro h
      rw [h] at hle
      norm_num at hle
    have hFE := riemannZeta_one_sub hs hne1
    rw [hzero, mul_zero] at hFE
    have hge : (1 : ℝ) ≤ ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact absurd hFE (riemannZeta_ne_zero_of_one_le_re hge)



/-- **Unconditional bridge**: Mathlib's `RiemannHypothesis` is equivalent to the textbook
critical-strip formulation. The analytic input is discharged by `trivialZerosOnLeft`. -/
theorem riemannHypothesis_iff_strip_unconditional :
    RiemannHypothesis ↔ RiemannHypothesisStrip :=
  riemannHypothesis_iff_strip trivialZerosOnLeft

/-- The textbook form follows from Mathlib's, unconditionally. -/
theorem riemannHypothesisStrip_unconditional (h : RiemannHypothesis) : RiemannHypothesisStrip :=
  riemannHypothesis_implies_strip h

end RHProvability
