/-
# Effective bounds for `e^γ`, and why Robin's criterion is *almost* `Π⁰₁`

Two things happen in this file.

## 1. An unconditional, machine-checked bracket for `e^γ`

`Robin.lean` introduced `robinCriterionEulerGamma` with the constant `e^γ` left abstract. Making the
comparison computable needs *rational* bounds on that constant, so here is the first one, derived
from Mathlib's bounds on the Euler–Mascheroni constant
(`Real.one_half_lt_eulerMascheroniConstant`, `Real.eulerMascheroniConstant_lt_two_thirds`) and the
elementary exponentials bounds (`Real.add_one_le_exp`, `Real.exp_lt_exp`, `Real.exp_one_lt_d9`):

  `3/2 < e^γ < 2`.

This is a real (if weak) certificate: the bounds are rationals and the proof is machine-checked.

## 2. A precise diagnosis of the obstruction

The obvious way to turn a real inequality `f < c · g` into a `Π⁰₁` matrix is to approximate `c` from
above by rationals `u k ↓ c` and rewrite the comparison as `∀ k, f < u k · g` — a `∀` over a
decidable comparison. That works for the **non-strict** inequality:

  `f ≤ c · g  ↔  ∀ k, f < u k · g`     (`le_iff_forall_lt_upper`)

and it **fails** for the strict one: the implication `(∀ k, f < u k · g) → f < c · g` is refuted by
a concrete numerical counterexample (`strict_version_refuted`), namely `c = 0`, `u k = 1/(k+1)`,
`f = 0`, `g = 1`.

Consequence, stated plainly: this route produces the `Π⁰₁` form of the **non-strict** Robin
inequality `σ(n) ≤ e^γ · n · log log n`, and *not* of Robin's strict inequality. The gap is exactly
the equality case `σ(n) = e^γ · n · log log n`, which this file does not resolve (it would need
independence-type information about a single transcendental equation).

## What is still missing after this file

The `∀ k` form still contains the real number `Real.log (Real.log n)`; making the matrix decidable
also needs *rational bounds on `log log n`*, which is a separate (logarithmic-arithmetic) task.
This file removes the obstruction coming from the constant `e^γ` and identifies the residual one.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Order.OrderClosed
import RHProvability.Robin

namespace RHProvability

open Filter
open scoped Topology

/-! ## Rational bounds for `e^γ` -/

/-- `e^γ > 3/2`, from `γ > 1/2` and `1 + x ≤ exp x`. -/
theorem exp_eulerMascheroniConstant_gt_three_halves :
    (3 / 2 : ℝ) < Real.exp Real.eulerMascheroniConstant := by
  have h := Real.add_one_le_exp Real.eulerMascheroniConstant
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  linarith

/-- `e^γ < 2`: this needs a strictly better upper bound than `exp 1 < 3`, obtained by cubing:
`e^2 = (e^1)^2 < 8`, hence `e^{2/3} < 2`, and `γ < 2/3`. -/
theorem exp_eulerMascheroniConstant_lt_two :
    Real.exp Real.eulerMascheroniConstant < 2 := by
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp2 : Real.exp 2 < 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hcube : Real.exp (2 / 3) ^ 3 < 2 ^ 3 := by
    rw [show ((2 : ℝ) ^ 3) = 8 by norm_num]
    have h := Real.exp_nat_mul (2 / 3 : ℝ) 3
    rw [show (3 : ℕ) * (2 / 3 : ℝ) = 2 by norm_num] at h
    rw [← h]
    exact hexp2
  have hnonneg : (0 : ℝ) ≤ Real.exp (2 / 3) := le_of_lt (Real.exp_pos _)
  have hlt : Real.exp (2 / 3) < 2 := by
    by_contra hcon
    push Not at hcon
    have : (2 : ℝ) ^ 3 ≤ Real.exp (2 / 3) ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num) hcon 3
    linarith
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  exact lt_trans (Real.exp_lt_exp.mpr hγ) hlt

/-- The bracket, as one statement. -/
theorem exp_eulerMascheroniConstant_bracket :
    (3 / 2 : ℝ) < Real.exp Real.eulerMascheroniConstant ∧
      Real.exp Real.eulerMascheroniConstant < 2 :=
  ⟨exp_eulerMascheroniConstant_gt_three_halves, exp_eulerMascheroniConstant_lt_two⟩

/-! ## Strictly-descending upper approximations: what they do and do not buy -/

/-- **The `Π⁰₁`-shaping theorem.** If `u : ℕ → ℝ` converges to `c` from *strictly above* and `g > 0`,
then the non-strict comparison `f ≤ c · g` is equivalent to the `∀ k` form `∀ k, f < u k · g`,
in which the matrix is a comparison against `u k` (a rational, in applications).

Forward: `c < u k` and `g > 0` give `c · g < u k · g`, so `f ≤ c · g < u k · g`.
Backward: pass to the limit in `f < u k · g`. -/
theorem le_iff_forall_lt_upper {c : ℝ} {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 c))
    (hupper : ∀ k, c < u k) {f g : ℝ} (hg : 0 < g) :
    f ≤ c * g ↔ ∀ k, f < u k * g := by
  constructor
  · rintro h k
    have hlt : c * g < u k * g := mul_lt_mul_of_pos_right (hupper k) hg
    linarith
  · intro h
    have hle : ∀ᶠ k in atTop, f ≤ u k * g := Eventually.of_forall fun k => le_of_lt (h k)
    have ht : Tendsto (fun k => u k * g) atTop (𝓝 (c * g)) := hu.mul_const g
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht hle

/-- **The obstruction, as a machine-checked counterexample.** The `≤` above cannot be strengthened
to `<`: taking `c = 0`, `u k = 1/(k+1)`, `f = 0`, `g = 1` satisfies every hypothesis (including
`∀ k, f < u k · g`) but `¬ (f < c · g)`.

So a strictly-descending rational approximation of a constant certifies the **non-strict**
inequality only. Robin's criterion is strict, and this gap is not an artefact of the proof — it is
the equality case. -/
theorem strict_version_refuted :
    ¬ ∀ (c : ℝ) (u : ℕ → ℝ) (f g : ℝ), Tendsto u atTop (𝓝 c) → (∀ k, c < u k) → 0 < g →
        (∀ k, f < u k * g) → f < c * g := by
  intro h
  have hu : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hall : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) * 1 := fun k => by linarith [hupper k]
  have := h 0 (fun k : ℕ => 1 / ((k : ℝ) + 1)) 0 1 hu hupper one_pos hall
  linarith

/-! ## The Robin instance: the non-strict criterion in `Π⁰₁` form -/

/-- The **non-strict** Robin inequality: `σ(n) ≤ e^γ · n · log log n` for every `n ≥ 5041`.

This is *not* Robin's criterion (which is strict) and this file does **not** claim it is equivalent
to RH. It is the statement that the machinery below actually reaches. -/
def RobinCriterionLe (c : ℝ) : Prop :=
  ∀ n : ℕ, 5041 ≤ n → (sigmaNat n : ℝ) ≤ c * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- For `n ≥ 5041`, the inner `log log n` is positive, so `n · log log n > 0`. -/
theorem log_log_pos_of_ge_5041 {n : ℕ} (hn : 5041 ≤ n) :
    0 < Real.log (Real.log (n : ℝ)) := by
  have hnR : (5041 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hexp : Real.exp 1 < (n : ℝ) := by linarith
  have h1 : 1 < Real.log (n : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  exact Real.log_pos h1

/-- **The Robin instance of the shaping theorem**: the non-strict inequality is equivalent to a
`∀ n ∀ k` statement whose matrix compares `σ(n)` with `u k · n · log log n`.

The remaining real number is `log log n`; bounding it rationally is a separate task. -/
theorem robinCriterionLe_iff_forall_upper {c : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 c)) (hupper : ∀ k, c < u k) :
    RobinCriterionLe c ↔
      ∀ n : ℕ, 5041 ≤ n → ∀ k : ℕ,
        (sigmaNat n : ℝ) < u k * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  constructor
  · intro h n hn k
    have hg : 0 < (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
      have hn' : (0 : ℝ) < (n : ℝ) := by
        have : (0 : ℝ) < 5041 := by norm_num
        have hnR : (5041 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact mul_pos hn' (log_log_pos_of_ge_5041 hn)
    have hle : (sigmaNat n : ℝ) ≤ c * ((n : ℝ) * Real.log (Real.log (n : ℝ))) :=
      (h n hn).trans_eq (by ring)
    have := (le_iff_forall_lt_upper hu hupper hg).mp hle k
    simpa [mul_assoc] using this
  · intro h n hn
    have hg : 0 < (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
      have hn' : (0 : ℝ) < (n : ℝ) := by
        have : (0 : ℝ) < 5041 := by norm_num
        have hnR : (5041 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact mul_pos hn' (log_log_pos_of_ge_5041 hn)
    have hm : (sigmaNat n : ℝ) ≤ c * ((n : ℝ) * Real.log (Real.log (n : ℝ))) :=
      (le_iff_forall_lt_upper hu hupper hg).mpr fun k => by
        have hk := h n hn k
        calc (sigmaNat n : ℝ) < u k * (n : ℝ) * Real.log (Real.log (n : ℝ)) := hk
          _ = u k * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := by ring
    calc (sigmaNat n : ℝ) ≤ c * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := hm
      _ = c * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring

end RHProvability
