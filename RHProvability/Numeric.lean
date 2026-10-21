/-
# Certified rational bounds for `log` and `exp` — the arithmetic substrate of the Lagarias route

`Lagarias.lean` reduced Lagarias's criterion to a `∀ n ∀ k` form (item 22) whose matrix compares
`σ(n)` with rational upper approximations of `H_n + exp(H_n)·log(H_n)`. This file supplies the
**elementary bounds** on `log` and `exp` that such approximations need, all proved from scratch where
Mathlib has nothing:

* `one_sub_inv_le_log` — `1 - 1/x ≤ log x` for `x > 0` (the lower companion of Mathlib's
  `log_le_sub_one_of_pos`);
* `exp_le_one_div_one_sub` — `exp x ≤ 1/(1-x)` for `0 ≤ x < 1`, obtained **without** power series, by
  applying the log lower bound to `y = 1/(1-x)` and then `exp ∘ log`;
* `exp_le_pow_bound` — `exp x ≤ (1 - x/N)⁻¹ ^ N` for `0 ≤ x < N`, the general rational upper bound
  (raise the `[0,1)` bound for `x/N` to the `N`-th power);
* `log_bounds_rat` — at a **positive rational** `q`, both `log q` bounds are *rational*:
  `1 - 1/q ≤ log q ≤ q - 1`;
* `exp_le_pow_bound_rat` — the same instantiation for `exp` at a rational point;
* `mul_bracket` — how a product of bracketed quantities is bracketed;
* `lagariasRHS_bounds` — the composition that turns rational bounds on `exp` and `log` at `H_n` into
  rational bounds on `H_n + exp(H_n)·log(H_n)`;
* a concrete instance at `n = 2`, with explicit numbers.

## Honest status

The bounds here are **correct but loose** (they are the first-order ones). Deciding the criterion at a
given `n` needs much tighter brackets — the registered task `TaskCertifiedExpLogBounds` in
`Overview.lean` asks for a gap `≤ 2⁻ⁿ`, and that is *not* achieved here. What is achieved is that every
step from "rational bounds on exp/log at `H_n`" to "rational bounds on the right-hand side" is now a
theorem, so the remaining work is purely the tightening of two elementary bounds.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RHProvability.Lagarias

namespace RHProvability

open Real

/-! ## `log`: lower and upper bounds -/

/-- `1 - 1/x ≤ log x` for `x > 0`. Obtained from Mathlib's upper bound
`log y ≤ y - 1` applied at `y = 1/x`, using `log (1/x) = -log x`. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have hinv : (0 : ℝ) < x⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  linarith

/-- **`exp x ≤ 1/(1-x)` for every `x < 1`** (no nonnegativity needed), proved without power series:
the log lower bound gives `1 - (1-x) ≤ log ((1-x)⁻¹)`, i.e. `x ≤ log ((1-x)⁻¹)`, then exponentiate. -/
theorem exp_le_one_div_one_sub {x : ℝ} (h1 : x < 1) :
    Real.exp x ≤ (1 - x)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hinv : (0 : ℝ) < (1 - x)⁻¹ := by positivity
  have hlog : x ≤ Real.log (1 - x)⁻¹ := by
    have h := one_sub_inv_le_log hinv
    rw [inv_inv] at h
    linarith
  calc Real.exp x ≤ Real.exp (Real.log (1 - x)⁻¹) := Real.exp_le_exp.mpr hlog
    _ = (1 - x)⁻¹ := Real.exp_log hinv

/-- **The general rational upper bound for `exp` on `x < N`**: `exp x ≤ ((1 - x/N))⁻¹ ^ N`.

Take the `x < 1` bound at `x/N` and raise to the `N`-th power. For a rational `x` and integer `N` the
right-hand side is rational, so this is a computable certificate. -/
theorem exp_le_pow_bound {x : ℝ} {N : ℕ} (hN : 0 < N) (hxN : x < N) :
    Real.exp x ≤ ((1 - x / N)⁻¹) ^ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hxN' : x / N < 1 := by
    rw [div_lt_one hNpos]
    exact hxN
  have hbase := exp_le_one_div_one_sub hxN'
  have hx : Real.exp x = Real.exp (x / N) ^ N := by
    rw [← Real.exp_nat_mul (x / N) N]
    congr 1
    field_simp
  rw [hx]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hbase N

/-! ## Rational instantiations -/

/-- At a positive rational `q`, `log q` is bracketed by **rationals**: `1 - 1/q ≤ log q ≤ q - 1`. -/
theorem log_bounds_rat {q : ℚ} (hq : 0 < q) :
    ((1 - 1 / q : ℚ) : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ ((q - 1 : ℚ) : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlow : ((1 - 1 / q : ℚ) : ℝ) = 1 - ((q : ℝ))⁻¹ := by
    push_cast
    rw [one_div]
  have hup : ((q - 1 : ℚ) : ℝ) = (q : ℝ) - 1 := by push_cast; ring
  constructor
  · rw [hlow]
    exact one_sub_inv_le_log hqR
  · rw [hup]
    exact Real.log_le_sub_one_of_pos hqR

/-- At a rational `q ≥ 0` and a positive integer `N > q`, `exp q` has a **rational** upper bound. -/
theorem exp_le_pow_bound_rat {q : ℚ} {N : ℕ} (hN : 0 < N) (hqN : q < N) :
    Real.exp (q : ℝ) ≤ ((1 - (q : ℝ) / N)⁻¹) ^ N := by
  have hqNR : (q : ℝ) < (N : ℝ) := by exact_mod_cast hqN
  exact exp_le_pow_bound hN hqNR

/-! ## Bracketing a product, and the right-hand side of Lagarias's inequality -/

/-- Bracket for a product of nonnegative quantities: if `a ≤ X ≤ A` and `b ≤ Y ≤ B` with `a, b ≥ 0`,
then `a·b ≤ X·Y ≤ A·B`. -/
theorem mul_bracket {a X A b Y B : ℝ} (hX : a ≤ X) (hX' : X ≤ A) (hY : b ≤ Y) (hY' : Y ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ X * Y ∧ X * Y ≤ A * B := by
  have hX0 : 0 ≤ X := le_trans ha hX
  have hA0 : 0 ≤ A := le_trans hX0 hX'
  constructor
  · exact mul_le_mul hX hY hb hX0
  · exact mul_le_mul hX' hY' (le_trans hb hY) hA0

/-- **Composition**: rational bounds on `exp (H_n)` and `log (H_n)` give rational-shaped bounds on
`H_n + exp(H_n)·log(H_n)`, i.e. on `lagariasRHS n`. -/
theorem lagariasRHS_bounds {n : ℕ} {a b c d : ℝ}
    (hlog1 : a ≤ Real.log (harmonic n : ℝ)) (hlog2 : Real.log (harmonic n : ℝ) ≤ b)
    (hexp1 : c ≤ Real.exp (harmonic n : ℝ)) (hexp2 : Real.exp (harmonic n : ℝ) ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (harmonic n : ℝ) + c * a ≤ lagariasRHS n ∧
      lagariasRHS n ≤ (harmonic n : ℝ) + d * b := by
  have hbracket := mul_bracket hexp1 hexp2 hlog1 hlog2 hc ha
  unfold lagariasRHS
  constructor <;> linarith [hbracket.1, hbracket.2]

/-! ## A concrete instance: `n = 2` -/

/-- `H_2 = 3/2`, so `log (H_2) ≤ 1/2` and `exp (H_2) ≤ 16` (the `N = 2` power bound is very loose).
This gives the first explicit, machine-checked rational bracket on `lagariasRHS`. -/
theorem lagariasRHS_two_bounds :
    (7 / 3 : ℝ) ≤ lagariasRHS 2 ∧ lagariasRHS 2 ≤ (19 / 2 : ℝ) := by
  have hH : harmonic 2 = 3 / 2 := by
    simp [harmonic, Finset.sum_range_succ]
    norm_num
  have hH2 : (harmonic 2 : ℝ) = 3 / 2 := by rw [hH]; norm_num
  have hlog1 : (1 / 3 : ℝ) ≤ Real.log (harmonic 2 : ℝ) := by
    rw [hH2]
    have hb := (log_bounds_rat (q := 3 / 2) (by norm_num)).1
    norm_num at hb ⊢
    exact hb
  have hlog2 : Real.log (harmonic 2 : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [hH2]
    have hb := (log_bounds_rat (q := 3 / 2) (by norm_num)).2
    norm_num at hb ⊢
    exact hb
  have hexp1 : (5 / 2 : ℝ) ≤ Real.exp (harmonic 2 : ℝ) := by
    rw [hH2]
    have := Real.add_one_le_exp (3 / 2 : ℝ)
    linarith
  have hexp2 : Real.exp (harmonic 2 : ℝ) ≤ 16 := by
    rw [hH2]
    have := exp_le_pow_bound (x := 3 / 2) (N := 2) (by norm_num) (by norm_num)
    norm_num at this ⊢
    exact this
  obtain ⟨hlo, hhi⟩ :=
    lagariasRHS_bounds (n := 2) hlog1 hlog2 hexp1 hexp2 (by norm_num) (by norm_num)
  constructor
  · rw [hH2] at hlo
    norm_num at hlo ⊢
    exact hlo
  · rw [hH2] at hhi
    norm_num at hhi ⊢
    exact hhi

end RHProvability
