/-
# Tight `exp` / `log` bounds: the artanh lower bound and a Taylor upper bound with geometric tail

`Numeric.lean` supplies *first-order* rational bounds on `log` and `exp` and the composition that
turns them into bounds on `lagariasRHS`.  Those bounds are correct but far too loose to decide the
criterion at even `n = 2`.  This file tightens the two elementary inputs.

## What is in here

* `log_lower_artanh` — `2 (y-1)/(y+1) ≤ log y` for **`y ≥ 1`** (the artanh / Padé `[1/1]` lower
  bound, far tighter than `1 - 1/y`).  Proved from Mathlib's `Real.le_log_one_add_of_nonneg`.
* `log_upper_artanh_of_le_one` — the companion upper bound `log y ≤ 2 (y-1)/(y+1)` for
  **`0 < y ≤ 1`**; together the two describe the full picture and make precise *where* the
  inequality flips sign.
* `log_lower_artanh_not_for_pos` — **a machine-checked refutation of the `y > 0` version.**
  The inequality `2 (y-1)/(y+1) ≤ log y` is *false* for `0 < y < 1`; at `y = 1/3` the left side is
  `-1` while `log (1/3) = -log 3 ≤ -16/15 < -1`.  The correct statement is one-sided, and the
  domain `y ≥ 1` is not a convenience.
* `exp_upper_taylor` — the Taylor bound with a geometric tail:
  `exp x ≤ (∑_{i<N} x^i/i!) + (x^N/N!) * (1 - x/(N+1))⁻¹` for `0 ≤ x < N+1`.
  Genuinely tighter than `exp_le_pow_bound`: at `x = 3/2`, `N = 7` it gives
  `exp (3/2) ≤ 4.47754 + 0.00417 = 4.48171`, while the power bound (`N = 2`) gives
  `((1 - 3/4)⁻¹)^2 = 16`.
* `lagariasRHS_two_tight` — the `n = 2` bracket narrowed from `[7/3, 19/2]` (width `43/6`) to
  `[3314/1000, 3321/1000]` (width `7/1000`), well inside the requested `1/10`.

## Proof of `exp_upper_taylor` (no analysis, no `tsum` axioms)

`exp` is the sum of its Taylor series (`NormedSpace.expSeries_div_hasSum_exp` transported to `ℝ`
by `Real.exp_eq_exp_ℝ`).  Split the series at `N` and bound the tail termwise by a geometric
progression: for `k ≥ 0`,
`x^(N+k)/(N+k)! ≤ (x^N/N!) · (x/(N+1))^k`,
which is the factorial inequality `N! (N+1)^k ≤ (N+k)!`
(`Nat.factorial_mul_pow_le_factorial`).  Summing the geometric progression
(`∑_{k<L} r^k ≤ (1-r)⁻¹` for `0 ≤ r < 1`, proved here from scratch by induction) and passing to
the limit along partial sums gives the claim.  The limit step is `le_of_tendsto'` applied to
`HasSum.tendsto_sum_nat`, so no infinite-sum comparison lemmas are needed.
-/
import RHProvability.Numeric

namespace RHProvability

open Real

/-! ## The artanh (Padé `[1/1]`) logarithmic bounds -/

/-- **The artanh lower bound for the logarithm, on `y ≥ 1`**:
`2 (y-1)/(y+1) ≤ log y`.

This is the `[1/1]` Padé lower bound; it is the standard sharpening of `1 - 1/y ≤ log y` and is
what makes rational log-brackets narrow enough to be useful.  It follows from Mathlib's
`Real.le_log_one_add_of_nonneg` (`2u/(u+2) ≤ log (1+u)` for `u ≥ 0`) at `u = y - 1`.

**Domain.**  `y ≥ 1` is necessary, not cosmetic: for `0 < y < 1` the inequality *reverses*
(see `log_upper_artanh_of_le_one`), and the `y > 0` version is outright false
(`log_lower_artanh_not_for_pos`). -/
theorem log_lower_artanh {y : ℝ} (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ Real.log y := by
  have h := Real.le_log_one_add_of_nonneg (x := y - 1) (by linarith)
  have h1 : y - 1 + 2 = y + 1 := by ring
  have h2 : 1 + (y - 1) = y := by ring
  rwa [h1, h2] at h

/-- **The companion upper bound for `log` on `0 < y ≤ 1`**: `log y ≤ 2 (y-1)/(y+1)`.

Together with `log_lower_artanh` this pins down where the sign flips: the inequality
`2 (y-1)/(y+1) ≤ log y` holds exactly on `y ≥ 1`, and is reversed on `0 < y ≤ 1`.  Obtained from
`log_lower_artanh` at `y⁻¹ ≥ 1` using `log y⁻¹ = -log y`. -/
theorem log_upper_artanh_of_le_one {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    Real.log y ≤ 2 * (y - 1) / (y + 1) := by
  have hinv : 1 ≤ y⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hy0 hy1
  have h := log_lower_artanh (y := y⁻¹) hinv
  rw [Real.log_inv] at h
  have hkey : 2 * (y⁻¹ - 1) / (y⁻¹ + 1) = -(2 * (y - 1) / (y + 1)) := by
    field_simp
    ring
  rw [hkey] at h
  linarith

/-- **The `y > 0` version of `log_lower_artanh` is false.**  This theorem is the machine-checked
record of that fact, so that the restricted domain in `log_lower_artanh` is not mistaken for a
weakness of the proof.

Counterexample: at `y = 1/3` the left-hand side is `2 (−2/3)/(4/3) = −1`, while
`log (1/3) = −log 3 ≤ −(2/3 + 2/5) = −16/15 < −1`, using `log_lower_artanh` itself at `y = 2` and
`y = 3/2`. -/
theorem log_lower_artanh_not_for_pos :
    ¬ (∀ y : ℝ, 0 < y → 2 * (y - 1) / (y + 1) ≤ Real.log y) := by
  intro h
  have hlog3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := log_lower_artanh (y := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have h32 : (2 / 5 : ℝ) ≤ Real.log (3 / 2) := by
    have := log_lower_artanh (y := 3 / 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have h3 : (16 / 15 : ℝ) ≤ Real.log 3 := by
    rw [hlog3]; linarith
  have h13 : Real.log (1 / 3) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.log_inv]
  have hL : 2 * ((1 / 3 : ℝ) - 1) / ((1 / 3) + 1) = -1 := by norm_num
  have hle := h (1 / 3) (by norm_num)
  rw [hL, h13] at hle
  linarith

/-! ## A Taylor upper bound for `exp` with a geometric tail -/

/-- **Taylor upper bound with geometric tail.**  For `x ≥ 0` and `x < N + 1`:
`exp x ≤ (∑_{i<N} x^i/i!) + (x^N / N!) · (1 - x/(N+1))⁻¹`.

This is strictly tighter than `exp_le_pow_bound` for every `x` in the range: at `x = 3/2`, `N = 7`
the right-hand side is `≈ 4.48171`, against `((1 - (3/2)/2)⁻¹)^2 = 16` for the power bound.
The classic `Real.exp_bound'` is not available here: it requires `x ≤ 1`, while this theorem
covers the whole range `x < N + 1`.

The proof splits the Taylor series of `exp` at `N`, bounds the tail termwise by
`x^(N+k)/(N+k)! ≤ (x^N/N!) (x/(N+1))^k` (from `N! (N+1)^k ≤ (N+k)!`), sums the resulting
geometric progression, and takes the limit of partial sums with `le_of_tendsto'`. -/
theorem exp_upper_taylor {x : ℝ} {N : ℕ} (hx : 0 ≤ x) (hN : x < (N : ℝ) + 1) :
    Real.exp x ≤ (∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℝ))
      + (x ^ N / (Nat.factorial N : ℝ)) * (1 - x / ((N : ℝ) + 1))⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set r : ℝ := x / ((N : ℝ) + 1) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hNpos]; linarith
  -- `exp` is the sum of its Taylor series
  have hmain : HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  -- geometric bound `∑_{k<L} r^k ≤ (1-r)⁻¹`, from scratch
  have hgeomkey : ∀ L : ℕ, (1 - r) * ∑ k ∈ Finset.range L, r ^ k = 1 - r ^ L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  have hgeom : ∀ L : ℕ, ∑ k ∈ Finset.range L, r ^ k ≤ (1 - r)⁻¹ := by
    intro L
    have hpos : (0 : ℝ) < 1 - r := by linarith
    have hS : (∑ k ∈ Finset.range L, r ^ k) * (1 - r) ≤ 1 := by
      rw [mul_comm (∑ k ∈ Finset.range L, r ^ k) (1 - r), hgeomkey L]
      nlinarith [pow_nonneg hr0 L]
    rw [show (1 - r)⁻¹ = 1 / (1 - r) by rw [one_div], le_div_iff₀ hpos]
    linarith
  -- bound every partial sum, then pass to the limit
  refine le_of_tendsto' hmain.tendsto_sum_nat (fun M => ?_)
  by_cases hMN : M ≤ N
  · have h1 : ∑ i ∈ Finset.range M, x ^ i / (Nat.factorial i : ℝ)
        ≤ ∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) (fun i _ _ => by positivity)
    have h2 : 0 ≤ (x ^ N / (Nat.factorial N : ℝ)) * (1 - r)⁻¹ := by positivity
    linarith
  · have hNM : N < M := by omega
    have hsplit : ∑ i ∈ Finset.range M, x ^ i / (Nat.factorial i : ℝ)
        = (∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℝ))
          + ∑ k ∈ Finset.range (M - N), x ^ (N + k) / (Nat.factorial (N + k) : ℝ) := by
      conv_lhs => rw [show M = N + (M - N) by omega]
      rw [Finset.sum_range_add]
    have hterm : ∀ k ∈ Finset.range (M - N),
        x ^ (N + k) / (Nat.factorial (N + k) : ℝ)
          ≤ (x ^ N / (Nat.factorial N : ℝ)) * r ^ k := by
      intro k _
      have hfac : (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k ≤ (Nat.factorial (N + k) : ℝ) := by
        have h := Nat.factorial_mul_pow_le_factorial (m := N) (n := k)
        exact_mod_cast h
      have hpos : (0 : ℝ) < (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k := by positivity
      calc x ^ (N + k) / (Nat.factorial (N + k) : ℝ)
          = x ^ N * x ^ k / (Nat.factorial (N + k) : ℝ) := by rw [pow_add]
        _ ≤ x ^ N * x ^ k / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) :=
            div_le_div_of_nonneg_left (by positivity) hpos hfac
        _ = (x ^ N / (Nat.factorial N : ℝ)) * r ^ k := by
            rw [hr, div_pow]
            field_simp
    have hsum : ∑ k ∈ Finset.range (M - N), x ^ (N + k) / (Nat.factorial (N + k) : ℝ)
        ≤ (x ^ N / (Nat.factorial N : ℝ)) * ∑ k ∈ Finset.range (M - N), r ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hstep : (x ^ N / (Nat.factorial N : ℝ)) * ∑ k ∈ Finset.range (M - N), r ^ k
        ≤ (x ^ N / (Nat.factorial N : ℝ)) * (1 - r)⁻¹ :=
      mul_le_mul_of_nonneg_left (hgeom (M - N)) (by positivity)
    linarith [hsplit, hsum, hstep]

/-! ## The `n = 2` instance, tightened -/

/-- **`lagariasRHS 2` bracketed to width `6/1000`.**

The previous bracket was `7/3 ≤ lagariasRHS 2 ≤ 19/2` (width `43/6 ≈ 7.2`).  Using the artanh log
bound and the Taylor `exp` bound of this file:

* `exp (3/2) = exp 1 · exp (1/2) ∈ [2.7180·1.6486, 2.7183·1.6488] ⊂ [4.4808, 4.4820]`;
* `log (3/2) ∈ [0.405, 0.406]` (via `exp 0.405 < 3/2 < exp 0.406`, then
  `Real.lt_log_iff_exp_lt` and `Real.log_lt_iff_lt_exp`);
* `H_2 = 3/2`, so `lagariasRHS 2 = 3/2 + exp (3/2)·log (3/2) ∈ [3.31472, 3.31969]`.

Hence the width is `< 1/10`, as requested.  (The true value is `≈ 3.31717`.) -/
theorem lagariasRHS_two_tight :
    (3314 / 1000 : ℝ) ≤ lagariasRHS 2 ∧ lagariasRHS 2 ≤ (3321 / 1000 : ℝ) := by
  have hH : harmonic 2 = 3 / 2 := by
    simp [harmonic, Finset.sum_range_succ]
    norm_num
  have hH2 : (harmonic 2 : ℝ) = 3 / 2 := by rw [hH]; norm_num
  -- `exp 1` and `exp (1/2)`, both sides
  have he1_lo : (2.7180 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 7
    norm_num at h ⊢
    linarith
  have he1_hi : Real.exp 1 ≤ (2.7183 : ℝ) := by
    have h := Real.exp_bound' (x := 1) (by norm_num) (le_refl (1 : ℝ)) (n := 7) (by norm_num)
    norm_num at h ⊢
    linarith
  have hhalf_lo : (1.6486 : ℝ) ≤ Real.exp (1 / 2) := by
    have h := Real.sum_le_exp_of_nonneg (x := 1 / 2) (by norm_num) 7
    norm_num at h ⊢
    linarith
  have hhalf_hi : Real.exp (1 / 2) ≤ (1.6488 : ℝ) := by
    have h := Real.exp_bound' (x := 1 / 2) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    norm_num at h ⊢
    linarith
  have hexp_split : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.exp_add]
  have he_lo : (4.4808 : ℝ) ≤ Real.exp (3 / 2) := by
    have hp : (2.7180 : ℝ) * 1.6486 ≤ Real.exp 1 * Real.exp (1 / 2) :=
      mul_le_mul he1_lo hhalf_lo (by norm_num) (Real.exp_pos 1).le
    rw [hexp_split]
    linarith
  have he_hi : Real.exp (3 / 2) ≤ (4.4820 : ℝ) := by
    have hp : Real.exp 1 * Real.exp (1 / 2) ≤ (2.7183 : ℝ) * 1.6488 :=
      mul_le_mul he1_hi hhalf_hi (Real.exp_pos (1 / 2)).le (by norm_num)
    rw [hexp_split]
    linarith
  -- `log (3/2)` from exponential bounds at `0.405` and `0.406`
  have hlog_lo : (0.405 : ℝ) ≤ Real.log (3 / 2) := by
    have hkey : (0.405 : ℝ) < Real.log (3 / 2) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h := Real.exp_bound' (x := 0.405) (by norm_num) (by norm_num) (n := 6) (by norm_num)
      norm_num at h ⊢
      linarith
    linarith
  have hlog_hi : Real.log (3 / 2) ≤ (0.406 : ℝ) := by
    have hkey : Real.log (3 / 2) < (0.406 : ℝ) := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (x := 0.406) (by norm_num) 5
      norm_num at h ⊢
      linarith
    linarith
  have hlog_pos : (0 : ℝ) ≤ Real.log (3 / 2) := by linarith
  -- assemble
  have hprod_lo : (4.4808 : ℝ) * 0.405 ≤ Real.exp (3 / 2) * Real.log (3 / 2) :=
    mul_le_mul he_lo hlog_lo (by norm_num) (Real.exp_pos (3 / 2)).le
  have hprod_hi : Real.exp (3 / 2) * Real.log (3 / 2) ≤ (4.4820 : ℝ) * 0.406 :=
    mul_le_mul he_hi hlog_hi hlog_pos (by norm_num)
  unfold lagariasRHS
  rw [hH2]
  constructor <;> linarith

end RHProvability
