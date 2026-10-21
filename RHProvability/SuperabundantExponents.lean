/-
# N2c, the analytic heart: the "swap" inequality behind exponent monotonicity

The structural theorem of Alaoglu–Erdős says that a record number `n = ∏ p_i^{e_i}` (primes
increasing) has **non-increasing exponents** `e_1 ≥ e_2 ≥ …`. The whole difficulty sits in one
comparison: for primes `p < q` and exponents `j < i`, moving a factor from the smaller prime to the
larger one

  `p^i q^j  ↦  p^j q^i`

produces a **smaller** number with a **larger** `σ(m)/m`, so a record cannot have `j < i` across
`p < q`.

Since `σ(p^e)/p^e = ∑_{k ≤ e} (1/p)^k`, that comparison is exactly the statement proved here:

**`sum_range_ratio_lt`** — for `0 < y < x` and `a < b`,

  `(∑_{i ≤ a} x^i)·(∑_{j ≤ b} y^j)  <  (∑_{i ≤ b} x^i)·(∑_{j ≤ a} y^j)`,

i.e. the ratio `R(x) = (∑_{i ≤ b} x^i)/(∑_{i ≤ a} x^i)` is increasing in `x`, so with
`x = 1/p > 1/q = y` the ratio is larger for the smaller prime.

## The proof (and why it is short)

Write `S_x = ∑_{i ≤ a} x^i`, `T_x = ∑_{a < i ≤ b} x^i`, likewise for `y`. Then

  `(S_x+T_x)S_y − S_x(S_y+T_y) = T_x S_y − S_x T_y`,

and expanding both products over the *same* index rectangle `{a < i ≤ b} × {j ≤ a}` pairs each term
`x^i y^j` with `x^j y^i`. The difference is

  `∑_{i>a, j≤a} x^j y^j (x^{i−j} − y^{i−j})`,

a sum of strictly positive terms because `i > a ≥ j` makes `i − j > 0` and `x > y > 0`.

## What else this file does

* `sigmaNat_prime_pow_eq_mul_sum` — the bridge `σ(p^e) = p^e · ∑_{k≤e} (1/p)^k`;
* `sigmaNat_prime_pow_swap` — the prime-level swap, cross-multiplied so that no division appears:
  for primes `p < q` and `j < i`,
  `σ(p^i)σ(q^j)·q^i·p^j > σ(p^j)σ(q^i)·q^j·p^i`, i.e. `p^i q^j ↦ p^j q^i` lowers the number and
  raises `σ(m)/m`.

## What this file does **not** do

It does not yet state the consequence for record numbers ("exponents non-increasing along increasing
primes"), which needs the `p^i q^j m` decomposition with `gcd(m, pq) = 1`.
-/
import RHProvability.SuperabundantEven

namespace RHProvability

open Finset

/-- Splitting a power sum at `a`: the tail `T_x = ∑_{a < i ≤ b} x^i`. -/
theorem sum_range_eq_add_tail {x : ℝ} {a b : ℕ} (hab : a < b) :
    (∑ i ∈ range (b + 1), x ^ i)
      = (∑ i ∈ range (a + 1), x ^ i) + ∑ k ∈ range (b - a), x ^ (a + 1 + k) := by
  have hsplit : b + 1 = (a + 1) + (b - a) := by omega
  rw [hsplit, Finset.sum_range_add]

/-- **The swap inequality.** For `0 < y < x` and `a < b`, the ratio
`(∑_{i≤b} x^i)/(∑_{i≤a} x^i)` is strictly larger than the same ratio at `y`. -/
theorem sum_range_ratio_lt {x y : ℝ} (hy : 0 < y) (hyx : y < x) {a b : ℕ} (hab : a < b) :
    (∑ i ∈ range (a + 1), x ^ i) * (∑ j ∈ range (b + 1), y ^ j)
      < (∑ i ∈ range (b + 1), x ^ i) * (∑ j ∈ range (a + 1), y ^ j) := by
  have hx : 0 < x := lt_trans hy hyx
  -- split both `b`-sums into head + tail
  have hTx : (∑ i ∈ range (b + 1), x ^ i)
      = (∑ i ∈ range (a + 1), x ^ i) + ∑ k ∈ range (b - a), x ^ (a + 1 + k) :=
    sum_range_eq_add_tail hab
  have hTy : (∑ j ∈ range (b + 1), y ^ j)
      = (∑ j ∈ range (a + 1), y ^ j) + ∑ k ∈ range (b - a), y ^ (a + 1 + k) :=
    sum_range_eq_add_tail hab
  -- the term-wise comparison on the common index rectangle
  have hinner : ∀ k ∈ range (b - a),
      0 < (∑ j ∈ range (a + 1), x ^ (a + 1 + k) * y ^ j)
          - (∑ j ∈ range (a + 1), x ^ j * y ^ (a + 1 + k)) := by
    intro k hk
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_pos (fun j hj => ?_) ⟨0, Finset.mem_range.mpr (by omega)⟩
    set m := a + 1 + k
    have hjm : j < m := by
      have := Finset.mem_range.mp hj
      omega
    have hpow : y ^ (m - j) < x ^ (m - j) :=
      pow_lt_pow_left₀ hyx (le_of_lt hy) (by omega)
    have hpos : 0 < x ^ j * y ^ j := by positivity
    have hL : x ^ j * y ^ j * y ^ (m - j) = x ^ j * y ^ m := by
      rw [mul_assoc, ← pow_add, show j + (m - j) = m by omega]
    have hR : x ^ j * y ^ j * x ^ (m - j) = x ^ m * y ^ j := by
      calc x ^ j * y ^ j * x ^ (m - j) = x ^ j * x ^ (m - j) * y ^ j := by ring
        _ = x ^ m * y ^ j := by rw [← pow_add, show j + (m - j) = m by omega]
    have hkey : x ^ j * y ^ m < x ^ m * y ^ j := by
      rw [← hL, ← hR]
      exact mul_lt_mul_of_pos_left hpow hpos
    linarith
  -- the tail comparison, as a positive sum of term differences
  have hkey : (∑ k ∈ range (b - a), ∑ j ∈ range (a + 1), x ^ j * y ^ (a + 1 + k))
      < (∑ k ∈ range (b - a), ∑ j ∈ range (a + 1), x ^ (a + 1 + k) * y ^ j) := by
    have hpos : 0 < (∑ k ∈ range (b - a), ∑ j ∈ range (a + 1), x ^ (a + 1 + k) * y ^ j)
        - (∑ k ∈ range (b - a), ∑ j ∈ range (a + 1), x ^ j * y ^ (a + 1 + k)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_pos hinner ⟨0, Finset.mem_range.mpr (by omega)⟩
    linarith
  -- assemble the two products
  have hmul1 : (∑ i ∈ range (a + 1), x ^ i) * (∑ j ∈ range (b + 1), y ^ j)
      = (∑ i ∈ range (a + 1), x ^ i) * (∑ j ∈ range (a + 1), y ^ j)
        + (∑ i ∈ range (a + 1), x ^ i) * (∑ k ∈ range (b - a), y ^ (a + 1 + k)) := by
    rw [hTy, mul_add]
  have hmul2 : (∑ i ∈ range (b + 1), x ^ i) * (∑ j ∈ range (a + 1), y ^ j)
      = (∑ i ∈ range (a + 1), x ^ i) * (∑ j ∈ range (a + 1), y ^ j)
        + (∑ k ∈ range (b - a), x ^ (a + 1 + k)) * (∑ j ∈ range (a + 1), y ^ j) := by
    rw [hTx, add_mul]
  rw [hmul1, hmul2]
  have hcross : (∑ i ∈ range (a + 1), x ^ i) * (∑ k ∈ range (b - a), y ^ (a + 1 + k))
      = ∑ k ∈ range (b - a), ∑ j ∈ range (a + 1), x ^ j * y ^ (a + 1 + k) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  have hcross2 : (∑ k ∈ range (b - a), x ^ (a + 1 + k)) * (∑ j ∈ range (a + 1), y ^ j)
      = ∑ k ∈ range (b - a), ∑ j ∈ range (a + 1), x ^ (a + 1 + k) * y ^ j := by
    rw [Finset.sum_mul_sum]
  rw [hcross, hcross2]
  linarith

/-! ## The `σ` bridge -/

/-- **`σ(p^e) = p^e · ∑_{k≤e} (1/p)^k`**, i.e. `σ(p^e)/p^e = ∑_{k≤e} p^{-k}`. Induction on `e`
using `σ(p^{e+1}) = σ(p^e) + p^{e+1}`. -/
theorem sigmaNat_prime_pow_eq_mul_sum {p e : ℕ} (hp : p.Prime) :
    (sigmaNat (p ^ e) : ℝ)
      = (p : ℝ) ^ e * ∑ k ∈ Finset.range (e + 1), (1 / (p : ℝ)) ^ k := by
  induction e with
  | zero => simp [sigmaNat_one]
  | succ e ih =>
    have hrec := sigmaNat_prime_pow_eq_add hp (Nat.succ_le_succ (Nat.zero_le e))
    have hsub : (e + 1) - 1 = e := by omega
    rw [hsub] at hrec
    have hS : (∑ k ∈ Finset.range (e + 1 + 1), (1 / (p : ℝ)) ^ k)
        = 1 + (1 / (p : ℝ)) * ∑ k ∈ Finset.range (e + 1), (1 / (p : ℝ)) ^ k := by
      have step : (∑ k ∈ Finset.range (e + 1 + 1), (1 / (p : ℝ)) ^ k)
          = (∑ k ∈ Finset.range (e + 1), (1 / (p : ℝ)) ^ (k + 1)) + (1 / (p : ℝ)) ^ 0 :=
        Finset.sum_range_succ' _ _
      rw [step, pow_zero, add_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun x _ => by rw [pow_succ]; ring)
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hS]
    calc (sigmaNat (p ^ (e + 1)) : ℝ)
        = (sigmaNat (p ^ e) : ℝ) + (p : ℝ) ^ (e + 1) := by
          rw [hrec]; push_cast; simp only [Nat.succ_eq_add_one]
      _ = (p : ℝ) ^ e * (∑ k ∈ Finset.range (e + 1), (1 / (p : ℝ)) ^ k) + (p : ℝ) ^ (e + 1) := by
          rw [ih]
      _ = (p : ℝ) ^ (e + 1)
            * (1 + (1 / (p : ℝ)) * ∑ k ∈ Finset.range (e + 1), (1 / (p : ℝ)) ^ k) := by
          field_simp
          ring

/-! ## The prime-level swap -/

/-- **Swapping exponents across two primes.** For primes `p < q` and `j < i`,

`σ(p^i)σ(q^j)·q^i·p^j > σ(p^j)σ(q^i)·q^j·p^i`,

which is `σ(p^i)/p^i · σ(q^j)/q^j > σ(p^j)/p^j · σ(q^i)/q^i` cross-multiplied. So the number
`p^i q^j` is **larger** than `p^j q^i` while its `σ(m)/m` is **smaller**. -/
theorem sigmaNat_prime_pow_swap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    {i j : ℕ} (hji : j < i) :
    (sigmaNat (p ^ j) : ℝ) * (sigmaNat (q ^ i) : ℝ) * (q : ℝ) ^ j * (p : ℝ) ^ i
      < (sigmaNat (p ^ i) : ℝ) * (sigmaNat (q ^ j) : ℝ) * (q : ℝ) ^ i * (p : ℝ) ^ j := by
  have hp1 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hq1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hlt : (1 : ℝ) / (q : ℝ) < 1 / (p : ℝ) := by
    rw [one_div_lt_one_div hq1 hp1]
    exact_mod_cast hpq
  have hy : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  -- the abstract inequality with `x = 1/p`, `y = 1/q`, `a = j`, `b = i`
  have habs := sum_range_ratio_lt hy hlt hji
  -- rewrite both sides with the `σ` bridge
  rw [sigmaNat_prime_pow_eq_mul_sum hp (e := j), sigmaNat_prime_pow_eq_mul_sum hq (e := i),
    sigmaNat_prime_pow_eq_mul_sum hp (e := i), sigmaNat_prime_pow_eq_mul_sum hq (e := j)]
  -- both sides are `p^{i+j} q^{i+j}` times the corresponding power sums
  have hpq_pos : (0 : ℝ) < (p : ℝ) ^ (i + j) * (q : ℝ) ^ (i + j) := by positivity
  have expand : ∀ a b : ℝ,
      (p : ℝ) ^ j * a * ((q : ℝ) ^ i * b) * (q : ℝ) ^ j * (p : ℝ) ^ i
        = ((p : ℝ) ^ (i + j) * (q : ℝ) ^ (i + j)) * (a * b) := by
    intro a b
    rw [show (p : ℝ) ^ (i + j) = (p : ℝ) ^ i * (p : ℝ) ^ j by rw [pow_add],
      show (q : ℝ) ^ (i + j) = (q : ℝ) ^ i * (q : ℝ) ^ j by rw [pow_add]]
    ring
  have expand2 : ∀ a b : ℝ,
      (p : ℝ) ^ i * a * ((q : ℝ) ^ j * b) * (q : ℝ) ^ i * (p : ℝ) ^ j
        = ((p : ℝ) ^ (i + j) * (q : ℝ) ^ (i + j)) * (a * b) := by
    intro a b
    rw [show (p : ℝ) ^ (i + j) = (p : ℝ) ^ i * (p : ℝ) ^ j by rw [pow_add],
      show (q : ℝ) ^ (i + j) = (q : ℝ) ^ i * (q : ℝ) ^ j by rw [pow_add]]
    ring
  have H : ((p : ℝ) ^ (i + j) * (q : ℝ) ^ (i + j))
        * ((∑ k ∈ Finset.range (j + 1), (1 / (p : ℝ)) ^ k)
            * (∑ k ∈ Finset.range (i + 1), (1 / (q : ℝ)) ^ k))
      < ((p : ℝ) ^ (i + j) * (q : ℝ) ^ (i + j))
        * ((∑ k ∈ Finset.range (i + 1), (1 / (p : ℝ)) ^ k)
            * (∑ k ∈ Finset.range (j + 1), (1 / (q : ℝ)) ^ k)) := by
    exact mul_lt_mul_of_pos_left habs hpq_pos
  -- transfer `H` to the goal via the two expansions
  have e1 := expand (∑ k ∈ Finset.range (j + 1), (1 / (p : ℝ)) ^ k)
    (∑ k ∈ Finset.range (i + 1), (1 / (q : ℝ)) ^ k)
  have e2 := expand2 (∑ k ∈ Finset.range (i + 1), (1 / (p : ℝ)) ^ k)
    (∑ k ∈ Finset.range (j + 1), (1 / (q : ℝ)) ^ k)
  rw [e1, e2]
  exact H

end RHProvability
