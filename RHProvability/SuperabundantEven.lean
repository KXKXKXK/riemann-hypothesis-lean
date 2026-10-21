/-
# N2b, first structural layer: record numbers above `1` are even

This file proves the first structural fact about the record numbers of `σ(m)/m`:

**`isSuperabundant_even`** — if `n > 1` is a record (no smaller positive `m` has `σ(m)/m` at least
as large), then `n` is even.

This is the classical Alaoglu–Erdős (1944) observation; it is what forces every superabundant number
above `1` to be divisible by `2`, hence to be built from `2` together with odd primes. Mathlib has
neither the notion nor the fact.

## The argument

Suppose `n > 1` is odd and a record. Let `q` be a prime divisor of `n` (then `q ≥ 3`) and write
`n = q^a · r` with `q ∤ r` and `a ≥ 1`. Put `m = 2·q^{a-1}·r = 2n/q`, so `m < n`. Because `q` and
`r` are odd, `2`, `q^{a-1}`, `r` are pairwise coprime, so multiplicativity of `σ` gives

  `σ(m) = 3 σ(q^{a-1}) σ(r)`,  `σ(n) = σ(q^a) σ(r)`.

The record property at `m < n` forbids `σ(m)/m < σ(n)/n`, i.e. gives `σ(m)·n ≥ σ(n)·m`; substituting
and cancelling `σ(r)·r·q^{a-1} > 0` leaves

  `3q σ(q^{a-1}) ≥ 2 σ(q^a)`.

But `σ(q^a) = σ(q^{a-1}) + q^a` and `σ(q^{a-1}) ≥ q^{a-1}`, so

  `2 σ(q^a) = 2σ(q^{a-1}) + 2q^a ≤ (3q-2) σ(q^{a-1}) < 3q σ(q^{a-1})`,

the last step because `q^{a-1}(q-2) > 0` for `q ≥ 3`. Contradiction.

## A caution about the threshold

This theorem is about the **threshold-free** notion `IsSuperabundant`. It does **not** transfer to the
parametrized `SuperabundantFrom N₀` with `N₀ ≥ 3` by this argument, because the comparison number
`2n/q` can fall *below* `N₀`: then the record condition says nothing about it. So the honest statement
is ``threshold-free records above 1 are even'', not ``every `SuperabundantFrom N₀` number is even''.

## What this file does **not** do

It does not prove that records exist, that they are sparse, that their prime exponents are
non-increasing, or that they are `colossally abundant`. Those are further Alaoglu–Erdős layers and
none of them is needed for the quantifier reduction in `Superabundant.lean`.
-/
import RHProvability.Superabundant

namespace RHProvability

/-- `IsSuperabundant n` (no threshold): no smaller positive integer has `σ(m)/m` at least as large as
`n`'s. Cross-multiplied, so no division appears. -/
def IsSuperabundant (n : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m < n → (sigmaNat m : ℝ) * (n : ℝ) < (sigmaNat n : ℝ) * (m : ℝ)

/-- The threshold-free notion is the parametrized one at `N₀ = 1`. -/
theorem isSuperabundant_iff_superabundantFrom_one {n : ℕ} (hn : 1 ≤ n) :
    IsSuperabundant n ↔ SuperabundantFrom 1 n := by
  unfold IsSuperabundant SuperabundantFrom
  constructor
  · intro h
    exact ⟨hn, fun m hm hmn => h m (by omega) hmn⟩
  · rintro ⟨_, h⟩ m hm hmn
    exact h m (by omega) hmn

/-! ## `σ` on coprime factors and on prime powers -/

/-- `σ` is multiplicative on coprime factors (transferred from `IsMultiplicative (σ 1)`). -/
theorem sigmaNat_mul_of_coprime {a b : ℕ} (hab : a.Coprime b) :
    sigmaNat (a * b) = sigmaNat a * sigmaNat b := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hab
  simpa [sigmaNat_eq_sigma_one] using h

/-- `σ(p^i) = ∑_{j ≤ i} p^j` for a prime `p`. -/
theorem sigmaNat_prime_pow {p i : ℕ} (hp : p.Prime) :
    sigmaNat (p ^ i) = ∑ k ∈ Finset.range (i + 1), p ^ k := by
  rw [sigmaNat_eq_sigma_one, ArithmeticFunction.sigma_one_apply_prime_pow hp]

/-- `σ(p^i) = σ(p^{i-1}) + p^i` for a prime `p` and `i ≥ 1`: the divisors of `p^i` are those of
`p^{i-1}` together with `p^i` itself. -/
theorem sigmaNat_prime_pow_eq_add {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    sigmaNat (p ^ i) = sigmaNat (p ^ (i - 1)) + p ^ i := by
  have h1 : sigmaNat (p ^ i) = (∑ k ∈ Finset.range i, p ^ k) + p ^ i := by
    rw [sigmaNat_prime_pow hp, Finset.sum_range_succ]
  have h2 : sigmaNat (p ^ (i - 1)) = ∑ k ∈ Finset.range i, p ^ k := by
    rw [sigmaNat_prime_pow hp, show i - 1 + 1 = i by omega]
  rw [h1, h2]

/-- **The prime-power inequality.** For a prime `p ≥ 3` and `i ≥ 1`,
`2 σ(p^i) < 3 p σ(p^{i-1})` — the arithmetic content of "removing one factor `p` and inserting a
factor `2` increases `σ(m)/m`". -/
theorem two_mul_sigmaNat_prime_pow_lt {p i : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hi : 1 ≤ i) :
    2 * (sigmaNat (p ^ i) : ℝ) < 3 * (p : ℝ) * (sigmaNat (p ^ (i - 1)) : ℝ) := by
  set S : ℝ := (sigmaNat (p ^ (i - 1)) : ℝ) with hS
  have hSpos : 0 < S := by
    rw [hS]
    exact_mod_cast sigmaNat_pos (by positivity : p ^ (i - 1) ≠ 0)
  have hge : ((p : ℝ) ^ (i - 1)) ≤ S := by
    rw [hS]
    exact_mod_cast le_sigmaNat (by positivity : p ^ (i - 1) ≠ 0)
  have hsplit : ((p : ℝ) ^ i) = (p : ℝ) * (p : ℝ) ^ (i - 1) := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega]
    rw [pow_succ']
  have hrec : (sigmaNat (p ^ i) : ℝ) = S + (p : ℝ) ^ i := by
    rw [sigmaNat_prime_pow_eq_add hp hi, hS]
    push_cast
    ring
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hpP : 2 * (p : ℝ) ^ i ≤ 2 * (p : ℝ) * S := by
    rw [hsplit]
    nlinarith [hge]
  have h3 : 2 * (p : ℝ) * S + 2 * S < 3 * (p : ℝ) * S := by nlinarith [hSpos, hpR]
  rw [hrec]
  nlinarith [hpP, h3]

/-! ## The main theorem -/

/-- **Record numbers above `1` are even** (Alaoglu–Erdős 1944, first structural layer). -/
theorem isSuperabundant_even {n : ℕ} (h : IsSuperabundant n) (hn : 1 < n) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exfalso
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hq2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := ho
      obtain ⟨c, hc⟩ := hqdvd
      omega
    have hq3 : 3 ≤ q := by
      have := hq.two_le
      omega
    have hq_odd : Odd q := (hq.eq_two_or_odd').resolve_left hq2
    -- write `n = q^a · r` with `q ∤ r`, `a ≥ 1`
    obtain ⟨a, r, hr, hn_eq⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) q hq.ne_one
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · rw [h0, mul_zero] at hn_eq
        omega
      · exact hpos
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · exfalso
        rw [h0, pow_zero, one_mul] at hn_eq
        rw [hn_eq] at hqdvd
        exact hr hqdvd
      · exact hpos
    -- `r` and hence `s = q^{a-1} r` are odd
    have hr_odd : Odd r := by
      rcases Nat.even_or_odd r with hre | hro
      · exfalso
        obtain ⟨k, hk⟩ := hre
        obtain ⟨j, hj⟩ := ho
        have h2n : n = 2 * (q ^ a * k) := by rw [hn_eq, hk]; ring
        omega
      · exact hro
    set s : ℕ := q ^ (a - 1) * r with hs
    have hs_pos : 0 < s := by
      rw [hs]
      exact Nat.mul_pos (by positivity) hr_pos
    have hs_odd : Odd s := by
      rw [hs]
      exact Odd.mul hq_odd.pow hr_odd
    have hn_eq2 : n = q * s := by
      have hqpow : q ^ a = q * q ^ (a - 1) := by
        conv_lhs => rw [show a = (a - 1) + 1 by omega]
        rw [pow_succ']
      rw [hn_eq, hs, hqpow]
      ring
    -- `m = 2s < n`, so the record property applies
    have h2s_lt : 2 * s < n := by
      rw [hn_eq2]
      exact Nat.mul_lt_mul_of_pos_right (by omega : 2 < q) hs_pos
    have hmain := h (2 * s) (by positivity) h2s_lt
    -- multiplicativity: `σ(2s) = 3 σ(q^{a-1}) σ(r)` and `σ(n) = σ(q^a) σ(r)`
    have hqcr : Nat.Coprime q r := (hq.coprime_iff_not_dvd).mpr hr
    have hqr : Nat.Coprime (q ^ (a - 1)) r := Nat.Coprime.pow_left _ hqcr
    have hqar : Nat.Coprime (q ^ a) r := Nat.Coprime.pow_left _ hqcr
    have h2s : Nat.Coprime 2 s := Nat.coprime_two_left.mpr hs_odd
    have hsigma_s : sigmaNat s = sigmaNat (q ^ (a - 1)) * sigmaNat r := by
      rw [hs]
      exact sigmaNat_mul_of_coprime hqr
    have hsigma_2s : sigmaNat (2 * s) = 3 * sigmaNat s := by
      rw [sigmaNat_mul_of_coprime h2s, sigmaNat_two]
    have hsigma_n : sigmaNat n = sigmaNat (q ^ a) * sigmaNat r := by
      rw [hn_eq]
      exact sigmaNat_mul_of_coprime hqar
    -- real bookkeeping
    set A : ℝ := (sigmaNat (q ^ (a - 1)) : ℝ) with hA
    set B : ℝ := (sigmaNat (q ^ a) : ℝ) with hB
    set C : ℝ := (sigmaNat r : ℝ) with hC
    set Q : ℝ := (q : ℝ) with hQ
    set R : ℝ := (r : ℝ) with hR
    set P : ℝ := Q ^ (a - 1) with hPdef
    have hQpos : 0 < Q := by rw [hQ]; exact_mod_cast hq.pos
    have hRpos : 0 < R := by rw [hR]; exact_mod_cast hr_pos
    have hCpos : 0 < C := by
      rw [hC]
      exact_mod_cast sigmaNat_pos (by omega : r ≠ 0)
    have hcast_s : (s : ℝ) = P * R := by
      rw [hs, hPdef, hQ, hR]
      push_cast
      ring
    have hcast_n : (n : ℝ) = Q ^ a * R := by
      rw [hn_eq, hQ, hR]
      push_cast
      ring
    have hQa : Q ^ a = Q * P := by
      rw [hPdef]
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ']
    -- substitute into the record inequality
    rw [hsigma_2s, hsigma_s, hsigma_n] at hmain
    push_cast at hmain
    rw [← hA, ← hB, ← hC, hcast_n, hcast_s] at hmain
    have hmain' : (3 * A * C) * (Q ^ a * R) < (B * C) * (2 * (P * R)) := by
      ring_nf at hmain ⊢
      linarith
    -- cancel `C·P·R > 0` to get `3 Q A < 2 B`
    have hkey : 3 * Q * A < 2 * B := by
      have hpos : 0 < C * P * R := by
        have hPpos : 0 < P := by rw [hPdef]; positivity
        positivity
      have hstep : (3 * Q * A) * (C * P * R) < (2 * B) * (C * P * R) := by
        rw [hQa] at hmain'
        ring_nf at hmain' ⊢
        linarith
      exact lt_of_mul_lt_mul_right hstep (le_of_lt hpos)
    -- contradiction with the prime-power inequality
    have hcontra := two_mul_sigmaNat_prime_pow_lt hq hq3 ha
    rw [← hA, ← hB, ← hQ] at hcontra
    linarith

/-- Bridge to the parametrized notion at `N₀ = 1`: `SuperabundantFrom 1` numbers above `1` are even. -/
theorem superabundantFrom_one_even {n : ℕ} (h : SuperabundantFrom 1 n) (hn : 1 < n) : Even n :=
  isSuperabundant_even ((isSuperabundant_iff_superabundantFrom_one (by omega)).mpr h) hn

end RHProvability
