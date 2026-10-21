/-
# N2, layer 1: Robin's inequality only needs to be checked at "record" numbers

Robin's criterion is the universal statement `RobinTest c n` for all `n ≥ 5041`. This file proves
the **first layer of the reduction to a sparse set**: it is enough to check the inequality at
integers that set a strict record for `σ(m)/m` above the threshold.

The argument is the standard minimal-counterexample argument (Alaoglu–Erdős 1944; Robin 1984), here
made explicit with the threshold `N₀` as a parameter:

* if `RobinTest` fails somewhere above `N₀`, take the **least** such `n₀`;
* every admissible `m < n₀` then satisfies `RobinTest`, i.e. `σ(m)/m < c · log log m`;
* `m < n₀` gives `log log m < log log n₀` (both are `> 0` once `m ≥ 3`);
* so `σ(m)/m < c · log log n₀ ≤ σ(n₀)/n₀`: no admissible `m < n₀` beats `n₀`'s ratio.

That last property is exactly what `SuperabundantFrom N₀` encodes.

## What this file does **not** do

1. It does **not** prove that record numbers are sparse, or that they have any density. The
   reduction is a reduction of the *quantifier domain*; it says nothing about how many records there
   are.
2. It does **not** prove Robin's theorem (`RiemannHypothesis ↔ robinCriterionEulerGamma`) — that
   equivalence is external and is not formalized anywhere in this development.
3. It does **not** pass from `superabundant` to `colossally abundant` (the stronger, sparser class),
   and it does **not** prove the Alaoglu–Erdős structural facts (records are even above `1`, the
   exponent pattern along records, …).

Proved here, all machine-checked, no `sorry`, no custom `axiom`:

* `SuperabundantFrom` — the definition (cross-multiplied, so no division appears);
* `robinTest_of_ratio_le` — **the monotonicity step**: if `m < n` has `σ(n)/n ≤ σ(m)/m` and
  `RobinTest` holds at `m`, then it holds at `n` (because `log log` is monotone);
* `forall_robinTest_iff_forall_superabundantFrom` — **the reduction**: checking Robin's inequality
  above `N₀` for *all* `n` is equivalent to checking it only at record numbers above `N₀`;
* `robinCriterion_iff_forall_superabundantFrom` — the same at the actual threshold `5041`.
-/
import RHProvability.Robin

namespace RHProvability

/-- `SuperabundantFrom N₀ n` says: `n ≥ N₀`, and no admissible `m < n` has a larger value of
`σ(m)/m` than `n` does.

The comparison is written **cross-multiplied** as `σ(m)·n < σ(n)·m`, so the definition needs no
division and no side conditions on positivity; for `0 < m ≤ n` it is equivalent to
`σ(m)/m < σ(n)/n` in `ℝ`. -/
def SuperabundantFrom (N₀ n : ℕ) : Prop :=
  N₀ ≤ n ∧ ∀ m : ℕ, N₀ ≤ m → m < n →
    (sigmaNat m : ℝ) * (n : ℝ) < (sigmaNat n : ℝ) * (m : ℝ)

/-! ## Elementary consequences of being above `3`

Everything below only needs `m ≥ 3`: then `log m > 1`, so `log log m` is *positive*, which is what
makes `log log` strictly increasing. (This is why the threshold `N₀ ≥ 3` appears everywhere: below
it `log log` is negative and the monotonicity argument breaks.) -/

/-- `log m > 1` for `m ≥ 3`. (`exp 1 < 3`, hence `1 < log 3 ≤ log m`.) -/
theorem one_lt_log_nat {m : ℕ} (hm : 3 ≤ m) : (1 : ℝ) < Real.log (m : ℝ) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3m : Real.log (3 : ℝ) ≤ Real.log (m : ℝ) := by
    apply Real.log_le_log h3pos
    exact_mod_cast hm
  have h13 : (1 : ℝ) < Real.log (3 : ℝ) := by
    have := Real.exp_one_lt_three
    -- `1 < log 3 ↔ exp 1 < 3`
    exact (Real.lt_log_iff_exp_lt h3pos).mpr this
  linarith

/-- `log log m > 0` for `m ≥ 3`. -/
theorem loglog_pos_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    0 < Real.log (Real.log (m : ℝ)) :=
  Real.log_pos (one_lt_log_nat hm)

/-- `log log` is **strictly increasing** on `m ≥ 3`. -/
theorem loglog_lt_loglog {m n : ℕ} (hm : 3 ≤ m) (hmn : m < n) :
    Real.log (Real.log (m : ℝ)) < Real.log (Real.log (n : ℝ)) := by
  have h1 : (0 : ℝ) < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have h2 : Real.log (m : ℝ) < Real.log (n : ℝ) := Real.log_lt_log hmR hmnR
  exact Real.log_lt_log h1 h2

/-! ## The monotonicity step -/

/-- **If a smaller admissible `m` has at least as large a ratio `σ(m)/m`, then Robin's inequality at
`m` transfers up to `n`.**

This is the direction that makes the minimal-counterexample argument work: the ratio can only go down
as `n` grows, and `log log n` is increasing, so the inequality cannot be lost by going up. -/
theorem robinTest_of_ratio_le {c : ℝ} (hc : 0 < c) {N₀ m n : ℕ} (hN₀ : 3 ≤ N₀)
    (hmN : N₀ ≤ m) (hmn : m < n)
    (hle : (sigmaNat n : ℝ) * (m : ℝ) ≤ (sigmaNat m : ℝ) * (n : ℝ))
    (hm : RobinTest c m) : RobinTest c n := by
  have hm3 : 3 ≤ m := le_trans hN₀ hmN
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hLlt := loglog_lt_loglog hm3 hmn
  -- `σ(n)/n ≤ σ(m)/m < c · log log m < c · log log n`
  have step2 : (sigmaNat m : ℝ) * (n : ℝ)
      < (c * (m : ℝ) * Real.log (Real.log (m : ℝ))) * (n : ℝ) :=
    mul_lt_mul_of_pos_right hm hnR
  have step3 : (c * (m : ℝ) * Real.log (Real.log (m : ℝ))) * (n : ℝ)
      < (c * (m : ℝ) * Real.log (Real.log (n : ℝ))) * (n : ℝ) := by
    have hpos : (0 : ℝ) < c * (m : ℝ) := mul_pos hc hmR
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hLlt hpos) hnR
  have hkey : (sigmaNat n : ℝ) * (m : ℝ)
      < (c * (n : ℝ) * Real.log (Real.log (n : ℝ))) * (m : ℝ) := by
    calc (sigmaNat n : ℝ) * (m : ℝ) ≤ (sigmaNat m : ℝ) * (n : ℝ) := hle
      _ < (c * (m : ℝ) * Real.log (Real.log (m : ℝ))) * (n : ℝ) := step2
      _ < (c * (m : ℝ) * Real.log (Real.log (n : ℝ))) * (n : ℝ) := step3
      _ = (c * (n : ℝ) * Real.log (Real.log (n : ℝ))) * (m : ℝ) := by ring
  exact lt_of_mul_lt_mul_right hkey (le_of_lt hmR)

/-! ## The reduction -/

/-- **Robin's inequality above `N₀` only needs to be checked at record numbers above `N₀`.**

`(∀ n ≥ N₀, RobinTest c n) ↔ (∀ n, SuperabundantFrom N₀ n → RobinTest c n)` for `c > 0` and
`N₀ ≥ 3`.

Forward is trivial. Backward is the minimal-counterexample argument: if some `n ≥ N₀` violated the
inequality, the *least* violator `n₀` would have `σ(m)·n₀ < σ(n₀)·m` for every admissible `m < n₀`
(otherwise `m` would be a smaller violator), i.e. `n₀` would be a record — and the hypothesis would
then apply to it.

Note what this does **not** say: it does not say records are few. It moves the quantifier onto a
strictly smaller class, and says nothing about the size of that class. -/
theorem forall_robinTest_iff_forall_superabundantFrom {c : ℝ} (hc : 0 < c) {N₀ : ℕ} (hN₀ : 3 ≤ N₀) :
    (∀ n : ℕ, N₀ ≤ n → RobinTest c n) ↔
      ∀ n : ℕ, SuperabundantFrom N₀ n → RobinTest c n := by
  classical
  constructor
  · rintro h n ⟨hn, _⟩
    exact h n hn
  · intro hrec n hn
    -- strong induction on `n`
    have key : ∀ n : ℕ, N₀ ≤ n → RobinTest c n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn
        by_cases hsa : SuperabundantFrom N₀ n
        · exact hrec n hsa
        · -- `n` is not a record: some admissible `m < n` has ratio at least as large
          have hnot : ¬ ∀ m : ℕ, N₀ ≤ m → m < n →
              (sigmaNat m : ℝ) * (n : ℝ) < (sigmaNat n : ℝ) * (m : ℝ) := by
            intro hall
            exact hsa ⟨hn, hall⟩
          push Not at hnot
          obtain ⟨m, hmN, hmn, hle⟩ := hnot
          exact robinTest_of_ratio_le hc hN₀ hmN hmn hle (ih m hmn hmN)
    exact key n hn

/-- The reduction at Robin's actual threshold `5041`. -/
theorem robinCriterion_iff_forall_superabundantFrom {c : ℝ} (hc : 0 < c) :
    RobinCriterion c ↔ ∀ n : ℕ, SuperabundantFrom 5041 n → RobinTest c n :=
  forall_robinTest_iff_forall_superabundantFrom hc (by norm_num : 3 ≤ 5041)

/-- **The `Π⁰₁` witness shape survives the reduction**: failing Robin's criterion is equivalent to
the existence of an explicit `n ≥ 5041` that is *moreover a record number*. So the reduction does not
cost us the witness form used elsewhere in this development. -/
theorem not_robinCriterion_iff_exists_superabundant_violation {c : ℝ} (hc : 0 < c) :
    ¬ RobinCriterion c ↔ ∃ n : ℕ, SuperabundantFrom 5041 n ∧ ¬ RobinTest c n := by
  classical
  rw [robinCriterion_iff_forall_superabundantFrom hc]
  constructor
  · intro h
    by_contra hcon
    exact h (fun n hn => by_contra fun hR => hcon ⟨n, hn, hR⟩)
  · rintro ⟨n, hn, hR⟩ h
    exact hR (h n hn)

end RHProvability
