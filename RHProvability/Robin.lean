/-
# Robin's criterion: a computable divisor sum, and the rational-certificate reduction

Route A step 4 asks for an *arithmetic* criterion together with the reduction of its real-valued
inequality to checkable rational bounds. This file takes that step for **Robin's criterion**

  `RH  ↔  ∀ n ≥ 5041,  σ(n) < e^γ · n · log log n`

and it is explicit about what it does and does not establish.

Proved here (all machine-checked, no `sorry`, no custom axiom):

* `sigmaNat` — `σ(n) = ∑_{d ∣ n} d`, **computable** (`Nat.divisors` is `{d ∈ Ico 1 (n+1) | d ∣ n}`),
  with kernel-checked values `σ(0), σ(1), σ(2), σ(4), σ(6), σ(12)` via `decide` (no
  `native_decide`, so no compiler-trust axiom enters);
* `le_sigmaNat`, `sigmaNat_pos` — elementary facts, so `sigmaNat` really is the divisor sum;
* `RobinTest c n`, `RobinCriterion c`, `robinCriterionEulerGamma` — the criterion at an arbitrary
  real constant and at the true constant `e^γ`;
* **`robinTest_iff_exists_rat_certificate`** — the real inequality at `n` is equivalent to the
  existence of a *rational* `a < log log n` with the inequality at `a`. This is the rigorous
  statement that the transcendental comparison can be certified by rational bounds;
* `robinCriterion_iff_forall_rat_certificates` — the same, uniformly in `n`;
* `robinTest_mono`, `robinCriterion_mono` — monotonicity in the constant, i.e. a rational
  bracketing of `e^γ` transfers validity of the criterion;
* `not_robinCriterion_iff_exists_violation` — the `Π⁰₁` negation form: a violation is a witness `n`.

## What this file does **not** do

1. It does **not** prove `RiemannHypothesis ↔ robinCriterionEulerGamma`. That equivalence is
   Robin's theorem (1984) and is not formalized here; `robinCriterionEulerGamma` is a *definition*,
   so nothing is claimed about it beyond its shape.
2. It does **not** produce a `Bool`-valued check: deciding `RobinTest c n` still needs rational
   bounds on `log log n` for each `n` (and on `e^γ`). What is proved is that the reduction to such
   bounds is exact, not that the bounds have been computed.
3. It does **not** prove that `RobinCriterion` implies anything about ZFC provability.
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RHProvability.Checks

namespace RHProvability

/-! ## The divisor sum, computably -/

/-- `σ(n) = ∑_{d ∣ n} d`, the sum of the positive divisors of `n` (`σ(0) = 0`).
This is a plain `Finset` sum over `Nat.divisors`, hence computable. -/
def sigmaNat (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

@[simp] theorem sigmaNat_zero : sigmaNat 0 = 0 := by decide

theorem sigmaNat_one : sigmaNat 1 = 1 := by decide

theorem sigmaNat_two : sigmaNat 2 = 3 := by decide

theorem sigmaNat_four : sigmaNat 4 = 7 := by decide

theorem sigmaNat_six : sigmaNat 6 = 12 := by decide

theorem sigmaNat_twelve : sigmaNat 12 = 28 := by decide

-- `σ(5040) = 19344`. The kernel needs a deeper recursion budget for `Nat.divisors` here;
-- without it `decide` fails with "maximum recursion depth" and would leave `sorryAx` behind.
set_option maxRecDepth 400000 in
theorem sigmaNat_5040 : sigmaNat 5040 = 19344 := by decide

/-- `σ(n) ≥ n` for `n ≠ 0`: `n` is a divisor of itself. -/
theorem le_sigmaNat {n : ℕ} (hn : n ≠ 0) : n ≤ sigmaNat n := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn
  exact Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hmem

/-- `σ(n) ≥ 1` for `n ≠ 0`. -/
theorem sigmaNat_pos {n : ℕ} (hn : n ≠ 0) : 0 < sigmaNat n := by
  have hmem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn
  have h := Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hmem
  simp only [sigmaNat]
  omega

/-! ## The bridge to Mathlib's (noncomputable) divisor sum

`ArithmeticFunction.sigma 1` is the divisor sum used by the existing Lean formalizations of Robin's
criterion (e.g. the `Robin1984` project). The lemma below says our computable `sigmaNat` *is* that
function, so statements phrased with either one transfer. -/
theorem sigmaNat_eq_sigma_one (n : ℕ) : sigmaNat n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_apply]
  simp [sigmaNat]

/-! ## Robin's inequality -/

/-- Robin's inequality at `n` with constant `c`: `σ(n) < c · n · log log n`. -/
def RobinTest (c : ℝ) (n : ℕ) : Prop :=
  (sigmaNat n : ℝ) < c * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- Robin's criterion with constant `c`: the inequality holds for every `n ≥ 5041`. -/
def RobinCriterion (c : ℝ) : Prop := ∀ n : ℕ, 5041 ≤ n → RobinTest c n

/-- Robin's criterion at the true constant `e^γ`, where `γ` is the Euler–Mascheroni constant.
This is a **definition**: the statement `RiemannHypothesis ↔ robinCriterionEulerGamma` is Robin's
theorem and is *not* proved in this development. -/
def robinCriterionEulerGamma : Prop := RobinCriterion (Real.exp Real.eulerMascheroniConstant)

/-! ## The rational-certificate reduction -/

/-- **The transcendental comparison reduced to rational bounds.** For `c > 0` and `n ≥ 1`,
Robin's inequality at `n` holds **iff** there is a rational `a` strictly below `log log n` for
which the inequality holds with `a` in place of `log log n`.

Forward: divide by `c·n > 0` and use density of `ℚ` in `ℝ`.
Backward: `c·n > 0` and `a < log log n` give `c·n·a < c·n·log log n`.

So no approximation error can hide: a certificate is a rational strictly *below* the true value,
and the inequality itself is checked at that rational. -/
theorem robinTest_iff_exists_rat_certificate {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n) :
    RobinTest c n ↔
      ∃ a : ℚ, (a : ℝ) < Real.log (Real.log (n : ℝ)) ∧
        (sigmaNat n : ℝ) < c * (n : ℝ) * (a : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcn : (0 : ℝ) < c * (n : ℝ) := mul_pos hc hn'
  constructor
  · intro h
    have hlt : (sigmaNat n : ℝ) / (c * (n : ℝ)) < Real.log (Real.log (n : ℝ)) := by
      rw [div_lt_iff₀ hcn]
      calc (sigmaNat n : ℝ) < c * (n : ℝ) * Real.log (Real.log (n : ℝ)) := h
        _ = Real.log (Real.log (n : ℝ)) * (c * (n : ℝ)) := by ring
    obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn hlt
    refine ⟨a, ha₂, ?_⟩
    rw [div_lt_iff₀ hcn] at ha₁
    calc (sigmaNat n : ℝ) < (a : ℝ) * (c * (n : ℝ)) := ha₁
      _ = c * (n : ℝ) * (a : ℝ) := by ring
  · rintro ⟨a, ha, h⟩
    have h₁ : c * (n : ℝ) * (a : ℝ) < c * (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
      mul_lt_mul_of_pos_left ha hcn
    exact lt_trans h h₁

/-- The same reduction uniformly in `n`, for the criterion itself. -/
theorem robinCriterion_iff_forall_rat_certificates {c : ℝ} (hc : 0 < c) :
    RobinCriterion c ↔
      ∀ n : ℕ, 5041 ≤ n →
        ∃ a : ℚ, (a : ℝ) < Real.log (Real.log (n : ℝ)) ∧
          (sigmaNat n : ℝ) < c * (n : ℝ) * (a : ℝ) := by
  constructor
  · intro h n hn
    exact (robinTest_iff_exists_rat_certificate hc (by omega)).mp (h n hn)
  · intro h n hn
    exact (robinTest_iff_exists_rat_certificate hc (by omega)).mpr (h n hn)

/-! ## Monotonicity in the constant (so a rational bracketing of `e^γ` transfers) -/

/-- Robin's inequality is monotone in the constant, provided `log log n ≥ 0`. -/
theorem robinTest_mono {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) {n : ℕ}
    (hL : 0 ≤ Real.log (Real.log (n : ℝ))) (h : RobinTest c₁ n) : RobinTest c₂ n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : c₁ * (n : ℝ) * Real.log (Real.log (n : ℝ))
      ≤ c₂ * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hc hn
    exact mul_le_mul_of_nonneg_right this hL
  exact lt_of_lt_of_le h hle

/-- **Bracketing `e^γ` by rationals transfers the criterion.** If the criterion holds at a
rational `r₁ ≤ e^γ`, it holds at `e^γ`. Combined with `robinTest_iff_exists_rat_certificate`, this
is the formal content of "approximate the constant by rationals with rigorous error bounds". -/
theorem robinCriterion_mono {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hL : ∀ n : ℕ, 5041 ≤ n → 0 ≤ Real.log (Real.log (n : ℝ)))
    (h : RobinCriterion c₁) : RobinCriterion c₂ := by
  intro n hn
  exact robinTest_mono hc (hL n hn) (h n hn)

/-! ## The `Π⁰₁` negation form -/

/-- Failure of Robin's criterion is witnessed by an explicit `n ≥ 5041` — the counterexample form
needed for a `Π⁰₁` presentation. -/
theorem not_robinCriterion_iff_exists_violation {c : ℝ} :
    ¬ RobinCriterion c ↔ ∃ n : ℕ, 5041 ≤ n ∧ ¬ RobinTest c n := by
  simp [RobinCriterion]

end RHProvability
