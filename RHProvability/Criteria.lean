/-
# Robin's criterion implies Lagarias's criterion (pointwise, with explicit hypotheses)

Both criteria are in this development (`RobinTest`, `lagariasTest`), and each is equivalent to RH by an
external theorem (Robin 1984, Lagarias 2001/2002). **Their pointwise relation had not been stated
anywhere**, and it is not automatic: Robin's right-hand side is `e^γ n log log n` while Lagarias's is
`H_n + e^{H_n} log H_n`, and the two agree only to first order.

This file proves the implication `RobinTest (e^γ) n → lagariasTest n` for `n ≥ 3`. The whole content is
the second-order fact

  `H_n − log n ≥ γ`   (Euler–Mascheroni),

which gives `e^{H_n} ≥ n·e^γ`, so that Lagarias's right-hand side dominates Robin's. Being an
implication between the two criteria, this is a transfer statement: a verification carried out against
one criterion transfers to the other.

## Not here

The equivalences with RH. Nothing in this file mentions `RiemannHypothesis`.
-/
import RHProvability.Numeric
import RHProvability.Lagarias
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Int
import RHProvability.TightBounds

namespace RHProvability

open Real

/-- **The sequence `H_n − log n` is antitone along the successor step** (for `n ≥ 1`). This is the
elementary fact `1/(n+1) ≤ log(1 + 1/n)`, which in this development is
`RHProvability.one_sub_inv_le_log`. -/
lemma harmonic_sub_log_antitone_succ {n : ℕ} (hn : 1 ≤ n) :
    (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) - Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n = Real.log (((n : ℝ) + 1) / n) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have hstep : ((n : ℝ) + 1)⁻¹ ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
    rw [hlog]
    have h := one_sub_inv_le_log (x := ((n : ℝ) + 1) / n) (by positivity)
    have heq : 1 - (((n : ℝ) + 1) / n)⁻¹ = ((n : ℝ) + 1)⁻¹ := by
      field_simp
      ring
    rwa [heq] at h
  rw [harmonic_succ]
  push_cast
  linarith

/-- **`H_n − log n ≥ γ` for every `n ≥ 1`.** Obtained from the antitone step plus convergence to the
Euler–Mascheroni constant (Mathlib:
`tendsto_harmonic_sub_log`, `NumberTheory/Harmonic/EulerMascheroni.lean:150`).

This is the quantitative input that makes Robin's criterion imply Lagarias's. -/
theorem eulerMascheroniConstant_le_harmonic_sub_log {n : ℕ} (hn : 1 ≤ n) :
    eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log n := by
  have key : ∀ m, n ≤ m → (harmonic m : ℝ) - Real.log m ≤ (harmonic n : ℝ) - Real.log n := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact le_trans (harmonic_sub_log_antitone_succ (le_trans hn hk)) ih
  refine le_of_tendsto_of_tendsto tendsto_harmonic_sub_log tendsto_const_nhds ?_
  exact Filter.eventually_atTop.2 ⟨n, fun m hm => key m hm⟩

/-- **`n·e^γ ≤ e^{H_n}`** for `n ≥ 1`: immediate from `H_n ≥ log n + γ`. -/
theorem mul_exp_eulerMascheroniConstant_le_exp_harmonic {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.exp eulerMascheroniConstant ≤ Real.exp (harmonic n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hge := eulerMascheroniConstant_le_harmonic_sub_log hn
  have hpos : 0 < eulerMascheroniConstant := by linarith [one_half_lt_eulerMascheroniConstant]
  calc (n : ℝ) * Real.exp eulerMascheroniConstant
      = Real.exp (Real.log n) * Real.exp eulerMascheroniConstant := by rw [Real.exp_log hnpos]
    _ = Real.exp (Real.log n + eulerMascheroniConstant) := by rw [Real.exp_add]
    _ ≤ Real.exp (Real.log n + ((harmonic n : ℝ) - Real.log n)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (harmonic n : ℝ) := by ring_nf

/-- **Robin's inequality implies Lagarias's inequality**, pointwise, for `n ≥ 3`.

Both sides are criteria for RH, so this is a *transfer* statement: a verification carried out against
Robin's inequality transfers to Lagarias's. It is not a consequence of RH (it holds for each `n`
regardless), and it is not in the literature as a formal implication.

The proof is the second-order estimate: `e^{H_n} ≥ n·e^γ` (`mul_exp_eulerMascheroniConstant_le_exp_harmonic`)
together with `log H_n ≥ log log n`, which makes Lagarias's right-hand side `H_n + e^{H_n} log H_n`
dominate Robin's `e^γ n log log n`. -/
theorem robinTest_imp_lagariasTest {n : ℕ} (hn : 3 ≤ n)
    (h : RobinTest (Real.exp eulerMascheroniConstant) n) : lagariasTest n := by
  unfold RobinTest at h
  unfold lagariasTest lagariasRHS
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn1 : (1 : ℝ) ≤ Real.log n := by
    have he : Real.exp 1 ≤ (n : ℝ) :=
      le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast hn))
    exact (Real.le_log_iff_exp_le hnpos).mpr he
  have hloglogn : (0 : ℝ) ≤ Real.log (Real.log n) := Real.log_nonneg hlogn1
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hH : Real.log n ≤ (harmonic n : ℝ) := by
    have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
    have h3 : Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) := by
      rw [← hcast]; exact log_add_one_le_harmonic n
    exact le_trans h2 h3
  have hlogH : Real.log (Real.log n) ≤ Real.log (harmonic n) :=
    Real.log_le_log (by linarith) hH
  have hexp := mul_exp_eulerMascheroniConstant_le_exp_harmonic hn1
  have hmul : Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n)
      ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) := by
    have h := mul_le_mul hexp hlogH hloglogn (Real.exp_pos _).le
    calc Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n)
        = ((n : ℝ) * Real.exp eulerMascheroniConstant) * Real.log (Real.log n) := by ring
      _ ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) := h
  have hHnonneg : (0 : ℝ) ≤ (harmonic n : ℝ) := by
    have hpos : 0 < harmonic n := harmonic_pos (by omega)
    exact_mod_cast hpos.le
  linarith [h, hmul]

/-- **Criterion-level transfer**: if Robin's criterion holds (at the true constant `e^γ`), then
Lagarias's inequality holds on the same range `n ≥ 5041`.

Because Robin's criterion is stated only from `5041` on, this is the sharp form of the transfer: it is
*not* the full `lagariasCriterion` (which quantifies over all `n ≥ 1`). -/
theorem robinCriterion_imp_lagarias_on_tail (h : robinCriterionEulerGamma) :
    ∀ n : ℕ, 5041 ≤ n → lagariasTest n := by
  intro n hn
  exact robinTest_imp_lagariasTest (by omega) (h n hn)

/-- **Lagarias's inequality does not imply Robin's**, so the two criteria are not interchangeable.

Machine-checked witness: `n = 1`. There `lagariasTest 1` holds *with equality* (`σ(1) = H_1 + e^{H_1}·0 = 1`,
see `lagariasTest_one`), while Robin's test fails since `log (log 1) = log 0 = 0` and `1 < 0` is false.

**Scope.** This settles the *unrestricted* implication. Whether the implication holds on the tail
`n ≥ 5041` is a different question: on that range Robin's inequality is strictly stronger by the margin
`e^γ·γ/log n` shown in `mul_exp_eulerMascheroniConstant_le_exp_harmonic`, so the answer there is not
decided by this theorem, and is not decided anywhere in this development. -/
theorem exists_lagariasTest_not_robinTest :
    ∃ n : ℕ, lagariasTest n ∧ ¬ RobinTest (Real.exp eulerMascheroniConstant) n := by
  refine ⟨1, lagariasTest_one, ?_⟩
  unfold RobinTest
  rw [sigmaNat_one]
  have hlog1 : Real.log (Real.log ((1 : ℕ) : ℝ)) = 0 := by
    simp
  rw [hlog1]
  push_cast
  intro hc
  linarith [Real.exp_pos eulerMascheroniConstant]

/-- **Lagarias's right-hand side dominates Robin's.** For `n ≥ 3`,

`e^γ · n · log(log n) ≤ H_n + e^{H_n} log H_n = lagariasRHS n`.

This is the exact inequality that makes Robin's criterion imply Lagarias's, extracted as a standalone
statement because it is also the quantity relevant to the *converse* question: whether Lagarias's
inequality can hold where Robin's fails is a question about the **slack**

`lagariasRHS n / n − e^γ log log n = H_n/n + (e^{H_n}/n)·log H_n − e^γ log log n`,

which is of order `e^γ·γ/log n` (the `H_n/n` term being much smaller). So the converse question is:
can `σ(n)/n` exceed `e^γ log log n` by an amount still below that slack? -/
theorem exp_eulerMascheroni_mul_loglog_le_lagariasRHS {n : ℕ} (hn : 3 ≤ n) :
    Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n) ≤ lagariasRHS n := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn1 : (1 : ℝ) ≤ Real.log n := by
    have he : Real.exp 1 ≤ (n : ℝ) :=
      le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast hn))
    exact (Real.le_log_iff_exp_le hnpos).mpr he
  have hloglogn : (0 : ℝ) ≤ Real.log (Real.log n) := Real.log_nonneg hlogn1
  have hH : Real.log n ≤ (harmonic n : ℝ) := by
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
    have h3 : Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) := by
      rw [← hcast]; exact log_add_one_le_harmonic n
    exact le_trans h2 h3
  have hlogH : Real.log (Real.log n) ≤ Real.log (harmonic n) :=
    Real.log_le_log (by linarith) hH
  have hexp := mul_exp_eulerMascheroniConstant_le_exp_harmonic hn1
  have hmul : Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n)
      ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) := by
    have h := mul_le_mul hexp hlogH hloglogn (Real.exp_pos _).le
    calc Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n)
        = ((n : ℝ) * Real.exp eulerMascheroniConstant) * Real.log (Real.log n) := by ring
      _ ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) := h
  have hHnonneg : (0 : ℝ) ≤ (harmonic n : ℝ) := by
    have hpos : 0 < harmonic n := harmonic_pos (by omega)
    exact_mod_cast hpos.le
  unfold lagariasRHS
  linarith

/-- **The counterexample set of the converse question, exactly.** For `n ≥ 3`, Lagarias's inequality
holds while Robin's fails **if and only if** `σ(n)/n` lies in the closed window

  `[e^γ · log log n, lagariasRHS n / n]`.

This is the precise object the tail question is about: the window has width
`e^γ·γ/log n + o(1/log n)` (see `exp_eulerMascheroni_mul_loglog_le_lagariasRHS`), so the converse
question asks whether Robin's violations can be *small enough* to land in it. -/
theorem lagariasTest_and_not_robinTest_iff {n : ℕ} (hn : 3 ≤ n) :
    (lagariasTest n ∧ ¬ RobinTest (Real.exp eulerMascheroniConstant) n)
      ↔ (Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log n) ≤ (sigmaNat n : ℝ)
          ∧ (sigmaNat n : ℝ) ≤ lagariasRHS n) := by
  unfold lagariasTest RobinTest
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨not_lt.mp h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, not_lt.mpr h1⟩

/-- `H_n ≥ 1` for `n ≥ 1`. (Used to make `log H_n ≥ 0`, which the slack analysis needs.) -/
theorem one_le_harmonic {n : ℕ} (hn : 1 ≤ n) : (1 : ℚ) ≤ harmonic n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [harmonic]
    · have hk1 : 1 ≤ k := hk
      have hprev := ih hk1
      rw [harmonic_succ]
      have hpos : (0 : ℚ) ≤ (((k + 1 : ℕ)) : ℚ)⁻¹ := by positivity
      linarith

/-- **The slack, exhibited.** For `n ≥ 3`,

`lagariasRHS n ≥ e^γ · n · log H_n`.

Compared with Robin's right-hand side `e^γ · n · log log n` this isolates where the extra room comes
from: the factor `log H_n` rather than `log log n`, since `H_n ≥ log n`. Dividing by `n` gives the
form the converse question needs:

`lagariasRHS n / n ≥ e^γ · log H_n`,

so the window `[e^γ log log n, lagariasRHS n / n]` contains the interval between `log log n` and
`log H_n` — which is exactly the quantity that shrinks like `γ/log n`. -/
theorem exp_mul_log_harmonic_le_lagariasRHS {n : ℕ} (hn : 3 ≤ n) :
    Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (harmonic n) ≤ lagariasRHS n := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hH1 : (1 : ℝ) ≤ (harmonic n : ℝ) := by
    have := one_le_harmonic hn1
    exact_mod_cast this
  have hlogH : (0 : ℝ) ≤ Real.log (harmonic n) := Real.log_nonneg hH1
  have hexp := mul_exp_eulerMascheroniConstant_le_exp_harmonic hn1
  have hmul : Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (harmonic n)
      ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) := by
    have := mul_le_mul_of_nonneg_right hexp hlogH
    calc Real.exp eulerMascheroniConstant * (n : ℝ) * Real.log (harmonic n)
        = ((n : ℝ) * Real.exp eulerMascheroniConstant) * Real.log (harmonic n) := by ring
      _ ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) := this
  unfold lagariasRHS
  linarith

/-- `log n ≤ H_n` for `n ≥ 1`: the harmonic number dominates the logarithm. -/
theorem log_le_harmonic {n : ℕ} (hn : 1 ≤ n) : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
  have h3 : Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) := by
    rw [← hcast]; exact log_add_one_le_harmonic n
  exact le_trans h2 h3

/-- **The window width, explicitly.** For `n ≥ 3`,

`log H_n − log log n ≥ (2γ/3) / log n`.

This is the quantitative core of the task-N1 tail question. The window of `n` where Lagarias's
inequality can hold while Robin's fails is

  `e^γ · n · log log n ≤ σ(n) ≤ lagariasRHS n`,

and its relative width is governed exactly by `log H_n − log log n`. So the window is **non-degenerate of
size ≳ (2γ/3)/log n**, uniformly in `n ≥ 3`: Robin's violations have room to hide there, and whether
they actually do is the open quantitative question.

Proof ingredients: `γ ≤ H_n − log n` (`eulerMascheroniConstant_le_harmonic_sub_log`),
`H_n ≤ 1 + log n` (Mathlib `harmonic_le_one_add_log`), and the artanh lower bound
`log y ≥ 2(y-1)/(y+1)` for `y ≥ 1` (`RHProvability.log_lower_artanh`). -/
theorem log_harmonic_sub_loglog_ge {n : ℕ} (hn : 3 ≤ n) :
    (2 * eulerMascheroniConstant / 3) / Real.log n
      ≤ Real.log (harmonic n) - Real.log (Real.log n) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn1 : (1 : ℝ) ≤ Real.log n := by
    have he : Real.exp 1 ≤ (n : ℝ) :=
      le_of_lt (lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast hn))
    exact (Real.le_log_iff_exp_le hnpos).mpr he
  have hlognpos : (0 : ℝ) < Real.log n := by linarith
  have hlo : Real.log n ≤ (harmonic n : ℝ) := log_le_harmonic hn1
  have hge := eulerMascheroniConstant_le_harmonic_sub_log hn1
  have hup : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have hHpos : (0 : ℝ) < (harmonic n : ℝ) := by linarith
  -- ratio r = H_n / log n, sandwiched between 1 + γ/log n and 2
  have hr1 : (1 : ℝ) ≤ (harmonic n : ℝ) / Real.log n := by
    rw [le_div_iff₀ hlognpos]; linarith
  have hrle : (harmonic n : ℝ) / Real.log n ≤ 2 := by
    rw [div_le_iff₀ hlognpos]; linarith
  -- rewrite the difference as log of the ratio
  have hkey : Real.log (harmonic n) - Real.log (Real.log n)
      = Real.log ((harmonic n : ℝ) / Real.log n) := by
    rw [Real.log_div hHpos.ne' hlognpos.ne']
  rw [hkey]
  -- artanh lower bound
  have hartanh := log_lower_artanh hr1
  -- lower bound on 2(r-1)/(r+1)
  have hlow : (2 * eulerMascheroniConstant / 3) / Real.log n
      ≤ 2 * ((harmonic n : ℝ) / Real.log n - 1) / ((harmonic n : ℝ) / Real.log n + 1) := by
    have hnum : 2 * eulerMascheroniConstant / 3 / Real.log n
        ≤ 2 * (((harmonic n : ℝ) / Real.log n) - 1) / 3 := by
      rw [div_le_iff₀ hlognpos]
      have h2 : eulerMascheroniConstant ≤ (harmonic n : ℝ) - Real.log n := hge
      have h3 : 2 * ((harmonic n : ℝ) / Real.log n - 1) / 3 * Real.log n
          = 2 * ((harmonic n : ℝ) - Real.log n) / 3 := by
        field_simp
      rw [h3]
      nlinarith
    have hden : ((harmonic n : ℝ) / Real.log n + 1) ≤ 3 := by linarith
    have hpos2 : (0 : ℝ) < ((harmonic n : ℝ) / Real.log n + 1) := by linarith
    calc (2 * eulerMascheroniConstant / 3) / Real.log n
        ≤ 2 * (((harmonic n : ℝ) / Real.log n) - 1) / 3 := hnum
      _ ≤ 2 * (((harmonic n : ℝ) / Real.log n) - 1) / ((harmonic n : ℝ) / Real.log n + 1) := by
          apply div_le_div_of_nonneg_left (by linarith [hge]) hpos2 hden
  linarith [hartanh, hlow]

/-- `lagariasRHS n > 0` for `n ≥ 1`. (Needed whenever the criterion's right-hand side is divided by or
compared with a logarithm.) -/
theorem lagariasRHS_pos {n : ℕ} (hn : 1 ≤ n) : 0 < lagariasRHS n := by
  have hH1 : (1 : ℝ) ≤ (harmonic n : ℝ) := by
    have := one_le_harmonic hn
    exact_mod_cast this
  have hlogH : (0 : ℝ) ≤ Real.log (harmonic n) := Real.log_nonneg hH1
  unfold lagariasRHS
  have : (0 : ℝ) ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n) :=
    mul_nonneg (Real.exp_pos _).le hlogH
  linarith

end RHProvability
