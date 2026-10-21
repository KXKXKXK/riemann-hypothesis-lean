/-
# Weil 正性：Fejér 构造的可验证核

本文件把 `数学家-核验记录/WEIL-positivity-feasibility-2026-10-18.md` §14
中**声称严格**的部分逐条形式化。

## 为什么先做这一条

报告撰写过程中出现过一次真实缺陷：`Λ(n)` 被误实现为
「最小素因子的对数」，于是 `Λ(6)` 返回 `log 2` 而非 `0`，
导致 `A_L` 在 `L ≥ 1.2` 时虚高 1.535 倍。本文件第一件事
就是把这个判别本身写成定理（§1）。

第二件事（§4）是 Fejér 核：矩形窗的自相关是三角形。
这是报告 §14.3 全部「严格下界」声明的支点，也是
`μ(L) ≥ μ_rect(L)` 的唯一解析输入。它不需要 Fourier 变换，
只需测度论。

## 记号

* `Λ n` = `ArithmeticFunction.vonMangoldt n`（Mathlib 现成）。
* `rectFun L` = `1_{[-L,L]}`，即支撑 `[-L,L]`、高度 1 的矩形窗。
* 自相关 `A_f(h) = ∫ x, f x * f (x - h)`（未归一化）。
-/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

open ArithmeticFunction MeasureTheory Set

namespace RHProvability.WeilFejer

/-! ### 1. 非素数幂的 `Λ` 必须为零（报告 §14.8.1 记录的缺陷） -/

theorem not_isPrimePow_six : ¬ IsPrimePow 6 := by decide

theorem not_isPrimePow_ten : ¬ IsPrimePow 10 := by decide

theorem not_isPrimePow_twelve : ¬ IsPrimePow 12 := by decide

/-- `6 = 2 · 3` 不是素数幂，故 `Λ 6 = 0`。 -/
theorem vonMangoldt_six : Λ 6 = 0 := by
  rw [vonMangoldt_apply]; simp [not_isPrimePow_six]

theorem vonMangoldt_ten : Λ 10 = 0 := by
  rw [vonMangoldt_apply]; simp [not_isPrimePow_ten]

theorem vonMangoldt_twelve : Λ 12 = 0 := by
  rw [vonMangoldt_apply]; simp [not_isPrimePow_twelve]

/-! ### 2. 素数幂的 `Λ` 取对数值 -/

theorem vonMangoldt_two : Λ 2 = Real.log 2 := vonMangoldt_apply_prime Nat.prime_two

theorem vonMangoldt_three : Λ 3 = Real.log 3 := vonMangoldt_apply_prime Nat.prime_three

theorem vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, vonMangoldt_apply_pow (by norm_num)]
  exact vonMangoldt_apply_prime Nat.prime_two

theorem vonMangoldt_eight : Λ 8 = Real.log 2 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, vonMangoldt_apply_pow (by norm_num)]
  exact vonMangoldt_apply_prime Nat.prime_two

theorem vonMangoldt_nine : Λ 9 = Real.log 3 := by
  have h : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h, vonMangoldt_apply_pow (by norm_num)]
  exact vonMangoldt_apply_prime Nat.prime_three

/-! ### 3. 非零支集恰为素数幂 -/

theorem vonMangoldt_eq_zero_of_not_isPrimePow (n : ℕ) (h : ¬ IsPrimePow n) : Λ n = 0 := by
  rw [vonMangoldt_apply]; simp [h]

theorem vonMangoldt_ne_zero_iff_isPrimePow (n : ℕ) : Λ n ≠ 0 ↔ IsPrimePow n :=
  vonMangoldt_ne_zero_iff

/-! ### 4. Fejér 核：矩形窗的自相关是三角形

这是报告 §14.3 的解析支点。纯测度论，不用 Fourier 变换。

`A(h) = volume([-L,L] ∩ [h-L,h+L]) = max 0 (2L - |h|)`
-/

lemma ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max 0 x) = ENNReal.ofReal x := by
  by_cases h : 0 ≤ x
  · rw [max_eq_right h]
  · have h' : x < 0 := not_le.mp h
    rw [max_eq_left h'.le, ENNReal.ofReal_eq_zero.mpr h'.le]
    simp

/-- 两个长度 `2L` 的区间错开 `h` 时的交集测度。 -/
theorem volume_Icc_inter_Icc_abs (L h : ℝ) :
    volume (Icc (-L) L ∩ Icc (h - L) (h + L)) = ENNReal.ofReal (max 0 (2 * L - |h|)) := by
  rw [Set.Icc_inter_Icc, Real.volume_Icc]
  have key : min L (h + L) - max (-L) (h - L) = 2 * L - |h| := by
    by_cases h0 : 0 ≤ h
    · rw [abs_of_nonneg h0, min_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · have h0' : h < 0 := not_le.mp h0
      rw [abs_of_neg h0', min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  rw [key, ofReal_max_zero]

theorem real_volume_Icc_inter_Icc_abs (L h : ℝ) :
    (volume (Icc (-L) L ∩ Icc (h - L) (h + L))).toReal = max 0 (2 * L - |h|) := by
  rw [volume_Icc_inter_Icc_abs, ENNReal.toReal_ofReal (le_max_left 0 _)]

/-- 矩形窗函数 `1_{[-L,L]}`。 -/
noncomputable def rectFun (L : ℝ) : ℝ → ℝ := (Icc (-L) L).indicator fun _ => (1 : ℝ)

lemma sub_mem_Icc_iff (L h x : ℝ) :
    x - h ∈ Icc (-L) L ↔ x ∈ Icc (h - L) (h + L) := by
  simp only [Set.mem_Icc]
  constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith

lemma rectFun_shift_apply (L h x : ℝ) :
    rectFun L (x - h) = (Icc (h - L) (h + L)).indicator (fun _ => (1 : ℝ)) x := by
  simp only [rectFun, Set.indicator_apply]
  by_cases hx : x - h ∈ Icc (-L) L
  · have hx' : x ∈ Icc (h - L) (h + L) := (sub_mem_Icc_iff L h x).mp hx
    simp [hx, hx']
  · have hx' : x ∉ Icc (h - L) (h + L) := fun hc => hx ((sub_mem_Icc_iff L h x).mpr hc)
    simp [hx, hx']

lemma indicator_one_mul_apply (s t : Set ℝ) (x : ℝ) :
    s.indicator (fun _ => (1 : ℝ)) x * t.indicator (fun _ => (1 : ℝ)) x
      = (s ∩ t).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, ht]

/-- **Fejér 核（时域形式）**：`[-L,L]` 上矩形窗的自相关是三角形的。 -/
theorem autocorr_rectFun (L h : ℝ) :
    ∫ x, rectFun L x * rectFun L (x - h) = max 0 (2 * L - |h|) := by
  have hfun : (fun x => rectFun L x * rectFun L (x - h))
      = (Icc (-L) L ∩ Icc (h - L) (h + L)).indicator (fun _ => (1 : ℝ)) := by
    funext x
    show (Icc (-L) L).indicator (fun _ => (1 : ℝ)) x * rectFun L (x - h) = _
    rw [rectFun_shift_apply L h x]
    exact indicator_one_mul_apply _ _ x
  rw [hfun, MeasureTheory.integral_indicator (measurableSet_Icc.inter measurableSet_Icc)]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  simpa [MeasureTheory.Measure.real] using real_volume_Icc_inter_Icc_abs L h

/-! ### 5. 归一化、支撑与零点值（报告 §14.3 的 `A_f(h) = (1-|h|/(2L))_+`） -/

/-- 归一化自相关 `A_f(h) = 自相关 / ‖f‖²`；矩形窗的 `‖f‖² = 2L`。 -/
theorem A_rect (L h : ℝ) (hL : 0 < L) :
    (∫ x, rectFun L x * rectFun L (x - h)) / (2 * L) = max 0 (1 - |h| / (2 * L)) := by
  rw [autocorr_rectFun]
  have h2L : (0 : ℝ) < 2 * L := by linarith
  rw [div_eq_iff h2L.ne']
  by_cases hc : |h| ≤ 2 * L
  · have hle : |h| / (2 * L) ≤ 1 := (div_le_one h2L).mpr hc
    have h1 : 0 ≤ 1 - |h| / (2 * L) := by linarith
    have h2 : 0 ≤ 2 * L - |h| := by linarith
    have e1 : max 0 (1 - |h| / (2 * L)) = 1 - |h| / (2 * L) := max_eq_right h1
    have e2 : max 0 (2 * L - |h|) = 2 * L - |h| := max_eq_right h2
    rw [e1, e2]
    field_simp
  · have hc' : 2 * L < |h| := not_le.mp hc
    have h2 : 2 * L - |h| < 0 := by linarith
    have h1 : 1 - |h| / (2 * L) < 0 := by
      rw [show 1 - |h| / (2 * L) = (2 * L - |h|) / (2 * L) by field_simp]
      exact div_neg_of_neg_of_pos h2 h2L
    have e1 : max 0 (1 - |h| / (2 * L)) = 0 := by
      apply le_antisymm
      · exact max_le (le_refl 0) h1.le
      · exact le_max_left 0 _
    have e2 : max 0 (2 * L - |h|) = 0 := by
      apply le_antisymm
      · exact max_le (le_refl 0) h2.le
      · exact le_max_left 0 _
    rw [e1, e2, zero_mul]

/-- Fejér 核在 `h = 0` 处的值：归一化为 1。 -/
theorem A_rect_zero (L : ℝ) (hL : 0 < L) :
    (∫ x, rectFun L x * rectFun L (x - 0)) / (2 * L) = 1 := by
  rw [A_rect L 0 hL]
  simp

/-- **支撑**：`|h| ≥ 2L` 时自相关为零。即 `supp(f * f̃) ⊆ [-2L, 2L]`。 -/
theorem autocorr_rectFun_eq_zero (L h : ℝ) (hh : 2 * L ≤ |h|) :
    ∫ x, rectFun L x * rectFun L (x - h) = 0 := by
  rw [autocorr_rectFun, max_eq_left (by linarith)]

/-! ### 6. `L = 0.8` 时只有三个素数幂（报告 §14.8.2 表格的依据）

`L = 0.8` ⟹ `e^{2L} = e^{1.6} \approx 4.95`，故求和只到 `n \le 4`。
在 `0..4` 中只有 `2, 3, 4` 是素数幂，所以 `A_L` 与 `\mu_{\rm rect}` 都只有三项。
本定理把"只有三项"这件事与 `\Lambda` 的判别绑定。 -/

theorem primePowsBelowFive : ∀ n : ℕ, n < 5 → (Λ n ≠ 0 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro n hn
  rw [vonMangoldt_ne_zero_iff]
  interval_cases n
  · simp [not_isPrimePow_zero]
  · simp [not_isPrimePow_one]
  · exact ⟨fun _ => Or.inl rfl, fun _ => Nat.prime_two.isPrimePow⟩
  · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => Nat.prime_three.isPrimePow⟩
  · have h4 : IsPrimePow (4 : ℕ) := by
      have := (Nat.prime_two.isPrimePow).pow (k := 2) (by norm_num)
      norm_num at this
      exact this
    exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => h4⟩

end RHProvability.WeilFejer
