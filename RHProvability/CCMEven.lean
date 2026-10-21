/-
# 实矩阵的实特征向量（以及一个必须撤回的结论）

## 本文件证明什么

1. `map_ofReal_mulVec_re` / `_im`：实矩阵 `T` 在 `ℂ^n` 的延拓，其作用与「取实部/虚部」交换。
2. `exists_real_eigenvector`：实矩阵的实特征值，若有非零复特征向量，则必有非零**实**特征向量。
3. `conjVec_ofReal`：**复共轭**在实向量上不动。
4. `exists_real_eigenvector_of_isSymmetric`：有限维实内积空间上 `T.IsSymmetric` 的谱非空（用谱定理）。
5. `exists_real_eigenvector_of_matrix_symm`：实对称矩阵 `M`（`M = Mᵀ`）在 `ℝ^n` 上必有实特征值与特征向量。

## ⚠️ 本文件**不能**做什么（2026-10-19 更正，此前结论撤回）

此前本文件声称「缺口①的『偶』自动成立，只需 `T` 是实矩阵」。**这个结论是错的，现撤回。**

原因：C-C-M 的 `γ` 是**复线性**对合 `γ(V_j) = V_{−j}`（Lemma 5.2(i)），
即中心化对数坐标下的 `x ↦ −x`，也就是 `u ↦ u⁻¹`。
而「实特征向量」用的是**反线性**的复共轭。

在基向量上两者给同一个像 `V_n ↦ V_{−n}`，但作为算子不同：
`conj(Σ z_n V_n) = Σ conj(z_n) V_{−n}`，而 `γ(Σ z_n V_n) = Σ z_n V_{−n}`。

* `fix(conj)` = 实向量（实维 `2N+1`）
* `fix(γ)` = 偶向量（复维 `N+1`，`cos` 空间）

**两者互不包含**：奇空间里也有实函数（`sin`），所以「实 ⟹ 偶」是**假的**。

`N = 1` 显式：`T = [[a₁,b₁,b₁],[b₁,a₀,b₁],[b₁,b₁,a₁]]`，
`(V₁+V_{−1})/√2 = √2 cos` 实且偶，`i(V₁−V_{−1})/√2 = −√2 sin` 实且**奇**，
最低特征向量落在哪一块没有任何强制。

**文献印证**：Suzuki, arXiv:2606.09096v3 §4.5 逐字：
> "the assumption in [4, Theorem 5.10] amounts to requiring that
> `dim E₊(λ_a) = 1` and `E₋(λ_a) = {0}`."

——**两个**条件，不是「单重 ⟹ 自动偶」。

所以缺口①仍然是两条：**最小特征值单重** ＋ **基态落在偶块**。
另外 Prop 5.7 的证明用 `δ_N(ξ) ≠ 0`（`δ_N = L^{−1/2}η`，`η` 偶）；
若 `ξ` 奇则 `⟨η|ξ⟩ = 0`，算子的构造本身不存在。**偶性不是装饰。**

## 那本文件还有什么用

定理本身是对的（实矩阵有实特征向量、实对称矩阵谱非空），
它们是**一般线性代数**，**不是缺口①的解答**。保留是因为：
* `exists_real_eigenvector_of_matrix_symm` 形式化了 C-C-M 的 `T` 的**谱存在性**；
* `exists_real_eigenvector` 的实部/虚部技巧在别处可能有用。

**但它们不减少缺口①的任何一条。**

## 与报告的关系

`数学家-核验记录/CCM-单重性-结构分析-2026-10-19.md`、
`CCM-路线整体判断-2026-10-19.md`。
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace RHProvability.CCMEven

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### 1. `T.map ofReal` 的实部就是 `T` 作用在实部上 -/

/-- 实矩阵 `T` 幂等延拓到 `ℂ^n` 后，取实部与「先取实部再作用」一致。 -/
theorem map_ofReal_mulVec_re (T : Matrix n n ℝ) (v : n → ℂ) :
    (fun i => (((T.map (algebraMap ℝ ℂ)) *ᵥ v) i).re) = T *ᵥ (fun i => (v i).re) := by
  funext i
  have h : (((T.map (algebraMap ℝ ℂ)) *ᵥ v) i).re
      = ∑ j, T i j * (v j).re := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_re]
    simp
  rw [h]
  rfl

/-- 同一件事的虚部版本。 -/
theorem map_ofReal_mulVec_im (T : Matrix n n ℝ) (v : n → ℂ) :
    (fun i => (((T.map (algebraMap ℝ ℂ)) *ᵥ v) i).im) = T *ᵥ (fun i => (v i).im) := by
  funext i
  have h : (((T.map (algebraMap ℝ ℂ)) *ᵥ v) i).im
      = ∑ j, T i j * (v j).im := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_im]
    simp
  rw [h]
  rfl

/-! ### 2. 主定理：实特征值有实特征向量 -/

/-- **核心引理**：若实矩阵 `T` 在 `ℂ^n` 上有非零特征向量 `v`（特征值 `λ` 为实数），
则 `T` 在 `ℝ^n` 上有非零特征向量，同一特征值。

证明只取 `v` 的实部或虚部——不需要谱定理。
-/
theorem exists_real_eigenvector (T : Matrix n n ℝ) (lam : ℝ) (v : n → ℂ) (hv : v ≠ 0)
    (h : (T.map (algebraMap ℝ ℂ)) *ᵥ v = lam • v) :
    ∃ w : n → ℝ, w ≠ 0 ∧ T *ᵥ w = lam • w := by
  have hre : T *ᵥ (fun i => (v i).re) = fun i => lam * (v i).re := by
    have := congrFun (map_ofReal_mulVec_re T v) 
    -- 左边：re of (T.map ofReal *ᵥ v) = re of (lam • v)
    ext i
    rw [← this]
    rw [show (fun i => (v i).re) = fun i => (v i).re from rfl] at *
    rw [h]
    simp [Pi.smul_apply]
  have him : T *ᵥ (fun i => (v i).im) = fun i => lam * (v i).im := by
    have := congrFun (map_ofReal_mulVec_im T v)
    ext i
    rw [← this]
    rw [h]
    simp [Pi.smul_apply]
  by_cases h1 : (fun i => (v i).re) ≠ 0
  · refine ⟨fun i => (v i).re, h1, ?_⟩
    ext i
    rw [hre]
    simp
  · push Not at h1
    have h2 : (fun i => (v i).im) ≠ 0 := by
      intro h2
      apply hv
      funext i
      have hi1 : (v i).re = 0 := by
        have := congrFun h1 i; simpa using this
      have hi2 : (v i).im = 0 := by
        have := congrFun h2 i; simpa using this
      exact Complex.ext hi1 hi2
    refine ⟨fun i => (v i).im, h2, ?_⟩
    ext i
    rw [him]
    simp

/-! ### 3. `γ`（复共轭）在实向量上不动 -/

/-- 复共轭 `γ` 逐点作用。 -/
noncomputable def conjVec (v : n → ℂ) : n → ℂ := fun i => starRingEnd ℂ (v i)

/-- 实向量嵌入 `ℂ^n` 后被 `γ` 固定：`γ ξ = ξ`。 -/
theorem conjVec_ofReal (w : n → ℝ) :
    conjVec (fun i => (w i : ℂ)) = fun i => (w i : ℂ) := by
  funext i
  simp [conjVec]

/-! ### 4. 合起来：`γ`-不动特征向量存在 -/

/-- **实特征向量在复共轭下不动**——这是平凡的，但**不是** C-C-M 的「偶」。

⚠️ 此定理此前被当作「缺口①的『偶』自动成立」的证据，**那是误读，已撤回**。
这里的不动点是**反线性**的复共轭 `conj`，而 C-C-M 的 `γ(V_j) = V_{−j}` 是**复线性**的；
`fix(conj)`（实向量）与 `fix(γ)`（偶向量）互不包含。详见文件头。 -/
theorem exists_conj_fixed_real_eigenvector (T : Matrix n n ℝ) (lam : ℝ) (v : n → ℂ)
    (hv : v ≠ 0) (h : (T.map (algebraMap ℝ ℂ)) *ᵥ v = lam • v) :
    ∃ w : n → ℝ, w ≠ 0 ∧ T *ᵥ w = lam • w ∧
      conjVec (fun i => (w i : ℂ)) = fun i => (w i : ℂ) := by
  obtain ⟨w, hw, hwT⟩ := exists_real_eigenvector T lam v hv h
  exact ⟨w, hw, hwT, conjVec_ofReal w⟩

/-! ### 5. 「存在」那一半：实对称算子必有实特征值（谱定理）

第 4 节把缺口①的「偶」消掉了，但它仍以「给定一个实特征值」为前提。
本节补上「**存在**」：有限维实内积空间上对称算子的谱非空，且特征向量可取实。

于是缺口①的完整链条是：

* 「存在」——谱定理（本节，无条件）；
* 「实/偶」——第 4 节（无条件）；
* 「**简单**」——**唯一的剩余假设**。
-/

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- **实对称算子的谱非空**：有限维非平凡实内积空间上，`T.IsSymmetric`
必有实特征值与相应非零特征向量。

由 Mathlib 谱定理（`LinearMap.IsSymmetric.eigenvectorBasis`）直接给出：
`eigenvectorBasis` 是 `OrthonormalBasis`，其第 `0` 个向量非零且是特征向量。 -/
theorem exists_real_eigenvector_of_isSymmetric (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) :
    ∃ (μ : ℝ) (v : E), v ≠ 0 ∧ T v = μ • v := by
  have hn : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  let i : Fin (Module.finrank ℝ E) := ⟨0, hpos⟩
  exact ⟨hT.eigenvalues hn i, hT.eigenvectorBasis hn i,
    (hT.eigenvectorBasis hn).orthonormal.ne_zero i, hT.apply_eigenvectorBasis hn i⟩

/-- **矩阵版本**：实对称矩阵 `M`（`M = Mᵀ`）作为 `ℝ^n` 上的算子的谱非空、特征值实。

桥接用 Mathlib 的 `Matrix.isSymmetric_toEuclideanLin_iff`
（`A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian`）。
缺的一环 `M.IsSymm → M.IsHermitian` 是初等的：`Mᴴ = Mᵀ.map star`，而对 `ℝ` 有 `star = id`。 -/
theorem exists_real_eigenvector_of_matrix_symm
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (M : Matrix n n ℝ) (hM : M.IsSymm) :
    ∃ (μ : ℝ) (v : EuclideanSpace ℝ n), v ≠ 0 ∧ M.toEuclideanLin v = μ • v := by
  have hHerm : M.IsHermitian := by
    have hmap : Mᵀ.map star = Mᵀ := by ext i j; simp
    show Mᴴ = M
    rw [Matrix.conjTranspose, hmap]
    exact hM
  exact exists_real_eigenvector_of_isSymmetric M.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm)

end Spectral


end RHProvability.CCMEven
