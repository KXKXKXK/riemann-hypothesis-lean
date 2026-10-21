/-
# The strip-box counting function `N(T)`-shaped count

`FiniteHeight.lean` used balls; a Backlund-type counting bound is about the **box**
`0 ≤ Re z ≤ 1`, `|Im z| ≤ T` instead. This file defines that box, proves it compact (so the zeros
inside it are finite), defines the count, and states RH in terms of the box.

Proved here: `isCompact_stripBox`, `finite_zerosInStripBox`, `stripCount_mono`,
`riemannHypothesis_iff_stripBox`, `not_riemannHypothesis_iff_exists_in_stripBox`.

Not proved here: **any bound on `stripCount T` in terms of `T`** — that is Backlund's theorem,
the analytic content of Route A step 2. Nothing in this file uses it or pretends to.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RHProvability.Counting

namespace RHProvability

open Complex
open scoped Real

/-- The closed critical-strip box up to height `T`: `0 ≤ Re z ≤ 1` and `|Im z| ≤ T`. -/
def stripBox (T : ℝ) : Set ℂ := {z | |z.im| ≤ T ∧ 0 ≤ z.re ∧ z.re ≤ 1}

/-- The box is compact: closed (preimage of a closed rectangle under `z ↦ (re z, im z)`) and
contained in a closed ball. For `T < 0` the box is empty. -/
theorem isCompact_stripBox (T : ℝ) : IsCompact (stripBox T) := by
  by_cases hT : 0 ≤ T
  · have hclosed : IsClosed (stripBox T) := by
      have h : stripBox T
          = (fun z : ℂ => (z.re, z.im)) ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-T) T) := by
        ext z
        simp only [stripBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
        rw [abs_le]
        tauto
      rw [h]
      exact (isClosed_Icc.prod isClosed_Icc).preimage (by fun_prop)
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (1 + |T|)) hclosed ?_
    rintro z ⟨him, h0, h1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : 1 + |T| - |z.re| - |z.im| ≥ 0 := by
      have h2 : |z.re| ≤ 1 := by
        rw [abs_of_nonneg h0]
        exact h1
      have h3 : |z.im| ≤ T := by simpa [abs_le] using him
      have h4 : T = |T| := by rw [abs_of_nonneg hT]
      linarith
    have hn := Complex.norm_le_abs_re_add_abs_im z
    linarith
  · push_neg at hT
    have hempty : stripBox T = ∅ := by
      ext z
      simp only [stripBox, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨him, -, -⟩
      have hnn := abs_nonneg z.im
      linarith
    rw [hempty]
    exact isCompact_empty

/-- Zeros of `ζ` in the strip box. -/
def zerosInStripBox (T : ℝ) : Set ℂ := {z | riemannZeta z = 0 ∧ z ∈ stripBox T}

/-- Only finitely many zeros in the strip box up to height `T`. -/
theorem finite_zerosInStripBox (T : ℝ) : (zerosInStripBox T).Finite := by
  have hfin : (stripBox T ∩ riemannZetaZeros).Finite :=
    (isCompact_stripBox T).inter_riemannZetaZeros_finite
  refine hfin.subset ?_
  rintro z ⟨hz, hbox⟩
  exact ⟨hbox, mem_riemannZetaZeros.mpr hz⟩

/-- The `N(T)`-shaped count: number of zeros of `ζ` in the strip box up to height `T`. -/
noncomputable def stripCount (T : ℝ) : ℕ := (zerosInStripBox T).ncard

/-- The count is monotone in the height. -/
theorem stripCount_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : stripCount T₁ ≤ stripCount T₂ := by
  refine Set.ncard_le_ncard ?_ (finite_zerosInStripBox T₂)
  rintro z ⟨hz, him, h0, h1⟩
  exact ⟨hz, abs_le.mpr ⟨by linarith [abs_le.mp him |>.1], by linarith [abs_le.mp him |>.2]⟩, h0, h1⟩

/-- A zero in the open strip lies in the box of height `‖z‖`. -/
theorem mem_stripBox_norm {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) : z ∈ stripBox ‖z‖ :=
  ⟨abs_im_le_norm z, le_of_lt h0, le_of_lt h1⟩

/-- **RH via the box count's underlying finite set.** For every height `T`, every zero in the box
of height `T` which lies in the open strip is on the critical line. -/
theorem riemannHypothesis_iff_stripBox :
    RiemannHypothesis ↔
      ∀ (T : ℝ), ∀ z ∈ (finite_zerosInStripBox T).toFinset,
        0 < z.re → z.re < 1 → z.re = 1 / 2 := by
  constructor
  · intro h T z hz h0 h1
    have hz' : z ∈ zerosInStripBox T := by simpa using hz
    exact riemannHypothesisStrip_unconditional h z h0 h1 hz'.1
  · intro h z hz htriv hne1
    have hstrip := zero_mem_strip_of_not_trivial hz htriv hne1
    have hmembox : z ∈ zerosInStripBox ‖z‖ := ⟨hz, mem_stripBox_norm hstrip.1 hstrip.2⟩
    have hmem : z ∈ (finite_zerosInStripBox ‖z‖).toFinset := by simpa using hmembox
    exact h ‖z‖ z hmem hstrip.1 hstrip.2

/-- **The negation, in the box form.** -/
theorem not_riemannHypothesis_iff_exists_in_stripBox :
    ¬ RiemannHypothesis ↔
      ∃ (T : ℝ) (z : ℂ), z ∈ (finite_zerosInStripBox T).toFinset ∧
        0 < z.re ∧ z.re < 1 ∧ z.re ≠ 1 / 2 := by
  rw [not_riemannHypothesis_iff_exists_off_line]
  constructor
  · rintro ⟨z, h0, h1, hz, hoff⟩
    refine ⟨‖z‖, z, ?_, h0, h1, hoff⟩
    have hmembox : z ∈ zerosInStripBox ‖z‖ := ⟨hz, mem_stripBox_norm h0 h1⟩
    simpa using hmembox
  · rintro ⟨T, z, hz, h0, h1, hoff⟩
    have hz' : z ∈ zerosInStripBox T := by simpa using hz
    exact ⟨z, h0, h1, hz'.1, hoff⟩

end RHProvability
