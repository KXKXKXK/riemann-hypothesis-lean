/-
# The counting invariant: line zeros versus strip zeros

The proposed route to a `Π⁰₁` presentation of RH through zero counting needs a *counting invariant*
before any computation: if the number of zeros **on** the critical line up to height `T` always equals
the number of zeros **in** the strip up to height `T`, then no zero can be off the line.

This file sets up that invariant and proves the implication that does not require any computation.

## Three levels, kept distinct

Following the audit note, three different claims must not be conflated:

1. **Finite** — the set of zeros in the box is finite. Proved in `StripCount.lean`
   (`finite_zerosInStripBox`) and here (`finite_zerosOnLineBox`).
2. **Computable** — there is an algorithm computing the count. **Not proved, not claimed.** Both
   `stripCount` and `lineCount` are `noncomputable` (`Set.ncard` on a set defined by a `Prop`).
3. **Certified** — an algorithm's output comes with a Lean-checkable correctness proof. **Not done.**

Only level 1 is established. Nothing in this file is a computation.

## Two honest caveats

* **Multiplicity.** `Set.ncard` counts *distinct* zeros, whereas the classical `N(T)` counts zeros
  **with multiplicity**. For RH — which is about *existence* of zeros off the line — the distinct
  count is the relevant one, and the implication below is about existence. A multiplicity-aware
  version needs the order of vanishing at a zero, a different (and heavier) definition.
* **The converse is not proved.** `riemannHypothesis_of_counts_eq` shows counts-agree-everywhere
  implies RH. The reverse (RH implies the counts agree) additionally needs: no zero of `ζ` on the
  boundary line `Re z = 0` inside the box. Mathematically this follows from the functional equation
  (`ζ(0+it) = 0` would force `ζ(1-it) = 0`, impossible since `Re(1-it) = 1`), but the boundary case
  `Re s = 0` is *not* covered by `Reflection.lean`, whose reflection lemma assumes `0 < Re s < 1`.
  So the converse is a genuine gap, not an oversight.
-/
import RHProvability.StripCount

namespace RHProvability

open Complex

/-- Zeros of `ζ` in the closed strip box up to height `T` that lie on the critical line. -/
def zerosOnLineBox (T : ℝ) : Set ℂ :=
  {z | riemannZeta z = 0 ∧ z ∈ stripBox T ∧ z.re = 1 / 2}

/-- The `N_line(T)`-shaped count: number of **distinct** zeros on the critical line in the box.

`noncomputable`, like `stripCount`: finiteness is proved, computability is not. -/
noncomputable def lineCount (T : ℝ) : ℕ := (zerosOnLineBox T).ncard

/-- Zeros on the line are a subset of the zeros in the box (same region, same boundary convention,
same multiplicity rule: both use `ncard` of a set, so both count distinct points). -/
theorem zerosOnLineBox_subset (T : ℝ) : zerosOnLineBox T ⊆ zerosInStripBox T := by
  rintro z ⟨hz, hbox, -⟩
  exact ⟨hz, hbox⟩

/-- Level 1 for the line count: the set is finite (it sits inside a compact set). -/
theorem finite_zerosOnLineBox (T : ℝ) : (zerosOnLineBox T).Finite :=
  (finite_zerosInStripBox T).subset (zerosOnLineBox_subset T)

/-- **The basic inequality** `N_line(T) ≤ N_strip(T)`. -/
theorem lineCount_le_stripCount (T : ℝ) : lineCount T ≤ stripCount T :=
  Set.ncard_le_ncard (zerosOnLineBox_subset T) (finite_zerosInStripBox T)

/-- If the two counts agree at height `T`, then the two **sets** coincide: a finite set with a
subset of equal cardinality is the whole set. -/
theorem zerosOnLineBox_eq_of_counts_eq {T : ℝ} (h : lineCount T = stripCount T) :
    zerosOnLineBox T = zerosInStripBox T := by
  refine Set.eq_of_subset_of_ncard_le (zerosOnLineBox_subset T) ?_ (finite_zerosInStripBox T)
  have h' : lineCount T = stripCount T := h
  unfold lineCount stripCount at h'
  omega

/-- Agreement of the counts at height `T` forces every box zero at that height onto the line. -/
theorem re_eq_half_of_counts_eq {T : ℝ} (h : lineCount T = stripCount T)
    {z : ℂ} (hz : z ∈ zerosInStripBox T) : z.re = 1 / 2 := by
  have heq := zerosOnLineBox_eq_of_counts_eq h
  have hz' : z ∈ zerosOnLineBox T := heq ▸ hz
  exact hz'.2.2

/-- **The counting invariant implies RH.** If at every height the line count equals the strip
count, then every non-trivial zero in the strip lies on the critical line.

This is the "counting" skeleton of the Backlund–Turing route: the missing piece is the *certified
computation* of either count, which is exactly levels 2 and 3 above, and is not in this file. -/
theorem riemannHypothesis_of_counts_eq (h : ∀ T : ℝ, lineCount T = stripCount T) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_stripBox.mpr ?_
  intro T z hz h0 h1
  have hz' : z ∈ zerosInStripBox T := by simpa using hz
  exact re_eq_half_of_counts_eq (h T) hz'

/-- A useful reformulation of the invariant: it is enough to prove, for each height, that the line
count is *not smaller* than the strip count (the other inequality is free). -/
theorem riemannHypothesis_of_stripCount_le_lineCount
    (h : ∀ T : ℝ, stripCount T ≤ lineCount T) : RiemannHypothesis :=
  riemannHypothesis_of_counts_eq fun T =>
    le_antisymm (lineCount_le_stripCount T) (h T)

/-! ## Parametrising the line zeros by a real variable

A sign-change computation counts zeros in the real variable `t` along `s = 1/2 + it`, so the count
has to be transported to `ℝ` first. The map `t ↦ 1/2 + it` is injective, which makes the transport
exact (no multiplicity is hidden in the parametrisation; distinct `t` give distinct points). -/

/-- The zeros of `ζ` on the critical line, as a set of real ordinates up to height `T`. -/
def lineZerosUpTo (T : ℝ) : Set ℝ :=
  {t | riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 ∧ |t| ≤ T}

/-- The parametrisation `t ↦ 1/2 + it` is injective. -/
theorem injective_lineParam :
    Function.Injective fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  intro a b h
  have him := congrArg Complex.im h
  simpa using him

/-- The line zeros in the box are exactly the image of the real ordinates. -/
theorem image_lineZerosUpTo (T : ℝ) :
    (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) '' lineZerosUpTo T
      = zerosOnLineBox T := by
  ext z
  constructor
  · rintro ⟨t, ⟨hz, ht⟩, rfl⟩
    have him : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
    have hre : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re = 1 / 2 := by simp
    refine ⟨hz, ?_, hre⟩
    simp only [stripBox, Set.mem_ofPred_eq, him, hre]
    exact ⟨ht, by norm_num, by norm_num⟩
  · rintro ⟨hz, hbox, hre⟩
    refine ⟨z.im, ⟨?_, ?_⟩, ?_⟩
    · have hz' : ((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = z := by
        apply Complex.ext <;> simp [hre]
      rw [hz']; exact hz
    · have hb := hbox
      simp only [stripBox, Set.mem_ofPred_eq] at hb
      exact hb.1
    · apply Complex.ext <;> simp [hre]

/-- **The real-variable form of the line count**: `N_line(T)` is the number of ordinates `t` with
`|t| ≤ T` and `ζ(1/2 + it) = 0`. This is the object a sign-change computation would produce. -/
theorem lineCount_eq_ncard_lineZerosUpTo (T : ℝ) : lineCount T = (lineZerosUpTo T).ncard := by
  unfold lineCount
  rw [← image_lineZerosUpTo T]
  exact Set.ncard_image_of_injective _ injective_lineParam

/-- The ordinates are confined to `[-T, T]` at height `T`, so the search is over a compact interval. -/
theorem lineZerosUpTo_subset_Icc (T : ℝ) : lineZerosUpTo T ⊆ Set.Icc (-T) T := by
  rintro t ⟨-, ht⟩
  exact Set.mem_Icc.mpr (abs_le.mp ht)

end RHProvability
