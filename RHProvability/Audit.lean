/-
# Audit record: the three defects found by an external reader, kept as machine-checked facts

An external reader audited the delivered bundle and reported five findings. Three of them are
defects in *this project* (not in Mathlib), and rather than fix them silently this module preserves
them as compiled theorems, so the record cannot drift:

1. `pi01Old_trivially_inhabited` — the **old** `Pi01` structure (no computability field) was
   inhabited for *every* proposition `P` classically, so `Nonempty (Pi01 _)` was provable and the
   register entry "a `Π⁰₁` presentation of RH is an open problem" recorded nothing. Fixed in
   `Pi01.lean` by requiring `Computable check`.
2. `oldOpenEffectiveLogLogBounds_false` — the old register entry for `log log n` bounds was not an
   open problem but a **false** proposition (it contradicted density of `ℚ`). Replaced.
3. `conj_symmetry_in_mathlib` — an earlier version of this project claimed that Mathlib lacks
   `ζ(conj s) = conj (ζ s)`. It is present at `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:458`.
   The claim came from a grep restricted to `Mathlib/NumberTheory/LSeries/`, which violated this
   project's own rule (iteration 2 addendum) of scanning all of `Mathlib/` before saying "Mathlib
   lacks X".

The new definitions live in `Pi01.lean` and `Overview.lean`; this file is evidence, not API.
-/
import RHProvability.Pi01
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace RHProvability
namespace Audit

/-! ## Finding 1: the old `Pi01` was trivially inhabited -/

/-- The **old** definition, kept verbatim (minus the fix) to record the defect. -/
structure Pi01Old (P : Prop) where
  /-- The decidable check. -/
  check : ℕ → Bool
  /-- `P` is equivalent to the universal statement "every check passes". -/
  iff : P ↔ ∀ n, check n = true

/-- **The defect, machine-checked.** For every `P`, the old structure is inhabited: take the check
`if P then true else decide (n ≠ 0)`. So `Nonempty (Pi01Old P)` was not an open problem for any `P`,
and in particular not for `RH`. -/
theorem pi01Old_trivially_inhabited (P : Prop) : Nonempty (Pi01Old P) := by
  classical
  by_cases h : P
  · exact ⟨{ check := fun _ => true, iff := ⟨fun _ _ => rfl, fun _ => h⟩ }⟩
  · refine ⟨{ check := fun n => decide (n ≠ 0), iff := ⟨fun hp => absurd hp h, fun hall => ?_⟩ }⟩
    exact absurd (hall 0) (by decide)

/-- The same defect for the thresholded variant. -/
theorem pi01FromOld_trivially_inhabited (N : ℕ) (P : Prop) :
    ∃ check : ℕ → Bool, (P ↔ ∀ n, N ≤ n → check n = true) := by
  classical
  by_cases h : P
  · exact ⟨fun _ => true, ⟨fun _ _ _ => rfl, fun _ => h⟩⟩
  · refine ⟨fun n => decide (n < N), ⟨fun hp => absurd hp h, fun hall => ?_⟩⟩
    exact absurd (hall N le_rfl) (by simp)

/-! ## Finding 2: the old register entry was false, not open -/

/-- The old `OpenEffectiveLogLogBounds`, kept verbatim. Its second conjunct says that no rational
lies strictly between `q n` and `log log n`, which contradicts density of `ℚ`. -/
def OldEffectiveLogLogBounds : Prop :=
  ∃ q : ℕ → ℚ, ∀ n : ℕ, 5041 ≤ n → (q n : ℝ) < Real.log (Real.log (n : ℝ)) ∧
    ∀ a : ℚ, (q n : ℝ) < (a : ℝ) → (a : ℝ) < Real.log (Real.log (n : ℝ)) → False

/-- **The defect, machine-checked**: the old entry is *false*. -/
theorem oldEffectiveLogLogBounds_false : ¬ OldEffectiveLogLogBounds := by
  rintro ⟨q, hq⟩
  obtain ⟨h1, h2⟩ := hq 5041 (le_refl 5041)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn h1
  exact h2 a ha1 ha2

/-! ## Finding 3: conjugation symmetry is in Mathlib -/

/-- **Not a gap.** `ζ(conj s) = conj (ζ s)` is `riemannZeta_conj` in
`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:458`. Recorded here so that no future version of this
project can claim it is missing without contradicting a compiled theorem. -/
theorem conj_symmetry_in_mathlib (s : ℂ) : riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conj s

end Audit
end RHProvability
