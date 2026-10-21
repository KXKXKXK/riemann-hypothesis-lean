/-
# Lagarias's elementary criterion, and why its non-strictness is structurally useful

An external auditor suggested switching the main line of attack from Robin's criterion to Lagarias's:
Robin's inequality is **strict**, which blocks the `∀ k`-shaping route to a decidable matrix, while
Lagarias's criterion is **non-strict**, which is exactly the shape `le_iff_forall_lt_upper` (item 11)
handles.

This file:

1. records the exact statement, matching the existing Lean formalization
   (`kimihiro64/Robin1984`, `Challenge.lean`, `LagariasElementaryCriterion`),
2. proves the elementary facts that pin the statement down at `n = 1` — in particular that both sides
   are equal there, so **any strict version is false**, which is precisely why the shape matters,
3. proves the general shaping lemma for non-strict comparisons against a descending upper
   approximation (this generalises item 11, which only covered a constant factor), and
4. states the resulting `Π⁰₁` form of Lagarias's criterion.

## What is *not* here

`RiemannHypothesis ↔ lagariasCriterion` is **Lagarias's theorem** (2001/2002) and is not proved in
this development. `lagariasCriterion` is a definition; nothing below claims it is equivalent to RH.
The comparison itself still involves `exp (H_n) · log (H_n)`, so the `∀ k` matrix is not yet a
rational computation — that is the same outstanding task as before (`TaskCertifiedLogLogBounds`).
-/
import Mathlib.NumberTheory.Harmonic.Defs
import RHProvability.Robin

namespace RHProvability

open Filter
open scoped Topology

/-! ## The criterion -/

/-- The right-hand side of Lagarias's inequality: `H_n + exp(H_n) · log(H_n)`, with `H_n` the `n`-th
harmonic number (`harmonic n` in Mathlib, a rational). -/
noncomputable def lagariasRHS (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- Lagarias's inequality at `n`: `σ(n) ≤ H_n + exp(H_n) · log(H_n)`.

Note the inequality is **non-strict** — this is not an accident, see `lagarias_strict_fails_at_one`. -/
def lagariasTest (n : ℕ) : Prop := (sigmaNat n : ℝ) ≤ lagariasRHS n

/-- **Lagarias's elementary criterion**: the inequality holds for every `n ≥ 1`.

Equivalence with `RiemannHypothesis` is Lagarias's theorem and is **not** proved here. -/
def lagariasCriterion : Prop := ∀ n : ℕ, 0 < n → lagariasTest n

/-! ## Elementary facts that pin the statement down -/

/-- At `n = 1`: `σ(1) = 1`, `H_1 = 1` and `log 1 = 0`, so the right-hand side is exactly `1`. -/
theorem harmonic_one' : harmonic 1 = 1 := by
  simp [harmonic]

theorem lagariasRHS_one : lagariasRHS 1 = 1 := by
  unfold lagariasRHS
  simp [Real.log_one]

/-- The inequality holds at `n = 1`, with equality. -/
theorem lagariasTest_one : lagariasTest 1 := by
  unfold lagariasTest
  rw [lagariasRHS_one, sigmaNat_one]
  norm_num

/-- **The strict version is false at `n = 1`.** Both sides equal `1`, so replacing `≤` by `<` makes
the criterion fail immediately. This is the machine-checked reason why Lagarias's criterion is stated
non-strictly, and why the `∀ k`-shaping lemma for non-strict comparisons is the right tool. -/
theorem lagarias_strict_fails_at_one : ¬ ((sigmaNat 1 : ℝ) < lagariasRHS 1) := by
  rw [lagariasRHS_one, sigmaNat_one]
  norm_num

/-! ## The general shaping lemma for non-strict comparisons -/

/-- **Shaping lemma (non-strict).** If `u` converges to `g` from strictly above, then `f ≤ g` is
equivalent to `∀ k, f < u k`.

This generalises `le_iff_forall_lt_upper` (item 11), which only covered a constant factor `c·g`; here
the right-hand side may be any real `g` (in applications, a transcendental quantity such as
`H_n + e^{H_n} log H_n`), and the approximation `u k` is what a computation would produce. -/
theorem le_iff_forall_lt_upperOf {g : ℝ} {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 g))
    (hupper : ∀ k, g < u k) {f : ℝ} : f ≤ g ↔ ∀ k, f < u k := by
  constructor
  · intro h k
    exact lt_of_le_of_lt h (hupper k)
  · intro h
    have hle : ∀ᶠ k in atTop, f ≤ u k := Eventually.of_forall fun k => le_of_lt (h k)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hu hle

/-- **The `Π⁰₁` form of Lagarias's criterion.** Given, for each `n`, a family `u n ·` that converges
to the right-hand side from above, the criterion is equivalent to a `∀ n ∀ k` statement whose matrix
compares `σ(n)` with `u n k`.

Because the criterion is non-strict, no strictness is lost here — in contrast to Robin's inequality,
where the corresponding step is impossible (item 17). -/
theorem lagariasCriterion_iff_forall_upper (u : ℕ → ℕ → ℝ)
    (hu : ∀ n : ℕ, Tendsto (fun k => u n k) atTop (𝓝 (lagariasRHS n)))
    (hupper : ∀ n k, lagariasRHS n < u n k) :
    lagariasCriterion ↔ ∀ n : ℕ, 0 < n → ∀ k : ℕ, (sigmaNat n : ℝ) < u n k := by
  constructor
  · intro h n hn k
    exact (le_iff_forall_lt_upperOf (hu n) (hupper n)).mp (h n hn) k
  · intro h n hn
    exact (le_iff_forall_lt_upperOf (hu n) (hupper n)).mpr fun k => h n hn k

end RHProvability
