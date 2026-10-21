/-
# `N_off`: the off-line zero count, and why a density bound is not a route to RH

Written after an independent reviewer (调研员) required, in this order: **first say why the density
route may not reach RH, then (only then) look at what it is good for.** So the negative analysis comes
first and occupies most of this file's prose; the formal object is small and is here so that later
statements have something to be about.

## 1. The object

`offLineCount T` counts the zeros of `ζ` in the closed strip box at height `T` that are **not** on the
critical line. It is the quantity that a *density* statement bounds. Two facts are proved below and
they pin it exactly:

* `stripCount T = lineCount T + offLineCount T` — the two counts partition the strip count;
* `RiemannHypothesis ↔ ∀ T, offLineCount T = 0` — RH is *exactly* the vanishing of this count.

So `offLineCount` is the right formal home for "how many zeros are off the line", and RH is the
statement that it is identically zero. Everything else on this route is a bound on it.

## 2. Why a bound on `N_off` does not reach RH (the required analysis, first)

A density theorem has the shape

  `∃ δ > 0, ∃ T₀, ∀ T ≥ T₀, N_off(T) ≤ T^{1-δ}`,

and there is a machine-checked obstruction to reading RH off it — `densityBound_does_not_force_zero`:
the schema "a bound of that shape forces `f ≡ 0`" is false, refuted by the constant function `1`.

**Scope of that refutation, stated carefully** (a reviewer has already caught this development once for
the mirror-image error, so the scope is spelled out rather than implied). The refutation is a statement
about the *schema* — an implication quantified over all `f : ℝ → ℕ`. It is therefore valid as such: it
shows the density bound carries **no purely logical** route to `N_off ≡ 0`. It does **not** show that
`ζ` can have an off-line zero, and it does not show that the density bound is worthless: `ζ`'s extra
structure might exclude sparse violations.

But *that* is the point: the missing step is precisely "off-line zeros cannot be sparse, and cannot
persist to arbitrarily large height at any density". Excluding a sparse-but-infinite family of
off-line zeros is not a counting statement; it is a location statement, and it is RH-strength. So the
density route terminates at "fewer off-line zeros than we can rule out", never at "none" — unless the
extra step is supplied, and that step is the theorem.

**Consequence for target-setting:** a density bound is a legitimate *partial* result (Ingham's `δ = 1/4`
is a real theorem) and an illegitimate *route*. It should not be registered as a step towards RH.

## 3. What the file buys

Not progress on RH. It buys the formal object `N_off`, the partition identity, the exact equivalence
`RH ↔ N_off ≡ 0`, and a machine-checked scope limit on the density shape. That is the honest yield.
-/
import RHProvability.LineCountClosed

namespace RHProvability

open Set

/-- The zeros of `ζ` inside the closed strip box at height `T` that are **not** on the critical line. -/
def zerosOffLineBox (T : ℝ) : Set ℂ := zerosInStripBox T \ zerosOnLineBox T

/-- `N_off(T)`: the number of off-line zeros at height `≤ T`. This is the quantity that a density
theorem bounds, and RH is the assertion that it vanishes for every `T`. -/
noncomputable def offLineCount (T : ℝ) : ℕ := (zerosOffLineBox T).ncard

theorem finite_zerosOffLineBox (T : ℝ) : (zerosOffLineBox T).Finite :=
  (finite_zerosInStripBox T).sdiff

theorem zerosOffLineBox_subset (T : ℝ) : zerosOffLineBox T ⊆ zerosInStripBox T :=
  Set.sdiff_subset

/-- `N_off(T) ≤ N_strip(T)`: the off-line zeros are a sub-collection of the strip zeros. -/
theorem offLineCount_le_stripCount (T : ℝ) : offLineCount T ≤ stripCount T :=
  Set.ncard_le_ncard (zerosOffLineBox_subset T) (finite_zerosInStripBox T)

/-- **The partition identity**: the strip zeros are the on-line zeros together with the off-line ones.
This is what makes `N_off` the correct complement of `N_line`. -/
theorem stripCount_eq_lineCount_add_offLineCount (T : ℝ) :
    stripCount T = lineCount T + offLineCount T := by
  have h := Set.ncard_sdiff_add_ncard_of_subset (zerosOnLineBox_subset T) (finite_zerosInStripBox T)
  simp only [offLineCount, stripCount, lineCount, zerosOffLineBox] at *
  omega

/-- **RH is exactly the vanishing of `N_off`.** Not a bound, not a density: the count is zero at every
height. This is the statement a density theorem would have to be upgraded into. -/
theorem riemannHypothesis_iff_offLineCount_eq_zero :
    RiemannHypothesis ↔ ∀ T : ℝ, offLineCount T = 0 := by
  constructor
  · intro h T
    have hcounts : lineCount T = stripCount T := (countsEq_iff_riemannHypothesis).mpr h T
    have hpart := stripCount_eq_lineCount_add_offLineCount T
    omega
  · intro h
    refine (countsEq_iff_riemannHypothesis).mp fun T => ?_
    have hpart := stripCount_eq_lineCount_add_offLineCount T
    have := h T
    omega

/-- **The schema refutation, with its scope stated.**

The implication "a density-shaped bound forces `f ≡ 0`" is false: the constant function `1` satisfies
the bound and is never zero.

Scope: this is a statement about the *schema*, quantified over all `f : ℝ → ℕ`. It shows that no purely
logical route goes from a density bound to `N_off ≡ 0`, so any route must add `ζ`-specific structure —
and the structure needed ("off-line zeros are not sparse, at any height") is itself RH-strength. It
does **not** assert anything about whether `ζ` has off-line zeros. -/
theorem densityBound_does_not_force_zero :
    ¬ ∀ f : ℝ → ℕ,
        (∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (f T : ℝ) ≤ T ^ (1 - δ)) →
          ∀ T : ℝ, f T = 0 := by
  intro h
  have hb : ∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (((fun _ => 1) T : ℕ) : ℝ) ≤ T ^ (1 - δ) := by
    refine ⟨1 / 2, by norm_num, 1, fun T hT => ?_⟩
    have hT1 : (1 : ℝ) ≤ T := hT
    have hexp : (0 : ℝ) ≤ 1 - 1 / 2 := by norm_num
    have := Real.one_le_rpow hT1 hexp
    simpa using this
  have hz : (fun _ => 1 : ℝ → ℕ) 0 = 0 := h (fun _ => 1) hb 0
  exact one_ne_zero hz

end RHProvability
