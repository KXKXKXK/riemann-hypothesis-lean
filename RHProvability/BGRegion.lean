/-
# Route exclusion (T1): the Bettin–Gonek link has a cliff at `θ = 1`, not a staircase

Bettin–Gonek, *The θ = ∞ conjecture implies the Riemann hypothesis*, Mathematika **63** (2017),
29–33, Theorem 1, **verbatim**:

> "Let θ > 0 and assume that for every ε > 0 we have I_N(0,T) ≪_ε T^{1+ε} for N in the range
> 2 ⩽ N ⩽ T^θ. Then ζ(s) has no zeros in the half-plane ℜs > 1/2 + 1/(2θ). In particular, if
> I_N(0,T) ≪_ε T^{1+ε} for 2 ⩽ N ⩽ T^θ with θ arbitrarily large, then the Riemann hypothesis
> is true."

The hypothesis `I_N(0,T) ≪ T^{1+ε}` is known (via the mollified second moment asymptotic
`lim I_{T^θ}(0,T)/T = 1 + 1/θ`) for `θ < 1/2` (Levinson 1974) and `θ < 4/7` (Conrey 1989).

This file records the **quantitative** reading of the conclusion, which decides whether the family
offers intermediate targets at all. With `bgEdge θ = 1/2 + 1/(2θ)`:

* `bgEdge` is **strictly decreasing** in `θ` (`bgEdge_strictAntiOn`);
* for `θ ≤ 1` the edge is `≥ 1` (`bgEdge_one_le_of_le_one`), so the half-plane `ℜs > bgEdge θ` sits
  inside the trivially zero-free half-plane `ℜs > 1` and the conclusion carries **zero information**;
* hence **every known instance is vacuous**: `θ ≤ 4/7 < 1` gives `1 < bgEdge θ`
  (`bgEdge_known_vacuous`);
* the first informative regime is exactly `θ > 1`, where the edge drops below `1`
  (`bgEdge_lt_one_iff`).

So improving `θ` from `4/7` to anything `≤ 1` would still produce a vacuous conclusion, and `θ > 1` is
exactly the regime the pre-1993 belief declared false (Bettin–Gonek quote: *"Initially it was believed
(see [2]) that (1.2) does not hold when θ > 1"*).

A genuine `θ > 1` instance would give a **fixed half-plane** zero-free region; by the truncated
explicit formula that alone yields a power-saving error term in the prime number theorem, far beyond
the known wedge `ℜs > 1 - c/log t`. So that rung is not a mild step either.

**Conclusion (route information, not new mathematics).** Between "known and vacuous" (`θ < 4/7`) and
"`θ = ∞` implies RH" (Bettin–Gonek) there is **no rung**: this family is not a staircase of weaker
targets with a foothold near the bottom.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RHProvability

/-- The right edge `1/2 + 1/(2θ)` of the zero-free half-plane produced by Bettin–Gonek (2017,
Theorem 1) from mollifier length `N = T^θ`. -/
noncomputable def bgEdge (θ : ℝ) : ℝ := 1 / 2 + 1 / (2 * θ)

/-- `bgEdge` is strictly decreasing on `θ > 0`: longer mollifiers give a stronger conclusion. -/
theorem bgEdge_strictAntiOn : StrictAntiOn bgEdge (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) < a := ha
  have hb0 : (0 : ℝ) < b := hb
  have h2a : (0 : ℝ) < 2 * a := by linarith
  have h2b : (0 : ℝ) < 2 * b := by linarith
  unfold bgEdge
  have h : 1 / (2 * b) < 1 / (2 * a) := one_div_lt_one_div_of_lt h2a (by linarith)
  linarith

/-- For `θ ≤ 1` the edge is at least `1`, so the conclusion `ℜs > 1/2 + 1/(2θ)` is **vacuous**: that
half-plane is contained in the trivially zero-free half-plane `ℜs > 1`. -/
theorem bgEdge_one_le_of_le_one {θ : ℝ} (hθ : 0 < θ) (h : θ ≤ 1) : 1 ≤ bgEdge θ := by
  have h2θ : (0 : ℝ) < 2 * θ := by linarith
  have hge : (1 : ℝ) / 2 ≤ 1 / (2 * θ) := one_div_le_one_div_of_le h2θ (by linarith)
  unfold bgEdge
  linarith

/-- Strict version: for `θ < 1` the edge is strictly inside `ℜs > 1`, so *a fortiori* vacuous. -/
theorem bgEdge_one_lt_of_lt_one {θ : ℝ} (hθ : 0 < θ) (h : θ < 1) : 1 < bgEdge θ := by
  have h2θ : (0 : ℝ) < 2 * θ := by linarith
  have hlt : (1 : ℝ) / 2 < 1 / (2 * θ) := one_div_lt_one_div_of_lt h2θ (by linarith)
  unfold bgEdge
  linarith

/-- The first informative regime is `θ > 1`, where the edge drops strictly below `1`. -/
theorem bgEdge_lt_one_iff {θ : ℝ} (hθ : 0 < θ) : bgEdge θ < 1 ↔ 1 < θ := by
  have h2θ : (0 : ℝ) < 2 * θ := by linarith
  unfold bgEdge
  have step : (1 : ℝ) / 2 + 1 / (2 * θ) < 1 ↔ 1 / (2 * θ) < 1 / 2 := by
    constructor <;> intro h <;> linarith
  rw [step, div_lt_iff₀ h2θ]
  constructor <;> intro h <;> nlinarith

/-- **Every known instance of Bettin–Gonek's Theorem 1 is vacuous.** The hypothesis is known for
`θ < 4/7` (Conrey 1989; Levinson 1974 gives `θ < 1/2`), and at every such `θ` the conclusion is a
half-plane containing `ℜs > 1`, hence a tautology. -/
theorem bgEdge_known_vacuous {θ : ℝ} (hθ : 0 < θ) (h : θ ≤ 4 / 7) : 1 < bgEdge θ :=
  bgEdge_one_lt_of_lt_one hθ (by linarith)

/-- The vacuity threshold is exactly `θ = 1`: there the edge equals `1`. -/
theorem bgEdge_one : bgEdge 1 = 1 := by
  unfold bgEdge
  norm_num

end RHProvability
