/-
# The topological content behind Gap 1 — and a second, independent proof of it

`LineFunction.lean` proves `OpenRealValuedLineFunction` (every real-valued continuous `Z` whose zero
set is exactly the critical-line zeros of `ζ`) by using the distance function to a closed set.

The reviewer at stage B (see `数学家-核验记录/RH-2026-10-19/B8-比对.md`) pointed out that the same
argument proves something **strictly stronger and completely unrelated to `ζ`**:

> every closed subset of `ℝ` is the zero set of some real-valued continuous function.

That is the real reason the registered "Gap 1" carries no RH content: the only `ζ`-specific input is
that the zero set is closed, and *any* closed set would do. This file records that fact as a
machine-checked theorem, and re-derives `OpenRealValuedLineFunction` from it — a **second independent
proof** of the same `Prop`, which also guards against a mistake in the first one.

## Status

Compiled with `lake env lean` against Lean v4.33.0 / Mathlib `db584cd6`.
**Not** part of this round's double check: the audited artifact of record is `LineFunction.lean`
(frozen after A/B). Everything here is new and must go through a fresh A/B round before being cited
as verified.
-/
import RHProvability.LineFunction

namespace RHProvability.Overview

open Metric

/-- **Any closed subset of `ℝ` is the zero set of a real-valued continuous function.** -/
theorem exists_continuous_zeroSet_of_isClosed {S : Set ℝ} (hS : IsClosed S) :
    ∃ Z : ℝ → ℝ, Continuous Z ∧ ∀ t : ℝ, (Z t = 0 ↔ t ∈ S) := by
  classical
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨fun _ => 1, continuous_const, ?_⟩
    intro t
    rw [hemp]
    constructor
    · intro h1; exact absurd h1 one_ne_zero
    · intro h2; exact absurd h2 (Set.notMem_empty t)
  · refine ⟨fun t => infDist t S, continuous_infDist_pt S, ?_⟩
    intro t
    exact (hS.mem_iff_infDist_zero hne (x := t)).symm

/-- **`OpenRealValuedLineFunction`, proved again — now from the general topological fact.** -/
theorem openRealValuedLineFunction' : OpenRealValuedLineFunction := by
  obtain ⟨Z, hZ, hiff⟩ :=
    exists_continuous_zeroSet_of_isClosed isClosed_zetaZeroSetOnCriticalLine
  exact ⟨Z, hZ, fun t => hiff t⟩

end RHProvability.Overview
