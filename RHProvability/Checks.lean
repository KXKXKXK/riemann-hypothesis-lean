/-
# The `Π⁰₁`-shape layer: a decidable check, its counterexample, and the first failing index

`Counting.lean` and `StripCount.lean` reduce RH to statements about explicit finite sets, but those
statements are `noncomputable`: they use `Set.ncard` on a set defined by a `Prop`. A genuine `Π⁰₁`
formulation needs a *decidable* check `Q : ℕ → Prop` together with `RH ↔ ∀ n, Q n`.

This file supplies the logical shape of that formulation and nothing more.

Proved here:

* `AllChecksPass Q` — the universal statement `∀ n, Q n`;
* `not_allChecksPass_iff_counterexample` — failure of the universal statement is a counterexample;
* `allChecksPass_iff_no_counterexample` — the same equivalence in dual form;
* `allChecksPass_iff_decide` — the `Bool` form `∀ n, decide (Q n) = true`;
* `exists_min_counterexample` — a counterexample search terminates at the *first* failing index
  (this is the only statement in the file that genuinely consumes `DecidablePred Q`);
* `rh_counterexample_of_check` — wires the shape to `RiemannHypothesis`.

## What this file does **not** do

1. It does not exhibit a decidable `Q : ℕ → Prop` with `RiemannHypothesis ↔ AllChecksPass Q`.
2. It does not make `zeroCount` / `stripCount` computable.

The equivalence `¬ (∀ n, Q n) ↔ ∃ n, ¬ Q n` is classical logic and holds for **every** predicate,
decidable or not (check the axiom output: `not_allChecksPass_iff_counterexample` does not depend on
`DecidablePred`). So what is established here is a *target shape*, not the `Π⁰₁` classification.
-/
import RHProvability.StripCount

namespace RHProvability

variable (Q : ℕ → Prop)
variable [DecidablePred Q]

/-- A decidable predicate on natural numbers. -/
def AllChecksPass : Prop :=
  ∀ n : ℕ, Q n

theorem not_allChecksPass_iff_counterexample :
    ¬ AllChecksPass Q ↔ ∃ n : ℕ, ¬ Q n := by
  simp [AllChecksPass]

/-- The same statement in dual form: passing every check is having no counterexample. -/
theorem allChecksPass_iff_no_counterexample :
    AllChecksPass Q ↔ ¬ ∃ n : ℕ, ¬ Q n := by
  simp [AllChecksPass]

/-- The `Bool` form of the universal statement: every check returns `true`.
This is the shape a machine-checkable `∀ n, check n = true` statement takes. -/
theorem allChecksPass_iff_decide :
    AllChecksPass Q ↔ ∀ n : ℕ, decide (Q n) = true := by
  exact ⟨fun h n => decide_eq_true (h n), fun h n => of_decide_eq_true (h n)⟩

/-- **Termination of the counterexample search.** If some index fails, then there is a *least*
failing index: everything below it passes. This is the only statement here that uses
`DecidablePred Q` essentially (via `Nat.find`). -/
theorem exists_min_counterexample (h : ∃ n : ℕ, ¬ Q n) :
    ∃ n : ℕ, ¬ Q n ∧ ∀ m : ℕ, m < n → Q m := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro m hm
  exact not_not.mp (Nat.find_min h hm)

/-- **The shape, wired to RH.** If RH is equivalent to a statement of the form "every check
passes" for a decidable `Q`, then a failing check is exactly a counterexample to RH. -/
theorem rh_counterexample_of_check
    (h : RiemannHypothesis ↔ AllChecksPass Q) :
    ¬ RiemannHypothesis ↔ ∃ n : ℕ, ¬ Q n := by
  rw [h, not_allChecksPass_iff_counterexample]

end RHProvability
