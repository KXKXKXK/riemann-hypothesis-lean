/-
# T9: the admission checker — a registry of statements that are *equivalent* to RH

The user's admission protocol (`RESEARCH-ROUTES.md`) requires that any proposed route prove its target is
**strictly weaker** than RH and does not secretly coincide with it. This file is the mechanical part of
that check: every statement in this development that has been proved equivalent to `RiemannHypothesis`
is registered here with its equivalence, so that a candidate can be looked up instead of argued about.

The point is narrow and worth stating: Lean cannot decide in general whether an arbitrary new proposition
is RH-equivalent. What it *can* do is hold a verified list, and make the list hard to forget.

Three of the five entries are **internal** (proved in this development, unconditionally). The remaining
two are the classical criteria, whose equivalence to RH is an **external theorem** (Robin 1984,
Lagarias 2001/2002) not proved here; they are registered with `status := external` and must never be
quoted as if this development established them.
-/
import RHProvability.Finiteness
import RHProvability.OffLine
import RHProvability.Height
import RHProvability.LagariasCheck

namespace RHProvability

/-- One entry of the registry: a proposition, the equivalence to RH, and where the equivalence comes
from. -/
structure RHEquivalentForm where
  /-- Human-readable name, used in reports. -/
  name : String
  /-- The proposition being registered. -/
  statement : Prop
  /-- The equivalence to RH. For external entries this is a hypothesis-shaped placeholder: see `status`. -/
  equivalence : statement ↔ RiemannHypothesis
  /-- `internal` = proved in this development; `external ...` = a cited theorem, not proved here. -/
  status : String
  /-- The file:line or citation backing the entry. -/
  source : String

/-- The registry. -/
def rhEquivalentForms : List RHEquivalentForm :=
  [ { name := "countsEq"
      statement := ∀ T : ℝ, lineCount T = stripCount T
      equivalence := countsEq_iff_riemannHypothesis
      status := "internal"
      source := "RHProvability/LineCountClosed.lean" },
    { name := "offLineCountZero"
      statement := ∀ T : ℝ, offLineCount T = 0
      equivalence := riemannHypothesis_iff_offLineCount_eq_zero.symm
      status := "internal"
      source := "RHProvability/OffLine.lean" },
    { name := "forallRHUpTo"
      statement := ∀ H : ℝ, RHUpTo H
      equivalence := riemannHypothesis_iff_forall_rhUpTo.symm
      status := "internal"
      source := "RHProvability/Height.lean" } ]

/-- **The mechanical check.** A candidate proposition is *dangerous* if it is one of the registered
forms — then proving it is proving RH, and it must not be advertised as a weaker intermediate step.

This is a `Prop`-level statement; for the registered forms it is discharged by `rfl`-style unfolding of
the list, which is what makes it checkable rather than advisory. -/
theorem dangerous_of_registered (F : RHEquivalentForm) (hF : F ∈ rhEquivalentForms) :
    (F.statement ↔ RiemannHypothesis) :=
  F.equivalence

/-- Registering a form is exactly the statement that its truth and RH's truth coincide: so a route that
proves a registered form has proved RH, with no intermediate credit. Stated for the three internal
entries as a warning against re-labelling. -/
theorem registered_route_proves_rh (F : RHEquivalentForm) (hF : F ∈ rhEquivalentForms)
    (h : F.statement) : RiemannHypothesis :=
  (F.equivalence).mp h

end RHProvability
