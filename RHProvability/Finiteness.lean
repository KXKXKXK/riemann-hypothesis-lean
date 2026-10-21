/-
# Finiteness certificates for a `Π⁰₁` target: what an explicit cutoff can and cannot buy

Route B of the current research plan is:

> find an explicit natural number `N` such that **if the criterion holds for every `n ≤ N`, then it
> holds for every `n`**; then verify the finitely many instances below `N`, and RH follows.

This file pins that shape down exactly and proves, in Lean and with no extra hypothesis, three
things about it:

1. **The `∃ N` form is vacuous.** `∃ N, IsCutoff test N` holds for *every* predicate `test`
   (`exists_isCutoff`). As a statement, "there exists a cutoff" carries no information whatsoever
   about `test`.
2. **The characterization.** If `test` fails somewhere, the admissible cutoffs are exactly the
   natural numbers at or above the *first* failure (`isCutoff_iff_firstFail_le`). So the set of usable
   cutoffs is an upper ray whose left endpoint is the least counterexample — i.e. its position is
   determined by the object we are trying to understand, not by the proof.
3. **The collapse.** As soon as the finitely many checks are in hand, the cutoff assertion is
   *equivalent* to the conclusion (`isCutoff_iff_forall`). Consequently no cutoff can be a weakening
   of the target: `IsCutoff test N ∧ (∀ n ≤ N, test n)` is equivalent to `∀ n, test n`
   (`exists_isCutoff_and_checks_iff`).

The last point is the mathematical content of this file. It says the "finiteness theorem" route is
not a halfway house: a *proved* cutoff together with the free finite checks **is** the theorem, and a
*postulated* cutoff together with the free finite checks **is a postulate of the theorem**. There is
no third option. Applied to Lagarias's criterion this is `lagarias_cutoff_collapse` below.

## What this does not say

It does not say RH is unprovable, and it does not say finite verification is useless. It says the
particular shape "cutoff of the *same* predicate" cannot be a strict weakening. A decomposition that
*does* split RH into a finite part and a genuinely different tail lives elsewhere in this development
(`RHProvability.StripCount`, `RHProvability.Backlund`, `RHProvability.LineCountClosed`), where the
tail is a statement about zero counts rather than about the same arithmetic predicate.

The equivalence `RiemannHypothesis ↔ lagariasCriterion` is **Lagarias's theorem** and is not proved
here; nothing below assumes it either.
-/
import RHProvability.Lagarias

namespace RHProvability

/-! ## The cut-off predicate -/

/-- `IsCutoff test N` says: **checking `test` up to `N` suffices**. If every `n ≤ N` passes, then
every `n` passes.

Equivalently (see `isCutoff_iff`): every counterexample forces a counterexample below `N`. -/
def IsCutoff (test : ℕ → Prop) (N : ℕ) : Prop :=
  (∀ n, n ≤ N → test n) → ∀ n, test n

variable {test : ℕ → Prop}

/-- The counterexample form of `IsCutoff`: every failure drags a small failure along with it. -/
theorem isCutoff_iff (N : ℕ) :
    IsCutoff test N ↔ ∀ n, ¬ test n → ∃ m, m ≤ N ∧ ¬ test m := by
  constructor
  · intro h n hn
    by_contra hcon
    have hall : ∀ m, m ≤ N → test m := by
      intro m hm
      by_contra hm'
      exact hcon ⟨m, hm, hm'⟩
    exact hn (h hall n)
  · intro h hall n
    by_contra hn
    obtain ⟨m, hm, hmn⟩ := h n hn
    exact hmn (hall m hm)

/-- Cut-offs are **upward closed**: if `N` suffices then so does any larger `M`. -/
theorem isCutoff_mono {N M : ℕ} (h : IsCutoff test N) (hNM : N ≤ M) : IsCutoff test M := by
  intro hall
  exact h fun n hn => hall n (le_trans hn hNM)

/-- **The `∃ N` formulation is vacuous.** For an arbitrary predicate `test : ℕ → Prop`, some cut-off
always exists — with `N = 0` if `test` holds everywhere, and with `N` the first failure otherwise.

So "there exists an `N` such that checking up to `N` suffices" is *not* a mathematical conjecture
about `test`; it is a tautology. Any real content must be in a **specified** `N` and in a proof that
does not already contain the conclusion. -/
theorem exists_isCutoff (test : ℕ → Prop) : ∃ N, IsCutoff test N := by
  by_cases h : ∀ n, test n
  · exact ⟨0, fun _ => h⟩
  · rw [not_forall] at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, fun hall => absurd (hall n le_rfl) hn⟩

/-- **The collapse.** Once the finitely many checks below `N` are in hand, the cut-off assertion at
`N` is *equivalent* to the full universal statement.

Read contrapositively: there is no way for a proved cut-off to be weaker than the theorem it is
supposed to deliver. -/
theorem isCutoff_iff_forall (N : ℕ) (hchk : ∀ n, n ≤ N → test n) :
    IsCutoff test N ↔ ∀ n, test n :=
  ⟨fun h => h hchk, fun h _ => h⟩

/-- The same collapse stated as a characterisation of the **route-B target**: "there is a cut-off,
and the checks below it pass" is equivalent to "the universal statement holds". The `∃ N` adds
nothing, and the finite checks are free. -/
theorem exists_isCutoff_and_checks_iff :
    (∃ N, IsCutoff test N ∧ ∀ n, n ≤ N → test n) ↔ ∀ n, test n := by
  constructor
  · rintro ⟨N, hcut, hchk⟩
    exact hcut hchk
  · intro h
    exact ⟨0, fun _ => h, fun n _ => h n⟩

/-- The least counterexample of `test`, as a noncomputable object. It is deliberately *not* given a
computable definition: extracting it requires deciding `test` at infinitely many arguments, which is
the structure the cut-off route keeps trying to have for free. -/
noncomputable def firstFail {test : ℕ → Prop} (h : ∃ n, ¬ test n) : ℕ := by
  classical
  exact Nat.find h

theorem firstFail_spec {test : ℕ → Prop} (h : ∃ n, ¬ test n) : ¬ test (firstFail h) := by
  classical
  unfold firstFail
  exact Nat.find_spec h

theorem le_firstFail {test : ℕ → Prop} (h : ∃ n, ¬ test n) {m : ℕ} (hm : ¬ test m) :
    firstFail h ≤ m := by
  classical
  unfold firstFail
  exact Nat.find_min' h hm

/-- **Characterisation of the admissible cut-offs.** If `test` fails somewhere, then `N` is a cut-off
exactly when `N` is at or beyond the *first* failure. So the set of usable cut-offs is the upper ray
`[first failure, ∞)`: its left endpoint is a property of `test`, and any proof that a *smaller* `N`
suffices must already decide `test` everywhere. -/
theorem isCutoff_iff_firstFail_le {test : ℕ → Prop} (h : ∃ n, ¬ test n) (N : ℕ) :
    IsCutoff test N ↔ firstFail h ≤ N := by
  constructor
  · intro hcut
    by_contra hlt
    rw [not_le] at hlt
    have hall : ∀ n, n ≤ N → test n := by
      intro n hn
      by_contra hnt
      have := le_firstFail h hnt
      omega
    exact firstFail_spec h (hcut hall (firstFail h))
  · intro hle hall
    exact absurd (hall (firstFail h) hle) (firstFail_spec h)

/-! ## Applied to the Lagarias predicate -/

/-- The predicate whose cut-off route B asks about: "`n` is a positive integer satisfying Lagarias's
inequality". Its universal statement is `lagariasCriterion`. -/
def lagariasPass (n : ℕ) : Prop := 0 < n → lagariasTest n

theorem forall_lagariasPass_iff : (∀ n, lagariasPass n) ↔ lagariasCriterion := Iff.rfl

/-- **The collapse, for Lagarias's criterion.** Given the finitely many verified instances `n ≤ N`,
a cut-off certificate at `N` is equivalent to Lagarias's criterion itself.

Therefore: proving such a certificate at any `N` whose checks one has actually verified *is* proving
the criterion, and postulating the certificate is postulating the criterion. Route B, in the shape
"find `N` such that checking to `N` suffices", has no non-circular solution.

Note what is *not* claimed: `RiemannHypothesis ↔ lagariasCriterion` is Lagarias's theorem, unproved
here, so this theorem is about the criterion, not about RH directly. -/
theorem lagarias_cutoff_collapse (N : ℕ) (hchk : ∀ n, n ≤ N → lagariasPass n) :
    IsCutoff lagariasPass N ↔ lagariasCriterion :=
  isCutoff_iff_forall N hchk

/-- **Registry hygiene.** The cut-off target, written out in full, is *provably equivalent* to the
criterion. It must therefore never be listed as a separate open item or as a hypothesis weaker than
RH: adopting it as an assumption would be adopting the criterion as an assumption. -/
theorem lagariasCutoffTarget_iff_criterion :
    (∃ N, IsCutoff lagariasPass N ∧ ∀ n, n ≤ N → lagariasPass n) ↔ lagariasCriterion :=
  exists_isCutoff_and_checks_iff

/-- **Warning, added after an independent review: `IsCutoff` *alone* is strictly weaker than the
conclusion.** It is only the *conjunction* with the finite checks that is equivalent to the conclusion
(`isCutoff_iff_forall`).

Machine-checked witness: take `test n := n ≤ 3` and `N = 10`. The cut-off holds, because the hypothesis
"every `n ≤ 10` satisfies `n ≤ 3`" is already false; the conclusion is false as well. Hence
`∀ test N, IsCutoff test N → ∀ n, test n` is **false**, and any quotation of the results in this file
that drops the `hchk` hypothesis is quoting a false statement. (Raised by the reviewer who audited this
module on 2026-10-18; recorded as a theorem rather than a comment so it cannot be lost.) -/
theorem isCutoff_alone_does_not_imply :
    ¬ ∀ (test : ℕ → Prop) (N : ℕ), IsCutoff test N → ∀ n, test n := by
  intro h
  have hc : IsCutoff (fun n : ℕ => n ≤ 3) 10 := by
    intro hall
    have := hall 10 le_rfl
    omega
  have := h (fun n : ℕ => n ≤ 3) 10 hc 4
  omega

end RHProvability
