/-
# An abstract provability interface, and what can be *proved* about independence

This file is the replacement for the `opaque` scaffold. Design decisions:

* `Prov` is not `opaque`. It is a *parameter*: an arbitrary relation `Set Sent → Sent → Prop`
  bundled with the four structural laws that any syntactic provability relation for a
  classical first-order theory satisfies (hypothesis rule, weakening, modus ponens,
  ex falso / contradiction). Everything below is a theorem *about* such a relation, proved
  by the kernel, with no axioms and no `sorry`.
* The consistency predicate is *defined* from `Prov` (`Con S T := ¬ S.Prov T falsum`),
  not postulated. The old file had `opaque ZFCConsistent : Prop`, which made
  "ZFC does not prove Con(ZFC)" a hypothesis about an uninterpreted proposition.
* The relative-consistency criterion (Task D) is now *derived* from the laws rather than
  assumed: the old file took the two bridges `ZFCPlusRHConsistent → ¬ Prov (¬RH)` as
  hypotheses, which is essentially the conclusion.
* What is *not* done here: no arithmetization (no coding of syntax, no `Prov` predicate
  inside the object language), hence Gödel's second incompleteness theorem is not proved.
  Where it is needed it appears as a named hypothesis with an explicit docstring; see
  `not_provable_of_imp_con`.
-/
import Mathlib.Data.Set.Basic

namespace RHProvability

universe u

/-- A syntactic provability relation for a first-order theory over an abstract sentence type.

The fields are the four laws used below. They are deliberately the *weakest* set that makes
the independence criterion go through; in particular nothing here mentions arithmetic,
coding, or `ZFC`, so this structure is a logic-level interface, not a formalization of any
particular theory. -/
structure ProvSystem (Sent : Type u) where
  /-- Object-language implication. -/
  imp : Sent → Sent → Sent
  /-- Object-language negation. -/
  neg : Sent → Sent
  /-- Object-language falsum. -/
  falsum : Sent
  /-- `Prov T φ` means: `φ` has a proof all of whose non-logical assumptions lie in `T`. -/
  Prov : Set Sent → Sent → Prop
  /-- Hypothesis rule: every axiom of `T` is provable from `T`. -/
  hyp : ∀ {T : Set Sent} {φ : Sent}, φ ∈ T → Prov T φ
  /-- Weakening: provability is monotone in the axiom set. -/
  weaken : ∀ {T T' : Set Sent} {φ : Sent}, T ⊆ T' → Prov T φ → Prov T' φ
  /-- Modus ponens. -/
  mp : ∀ {T : Set Sent} {p q : Sent}, Prov T (imp p q) → Prov T p → Prov T q
  /-- Negation elimination (NOT ex falso): from `φ` and `¬φ`, infer falsum.

  The old field name was `efq`, which names the *other* rule ("from falsum infer anything"). The
  type below is what is used, and it is worth naming honestly — an independent reader flagged the
  mismatch. -/
  neg_elim : ∀ {T : Set Sent} {φ : Sent}, Prov T φ → Prov T (neg φ) → Prov T falsum

variable {Sent : Type u}

/-- Meta-level consistency of the axiom set `T`: no contradiction is provable from `T`.

This is a proposition *about* `Prov`, hence a statement in Lean's logic (the metatheory),
not a sentence of the object language. Confusing the two is the central trap in this
project; see `not_provable_of_imp_con` for the place where an object-language sentence
(`conSentence`) is needed instead. -/
def Con (S : ProvSystem Sent) (T : Set Sent) : Prop := ¬ S.Prov T S.falsum

/-- Consistency is inherited by weaker axiom sets. -/
theorem con_mono (S : ProvSystem Sent) {T T' : Set Sent} (hsub : T ⊆ T')
    (hcon : Con S T') : Con S T := by
  intro h
  exact hcon (S.weaken hsub h)

/-- If adding `¬φ` keeps `T` consistent, then `T` does not prove `φ`. -/
theorem not_provable_of_con_add_neg (S : ProvSystem Sent) {T : Set Sent} {φ : Sent}
    (hcon : Con S (T ∪ {S.neg φ})) : ¬ S.Prov T φ := by
  intro hφ
  apply hcon
  have h₁ : S.Prov (T ∪ {S.neg φ}) φ := S.weaken Set.subset_union_left hφ
  have h₂ : S.Prov (T ∪ {S.neg φ}) (S.neg φ) :=
    S.hyp (Set.mem_union_right T (by exact rfl))
  exact S.neg_elim h₁ h₂

/-- If adding `φ` keeps `T` consistent, then `T` does not prove `¬φ`. -/
theorem not_provable_neg_of_con_add (S : ProvSystem Sent) {T : Set Sent} {φ : Sent}
    (hcon : Con S (T ∪ {φ})) : ¬ S.Prov T (S.neg φ) := by
  intro hneg
  apply hcon
  have h₁ : S.Prov (T ∪ {φ}) (S.neg φ) := S.weaken Set.subset_union_left hneg
  have h₂ : S.Prov (T ∪ {φ}) φ := S.hyp (Set.mem_union_right T (by exact rfl))
  exact S.neg_elim h₂ h₁

/-- `φ` is independent of `T`: `T` proves neither `φ` nor its negation. -/
def Independent (S : ProvSystem Sent) (T : Set Sent) (φ : Sent) : Prop :=
  ¬ S.Prov T φ ∧ ¬ S.Prov T (S.neg φ)

/-- **Task D, derived rather than assumed.** If both `T + φ` and `T + ¬φ` are consistent,
then `φ` is independent of `T`.

The old scaffold took the two implications
`ZFCPlusRHConsistent → ¬ ProvableZFC (¬ RH)` and `ZFCPlusNotRHConsistent → ¬ ProvableZFC RH`
as hypotheses; here they are theorems, obtained from `hyp`, `weaken` and `efq` alone. -/
theorem independent_of_consistent_extensions (S : ProvSystem Sent) {T : Set Sent} {φ : Sent}
    (hpos : Con S (T ∪ {φ})) (hneg : Con S (T ∪ {S.neg φ})) : Independent S T φ :=
  ⟨not_provable_of_con_add_neg S hneg, not_provable_neg_of_con_add S hpos⟩

/-- The paper's route, with every hypothesis named.

`hImp`: the object-language sentence `RH → ConSentence` is provable from `T`.
`hGodel2`: `T` does not prove its own internal consistency sentence. This is the *only*
mathematical input that is not logic: it is Gödel's second incompleteness theorem applied
to `T`, and discharging it requires an arithmetization (coding, a provability predicate in
the object language, and the Hilbert–Bernays–Löb derivability conditions). None of that is
in this file, and none of it is in Mathlib; see the research note for the dependency that
does provide it (Saitou–Noguchi, arXiv:2609.13780).

Conclusion: no axiom in this file, and no `opaque` declaration, can manufacture `hImp`. The
route is therefore exactly as strong as the unproved implication "ZFC proves RH → Con(ZFC)". -/
theorem not_provable_of_imp_con (S : ProvSystem Sent) {T : Set Sent} {RH conSentence : Sent}
    (hImp : S.Prov T (S.imp RH conSentence))
    (hGodel2 : ¬ S.Prov T conSentence) : ¬ S.Prov T RH := by
  intro hRH
  exact hGodel2 (S.mp hImp hRH)

/-- Repackaging of `not_provable_of_imp_con` with the negations pushed inside. Note: this is
**not** the contrapositive, despite the earlier docstring; the proof still goes by contradiction. -/
theorem imp_con_of_not_provable (S : ProvSystem Sent) {T : Set Sent} {RH conSentence : Sent}
    (h : ¬ ¬ S.Prov T RH) (hImp : S.Prov T (S.imp RH conSentence)) :
    ¬ ¬ S.Prov T conSentence := by
  intro hcon
  exact h (not_provable_of_imp_con S hImp hcon)

end RHProvability
