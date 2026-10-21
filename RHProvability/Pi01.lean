/-
# `Π⁰₁` presentations, and the asymmetry between refuting and proving

`Checks.lean` gave the bare logical shape. This file makes the *notion* usable and then proves
the one metamathematical fact that the whole project turns on.

## The notion

`Pi01 P` is a **presentation** of `P` as a `Π⁰₁` statement: a *function* `check : ℕ → Bool` with
`P ↔ ∀ n, check n = true`. Using a `Bool`-valued function (rather than a `DecidablePred`) matters:
a function is data, so the counterexample search is a computable map, and `n ↦ check n = false`
carries its decidability for free.

`Pi01From N P` is the same with a threshold (`∀ n ≥ N`), which is the shape of Robin's criterion
(`n > 5040`) and of every "eventually" criterion.

## The asymmetry (the point of the file)

For `Π⁰₁` statements truth and provability interact in **one direction only**:

* `true_of_not_provable_neg` — if a theory `T` cannot refute `P`, and `T` is `Σ₁`-complete for the
  failing checks, then `P` is **true**. A refutation of a `Π⁰₁` statement must exhibit a numeral,
  and numerals are hard currency.
* `false_of_provable_neg` — the same transport in the dual direction needs *soundness* of the
  interpretation.

There is **no** analogous statement for `Π⁰₁`-ness giving `T ⊬ P`: provability of a `Π⁰₁` sentence is
perfectly possible (the prime number theorem is `Π⁰₁` and proved). So a `Π⁰₁` presentation of RH
buys: "if RH is independent of `T` in the `¬RH` direction, then RH". It does **not** buy
"`T ⊬ RH`".

## What is *not* here

No arithmetization: `Sent` is abstract, `code : ℕ → Sent` and the logical scheme `hwitness` are
hypotheses, not constructions. No instance of `Pi01 RiemannHypothesis` is produced (that is the
open formalization task: it needs effective bounds for the `log log n` comparison). Everything is
proved by the kernel with no axioms beyond Lean's standard three.
-/
import Mathlib.Computability.Partrec
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RHProvability.Provability

namespace RHProvability

universe u

/-! ## Presentations -/

/-- A `Π⁰₁` presentation of `P`: a computable (indeed `Bool`-valued) check function such that `P`
holds exactly when every check passes. -/
structure Pi01 (P : Prop) where
  /-- The decidable check. -/
  check : ℕ → Bool
  /-- **The check must be computable** (i.e. computed by a Turing machine, `Computable` from
  Mathlib's computability library). This field is not decoration: *without* it the structure is
  inhabited for **every** `P` classically — take `check n := if P then true else decide (n ≠ 0)` —
  so `Nonempty (Pi01 _)` would be provable outright and the register would record nothing.
  Verified failure mode, kept in `NOTES-iteration8-audit-fixes.md`. -/
  computable : Computable check
  /-- `P` is equivalent to the universal statement "every check passes". -/
  iff : P ↔ ∀ n, check n = true

/-- The same with a threshold: `P ↔ ∀ n ≥ N, check n`. This is the shape of Robin's criterion. -/
structure Pi01From (N : ℕ) (P : Prop) where
  /-- The decidable check. -/
  check : ℕ → Bool
  /-- The check must be computable; same reason as for `Pi01`. -/
  computable : Computable check
  /-- `P` is equivalent to "every check past `N` passes". -/
  iff : P ↔ ∀ n, N ≤ n → check n = true

namespace Pi01

variable {P : Prop}

/-- The universal statement as a `Bool` condition. -/
theorem iff_all_true (pres : Pi01 P) : P ↔ ∀ n, pres.check n = true := pres.iff

/-- Failure of a universal `Bool` check is the existence of a failing index. -/
theorem exists_false_iff_not_forall_true (check : ℕ → Bool) :
    (∃ n, check n = false) ↔ ¬ ∀ n, check n = true := by
  constructor
  · rintro ⟨n, hn⟩ h
    rw [h n] at hn
    exact Bool.noConfusion hn
  · intro h
    by_contra hc
    exact h fun n => by
      cases hv : check n with
      | true => rfl
      | false => exact absurd ⟨n, hv⟩ hc

/-- **The counterexample form.** A `Π⁰₁` statement fails exactly when some check fails. -/
theorem not_iff_exists_false (pres : Pi01 P) : ¬ P ↔ ∃ n, pres.check n = false := by
  have h := exists_false_iff_not_forall_true pres.check
  constructor
  · intro hP
    by_contra hc
    apply hP
    rw [pres.iff]
    by_contra hforall
    exact hc (h.mpr hforall)
  · rintro ⟨n, hn⟩ hP
    have hforall : ∀ m, pres.check m = true := pres.iff.mp hP
    rw [hforall n] at hn
    exact Bool.noConfusion hn

/-- **The witness can be taken minimal**: a failing check has a first failing index. Since the
check is a function, this is a genuine computation over a decidable predicate. -/
theorem exists_min_false (pres : Pi01 P) (h : ∃ n, pres.check n = false) :
    ∃ n, pres.check n = false ∧ ∀ m, m < n → pres.check m = true := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro m hm
  have hmin : ¬ (pres.check m = false) := Nat.find_min h hm
  cases hv : pres.check m with
  | true => rfl
  | false => exact absurd hv hmin

/-- A `Π⁰₁` presentation of a true statement is a machine-checkable certificate. -/
theorem all_true_of (pres : Pi01 P) (h : P) : ∀ n, pres.check n = true := pres.iff.mp h

end Pi01

namespace Pi01From

variable {N : ℕ} {P : Prop}

/-- Shift a thresholded presentation to a threshold-free one: `n ↦ n + N`. -/
def toPi01 (pres : Pi01From N P) : Pi01 P where
  check := fun k => pres.check (k + N)
  computable := pres.computable.comp <|
    Primrec.to_comp (Primrec.nat_add.comp Primrec.id (Primrec.const N))
  iff := pres.iff.trans (by
    constructor
    · intro h k
      exact h (k + N) (Nat.le_add_left N k)
    · intro h n hn
      have hsub : n - N + N = n := Nat.sub_add_cancel hn
      rw [← hsub]
      exact h (n - N))

/-- The counterexample form for a thresholded presentation. -/
theorem not_iff_exists_false (pres : Pi01From N P) :
    ¬ P ↔ ∃ n, N ≤ n ∧ pres.check n = false := by
  rw [pres.toPi01.not_iff_exists_false]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + N, Nat.le_add_left N k, hk⟩
  · rintro ⟨n, hn, hfn⟩
    refine ⟨n - N, ?_⟩
    show pres.check (n - N + N) = false
    rw [Nat.sub_add_cancel hn]
    exact hfn

end Pi01From

/-! ## The asymmetry -/

/-- **Truth from un-refutability.** Let `P` have a `Π⁰₁` presentation by `check`, let `rh` and
`negAll` be object-language sentences for `P` and for "not every check passes", and suppose

* `hSigma1`: `T` proves the numeral fact `code n` whenever `check n = false` — the `Σ₁`-completeness
  of `T` restricted to true `Σ₁` facts (this is the only genuinely arithmetical input);
* `hwitness`: `T` proves, for each `n`, that `code n` implies `negAll` — the object-language
  version of "a witness refutes a universal";
* `hbridge`: `T` proves `negAll → ¬ rh` — the contrapositive of `T ⊢ P → ∀ n, check n`.

Then if `T` does *not* prove `¬ rh`, the statement `P` is **true**. -/
theorem true_of_not_provable_neg {Sent : Type u} (S : ProvSystem Sent) {T : Set Sent}
    {P : Prop} (pres : Pi01 P) (rh : Sent) (code : ℕ → Sent) (negAll : Sent)
    (hSigma1 : ∀ n, pres.check n = false → S.Prov T (code n))
    (hwitness : ∀ n, S.Prov T (S.imp (code n) negAll))
    (hbridge : S.Prov T (S.imp negAll (S.neg rh)))
    (hnot : ¬ S.Prov T (S.neg rh)) : P := by
  by_contra hP
  obtain ⟨n, hn⟩ := (pres.not_iff_exists_false).mp hP
  exact hnot (S.mp hbridge (S.mp (hwitness n) (hSigma1 n hn)))

/-- **The dual direction, and why it is weaker.** Refutation transports to falsity only through a
*sound interpretation* `I` of the object language, which must additionally respect negation.
Whereas `true_of_not_provable_neg` needed no interpretation at all: a numeral witness is already
in the metatheory. -/
theorem false_of_provable_neg {Sent : Type u} (S : ProvSystem Sent) {T : Set Sent}
    {P : Prop} (I : Sent → Prop) (rh : Sent)
    (hRh : I rh ↔ P)
    (hNeg : I (S.neg rh) ↔ ¬ I rh)
    (hsound : ∀ φ, S.Prov T φ → I φ)
    (h : S.Prov T (S.neg rh)) : ¬ P := by
  have hI : I (S.neg rh) := hsound _ h
  rw [hNeg] at hI
  intro hP
  exact hI (hRh.mpr hP)

/-- **The RH face of the asymmetry.** If RH has a `Π⁰₁` presentation, `T` is `Σ₁`-complete for the
failing checks and proves that a failing check refutes RH, then `T ⊬ ¬RH` implies **RH**. -/
theorem riemannHypothesis_of_not_provable_neg {Sent : Type u} (S : ProvSystem Sent) {T : Set Sent}
    (pres : Pi01 RiemannHypothesis) (rh : Sent) (code : ℕ → Sent) (negAll : Sent)
    (hSigma1 : ∀ n, pres.check n = false → S.Prov T (code n))
    (hwitness : ∀ n, S.Prov T (S.imp (code n) negAll))
    (hbridge : S.Prov T (S.imp negAll (S.neg rh)))
    (hnot : ¬ S.Prov T (S.neg rh)) : RiemannHypothesis :=
  true_of_not_provable_neg S pres rh code negAll hSigma1 hwitness hbridge hnot

/-! ## Non-vacuity: concrete presentations that really carry computability data -/

/-- A true `Π⁰₁` statement with a constant check. -/
def pi01True : Pi01 True where
  check := fun _ => true
  computable := Computable.const true
  iff := by simp

/-- A false one: the check is constantly `false`, so the universal statement fails. -/
def pi01False : Pi01 False where
  check := fun _ => false
  computable := Computable.const false
  iff := ⟨False.elim, fun h => by simpa using h 0⟩

/-- A **non-constant** computable check: the parity bit. The statement it presents is false, and the
counterexample machinery extracts the witness `n = 2`. -/
def pi01Odd : Pi01 (∀ n : ℕ, Nat.bodd n = true) where
  check := Nat.bodd
  computable := Computable.nat_bodd
  iff := Iff.rfl

/-- The parity presentation fails at `n = 2`, and `not_iff_exists_false` turns that into a witness. -/
theorem pi01Odd_counterexample : ∃ n, pi01Odd.check n = false :=
  ⟨2, by decide⟩

/-- A thresholded presentation: "every `n ≥ 3` passes a constant check". Reduces to `Pi01` by
shifting, and the shift has to transport the computability witness. -/
def pi01FromTrue : Pi01From 3 True where
  check := fun _ => true
  computable := Computable.const true
  iff := ⟨fun _ _ _ => rfl, fun _ => trivial⟩

/-- Its shifted `Pi01` form runs (and is computable by construction). -/
theorem pi01FromTrue_all : ∀ k, pi01FromTrue.toPi01.check k = true := fun k => by
  simp [Pi01From.toPi01, pi01FromTrue]

end RHProvability
