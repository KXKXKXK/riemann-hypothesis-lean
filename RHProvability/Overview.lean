/-
# Overview — the whole project, as a compilable census

This module is the **summary of the development, written in Lean rather than in prose**. It has four
parts, and the point of the file is that every claim in it is either proved by the kernel or is
explicitly flagged as unproved data:

* **Part I** restates the headline results as aliases, so that `lake build` fails if any of them
  disappears or changes type.
* **Part II** registers the *assumptions* as `Prop`-valued definitions. Nothing in this file turns
  them into theorems; the conditional theorems that consume them are restated next to them.
* **Part III** registers the *gaps* as `Prop`-valued definitions (`Open…`). They are statements,
  not proofs — there is no definition of them anywhere in this development.
* **Part IV** records the one *negative* result and, importantly, its exact scope.

## What RH itself

`RiemannHypothesis` is **not** proved, **not** refuted, and this development contains no evidence
for or against it. What is established is: (a) several unconditional *equivalent* reformulations of
it, (b) the logical skeleton that makes a "RH is unprovable" claim interesting, and (c) that one
attractive shortcut to a decidable presentation is invalid.

## Axiom status

Every declaration in Part I and Part II below depends at most on Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`); several depend on none. There is no `sorry`, no
`admit`, and no user-declared `axiom` anywhere in the library. This was checked declaration by
declaration with `#print axioms`; the per-module breakdown is in the VibeMath `README.md`.
-/
import RHProvability.Provability
import RHProvability.RHFormulas
import RHProvability.BernoulliZeta
import RHProvability.Reflection
import RHProvability.FiniteHeight
import RHProvability.Counting
import RHProvability.StripCount
import RHProvability.Checks
import RHProvability.Robin
import RHProvability.Pi01
import RHProvability.Bounds
import RHProvability.LineCount
import RHProvability.LineCountClosed
import RHProvability.Lagarias
import RHProvability.Numeric
import RHProvability.Backlund
import RHProvability.TightBounds
import RHProvability.LagariasCheck
import RHProvability.Finiteness
import RHProvability.TailShape
import RHProvability.OffLine
import RHProvability.Audit

namespace RHProvability
namespace Overview

open Filter
open scoped Topology

/-! ## Part I — Proved

Each item is an alias of a theorem proved in a module of this library. The docstring records what
the item buys and what it does *not* buy. -/

/-- **(I.1)** Mathlib's `RiemannHypothesis` is equivalent to the textbook critical-strip statement.
This is the unconditional bridge; the `TrivialZerosOnLeft` side is discharged by (I.2). -/
theorem item1 : RiemannHypothesis ↔ RiemannHypothesisStrip :=
  riemannHypothesis_iff_strip_unconditional

/-- **(I.2)** Every even-index Bernoulli number with positive index is nonzero. Mathlib did not have
this; it is derived here from `ζ(2k) ≠ 0` and the closed form, i.e. not circularly. -/
theorem item2 {k : ℕ} (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 :=
  bernoulli_two_mul_ne_zero hk

/-- **(I.3)** RH is equivalent to `NoZerosRightOfCriticalLine`: there is **no zero of `ζ` inside the
strip** whose real part exceeds `1/2`.

(An earlier version of this docstring called this "the reflection-symmetric form"; that was the wrong
description — the reflection symmetry enters through (I.18), not here.) -/
theorem item3 : RiemannHypothesis ↔ NoZerosRightOfCriticalLine :=
  riemannHypothesis_iff_no_right

/-- **(I.4)** The `Π⁰₁`-shaped logical skeleton: for a decidable `Q`, `¬∀ n, Q n ↔ ∃ n, ¬Q n`. -/
theorem item4 (Q : ℕ → Prop) [DecidablePred Q] :
    ¬ AllChecksPass Q ↔ ∃ n : ℕ, ¬ Q n :=
  not_allChecksPass_iff_counterexample Q

/-- **(I.5)** A failing `Bool` check has a **least** failing index. This is the only statement in the
library that consumes decidability essentially (`Nat.find`); it has no axioms. -/
theorem item5 {P : Prop} (pres : Pi01 P) (h : ∃ n, pres.check n = false) :
    ∃ n, pres.check n = false ∧ ∀ m, m < n → pres.check m = true :=
  Pi01.exists_min_false pres h

/-- **(I.6) The asymmetry.** For a `Π⁰₁`-presented `P`, if `T` is `Σ₁`-complete for the failing
checks and knows that a witness refutes the universal, then `T ⊬ ¬P` forces `P` to be **true**.

The three hypotheses are the arithmetization (`code`), the logical scheme (`hwitness`) and the
`Σ₁`-completeness (`hSigma1`); none of them is proved anywhere in the library. -/
theorem item6 {Sent : Type} (S : ProvSystem Sent) {T : Set Sent} {P : Prop} (pres : Pi01 P)
    (rh : Sent) (code : ℕ → Sent) (negAll : Sent)
    (hSigma1 : ∀ n, pres.check n = false → S.Prov T (code n))
    (hwitness : ∀ n, S.Prov T (S.imp (code n) negAll))
    (hbridge : S.Prov T (S.imp negAll (S.neg rh)))
    (hnot : ¬ S.Prov T (S.neg rh)) : P :=
  true_of_not_provable_neg S pres rh code negAll hSigma1 hwitness hbridge hnot

/-- **(I.7)** The RH face of the asymmetry: `T ⊬ ¬RH` implies RH — *conditional on* a `Π⁰₁`
presentation of RH existing, which is open (see `OpenPi01Presentation`). -/
theorem item7 {Sent : Type} (S : ProvSystem Sent) {T : Set Sent}
    (pres : Pi01 RiemannHypothesis) (rh : Sent) (code : ℕ → Sent) (negAll : Sent)
    (hSigma1 : ∀ n, pres.check n = false → S.Prov T (code n))
    (hwitness : ∀ n, S.Prov T (S.imp (code n) negAll))
    (hbridge : S.Prov T (S.imp negAll (S.neg rh)))
    (hnot : ¬ S.Prov T (S.neg rh)) : RiemannHypothesis :=
  riemannHypothesis_of_not_provable_neg S pres rh code negAll hSigma1 hwitness hbridge hnot

/-- **(I.8)** Robin's inequality at `n` is equivalent to the existence of a **rational certificate**
`a < log log n`. This is the exact reduction from a real comparison to rational bounds. -/
theorem item8 {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n) :
    RobinTest c n ↔
      ∃ a : ℚ, (a : ℝ) < Real.log (Real.log (n : ℝ)) ∧
        (sigmaNat n : ℝ) < c * (n : ℝ) * (a : ℝ) :=
  robinTest_iff_exists_rat_certificate hc hn

/-- **(I.9)** The computable divisor sum is Mathlib's `ArithmeticFunction.sigma 1` — the definition
used by the existing Lean formalization of Robin's criterion. -/
theorem item9 (n : ℕ) : sigmaNat n = ArithmeticFunction.sigma 1 n :=
  sigmaNat_eq_sigma_one n

/-- **(I.10)** Unconditional bracket for the constant in Robin's criterion: `3/2 < e^γ < 2`. -/
theorem item10 : (3 / 2 : ℝ) < Real.exp Real.eulerMascheroniConstant ∧
    Real.exp Real.eulerMascheroniConstant < 2 :=
  exp_eulerMascheroniConstant_bracket

/-- **(I.11)** A strictly-descending upper approximation converts the **non-strict** comparison
`f ≤ c·g` into a `∀ k` form with a decidable matrix. -/
theorem item11 {c : ℝ} {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 c)) (hupper : ∀ k, c < u k)
    {f g : ℝ} (hg : 0 < g) : f ≤ c * g ↔ ∀ k, f < u k * g :=
  le_iff_forall_lt_upper hu hupper hg

/-- **(I.12)** The counting invariant: `N_line(T) ≤ N_strip(T)`. -/
theorem item12 (T : ℝ) : lineCount T ≤ stripCount T :=
  lineCount_le_stripCount T

/-- **(I.13)** Equality of the two counts at every height implies RH. This is the counting skeleton
of the Backlund–Turing route; the *computation* of either count is not in the library. -/
theorem item13 (h : ∀ T : ℝ, lineCount T = stripCount T) : RiemannHypothesis :=
  riemannHypothesis_of_counts_eq h

/-- **(I.14)** The line count is literally the number of real ordinates `t` with `|t| ≤ T` and
`ζ(1/2 + it) = 0` — the object a sign-change computation would produce. -/
theorem item14 (T : ℝ) : lineCount T = (lineZerosUpTo T).ncard :=
  lineCount_eq_ncard_lineZerosUpTo T

/-- **(I.15)** The logical core of independence, derived rather than assumed: if both one-point
extensions are consistent, the sentence is independent. -/
theorem item15 {Sent : Type} (S : ProvSystem Sent) {T : Set Sent} {φ : Sent}
    (hpos : Con S (T ∪ {φ})) (hneg : Con S (T ∪ {S.neg φ})) :
    Independent S T φ :=
  independent_of_consistent_extensions S hpos hneg

/-- **(I.16)** The conditional independence route: if `T` proves `RH → Con(T)` and does not prove its
own consistency sentence, then `T ⊬ RH`. The second hypothesis is Gödel's second theorem, which is
**not** formalized here. -/
theorem item16 {Sent : Type} (S : ProvSystem Sent) {T : Set Sent} {rh conSentence : Sent}
    (hImp : S.Prov T (S.imp rh conSentence)) (hGodel2 : ¬ S.Prov T conSentence) :
    ¬ S.Prov T rh :=
  not_provable_of_imp_con S hImp hGodel2

/-- **(I.18)** Conjugation symmetry of `ζ`: `ζ(conj s) = conj (ζ s)`, **cited from Mathlib**
(`riemannZeta_conj`, `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:458`).

An earlier version of this file listed this as a *missing, blocking* lemma. That was wrong, and the
correction is preserved as the compiled theorem `Audit.conj_symmetry_in_mathlib`. -/
theorem item18 (s : ℂ) : riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conj s

/-- **(I.19)** The zero-counting invariant is an **equivalence**: the line count equals the strip
count at every height **iff** RH holds. The `Re z = 0` boundary case that an earlier version listed
as a gap is closed by `riemannZeta_ne_zero_of_re_eq_zero`. -/
theorem item19 : (∀ T : ℝ, lineCount T = stripCount T) ↔ RiemannHypothesis :=
  countsEq_iff_riemannHypothesis

/-- **(I.20)** At `n = 1`, Lagarias's inequality is an **equality**: `σ(1) = H_1 = 1` and
`log 1 = 0`. This pins down the statement's normalisation. -/
theorem item20 : lagariasTest 1 :=
  lagariasTest_one

/-- **(I.21)** **The strict form of Lagarias's criterion is false at `n = 1`** (both sides are `1`).
Machine-checked reason why the criterion is stated non-strictly — and why the non-strict shaping lemma
applies here while Robin's strict inequality blocks it (item 17). -/
theorem item21 : ¬ ((sigmaNat 1 : ℝ) < lagariasRHS 1) :=
  lagarias_strict_fails_at_one

/-- **(I.22)** The `Π⁰₁` form of Lagarias's criterion: given descending upper approximations `u n ·`
of the right-hand side, the criterion is a `∀ n ∀ k` comparison of `σ(n)` against `u n k`. -/
theorem item22 (u : ℕ → ℕ → ℝ)
    (hu : ∀ n : ℕ, Tendsto (fun k => u n k) atTop (𝓝 (lagariasRHS n)))
    (hupper : ∀ n k, lagariasRHS n < u n k) :
    lagariasCriterion ↔ ∀ n : ℕ, 0 < n → ∀ k : ℕ, (sigmaNat n : ℝ) < u n k :=
  lagariasCriterion_iff_forall_upper u hu hupper

/-- **(I.23)** The lower companion of Mathlib's `log x ≤ x - 1`: for every `x > 0`,
`1 - 1/x ≤ log x`. -/
theorem item23 {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x :=
  one_sub_inv_le_log hx

/-- **(I.24)** `exp x ≤ 1/(1-x)` for **every** `x < 1` (no nonnegativity needed), proved without any
power series: apply the log lower bound at `y = 1/(1-x)` and exponentiate. -/
theorem item24 {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ :=
  exp_le_one_div_one_sub hx

/-- **(I.25)** The general rational upper bound for `exp`: for `x < N`, `exp x ≤ (1 - x/N)⁻¹ ^ N`.
At rational `x` and integer `N` the right-hand side is rational. -/
theorem item25 {x : ℝ} {N : ℕ} (hN : 0 < N) (hx : x < N) :
    Real.exp x ≤ ((1 - x / N)⁻¹) ^ N :=
  exp_le_pow_bound hN hx

/-- **(I.26)** At a positive rational `q` **both** bounds on `log q` are rational:
`1 - 1/q ≤ log q ≤ q - 1`. This is the rational certificate for `log` at rational points. -/
theorem item26 {q : ℚ} (hq : 0 < q) :
    ((1 - 1 / q : ℚ) : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ ((q - 1 : ℚ) : ℝ) :=
  log_bounds_rat hq

/-- **(I.27)** Composition: rational bounds on `exp (H_n)` and `log (H_n)` produce rational-shaped
bounds on `H_n + exp(H_n)·log(H_n)` — i.e. on the right-hand side of Lagarias's inequality. -/
theorem item27 {n : ℕ} {a b c d : ℝ}
    (hlog1 : a ≤ Real.log (harmonic n : ℝ)) (hlog2 : Real.log (harmonic n : ℝ) ≤ b)
    (hexp1 : c ≤ Real.exp (harmonic n : ℝ)) (hexp2 : Real.exp (harmonic n : ℝ) ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (harmonic n : ℝ) + c * a ≤ lagariasRHS n ∧
      lagariasRHS n ≤ (harmonic n : ℝ) + d * b :=
  lagariasRHS_bounds hlog1 hlog2 hexp1 hexp2 ha hc

/-- **(I.28)** A first explicit, machine-checked rational bracket for the Lagarias right-hand side:
`7/3 ≤ lagariasRHS 2 ≤ 19/2`. These bounds are **correct but loose** — they do not decide the
criterion at `n = 2`, which needs far tighter ones (see `TaskCertifiedExpLogBounds`). -/
theorem item28 : (7 / 3 : ℝ) ≤ lagariasRHS 2 ∧ lagariasRHS 2 ≤ (19 / 2 : ℝ) :=
  lagariasRHS_two_bounds

/-- **(I.29)** The first comparison theorem of the counting route: the strip count is bounded by the
disk count at radius `1 + |T|`. This is how "an upper bound for `N_strip`" becomes "an upper bound for
`zeroCount`", which can be attached to Mathlib's Nevanlinna/divisor machinery (see
`NOTES-iteration11-backlund-scope.md`). -/
theorem item29 (T : ℝ) : stripCount T ≤ zeroCount (1 + |T|) :=
  stripCount_le_zeroCount T

/-- **(I.30)** The same comparison with an arbitrary radius. -/
theorem item30 {T R : ℝ} (hR : 1 + |T| ≤ R) : stripCount T ≤ zeroCount R :=
  stripCount_le_zeroCount_of hR

/-- **(I.31)** For negative height the strip box is empty, so `stripCount T = 0` — the only place in
the development where the count is actually evaluated. -/
theorem item31 {T : ℝ} (hT : T < 0) : stripCount T = 0 :=
  stripCount_of_neg hT

/-- **(I.32)** If the registered `BacklundBound` held, it would bound the **line** count as well
(via `N_line ≤ N_strip`). This records the transfer without assuming the bound. -/
theorem item32 (h : BacklundBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (lineCount T : ℝ) ≤ C * T * Real.log T :=
  lineCount_le_of_backlund h

/-- **(I.33)** The tight log lower bound (Padé `[1/1]`), valid for `y ≥ 1`:
`2(y-1)/(y+1) ≤ log y`. Contributed by a teammate; note the domain restriction is *necessary* —
see (I.34). -/
theorem item33 {y : ℝ} (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ Real.log y :=
  log_lower_artanh hy

/-- **(I.34)** The domain restriction in (I.33) is not an artefact: the naive statement
`∀ y > 0, 2(y-1)/(y+1) ≤ log y` is **false** (machine-checked refutation, counterexample at
`y = 1/3`), and on `0 < y ≤ 1` the inequality reverses. -/
theorem item34 : ¬ (∀ y : ℝ, 0 < y → 2 * (y - 1) / (y + 1) ≤ Real.log y) :=
  log_lower_artanh_not_for_pos

/-- **(I.35)** The Taylor + geometric-tail upper bound for `exp`, in full: for `0 ≤ x < N+1`,
`exp x ≤ ∑_{i<N} x^i/i! + (x^N/N!)·(1 - x/(N+1))⁻¹`. This is much sharper than (I.25): at `x = 3/2`
with `N = 7` it gives `≈ 4.48171`, where (I.25) gives `16`. -/
theorem item35 {x : ℝ} {N : ℕ} (hx : 0 ≤ x) (hN : x < (N : ℝ) + 1) :
    Real.exp x ≤ (∑ i ∈ Finset.range N, x ^ i / (Nat.factorial i : ℝ)) +
      (x ^ N / (Nat.factorial N : ℝ)) * (1 - x / ((N : ℝ) + 1))⁻¹ :=
  exp_upper_taylor hx hN

/-- **(I.36)** The right-hand side of Lagarias's inequality at `n = 2`, bracketed to width `0.007`:
`3.314 ≤ H_2 + exp(H_2)·log(H_2) ≤ 3.321` (true value `≈ 3.3172`). -/
theorem item36 : (3314 / 1000 : ℝ) ≤ lagariasRHS 2 ∧ lagariasRHS 2 ≤ 3321 / 1000 :=
  lagariasRHS_two_tight

/-- **(I.37)** **First certified instance of a criterion check.** The tight bracket separates the
right-hand side from `σ(2) = 3`, so the criterion is *decided* at `n = 2`: `lagariasTest 2` holds.
Not a decision procedure for all `n`; one instance, fully machine-checked. -/
theorem item37 : lagariasTest 2 :=
  lagariasTest_two

/-- **(I.38)** The *loose* bounds do not suffice at `n = 2` (`7/3 < σ(2) = 3`), which is why the
tightening (I.33, I.35) was needed. -/
theorem item38 : (7 / 3 : ℝ) < (sigmaNat 2 : ℝ) :=
  loose_bounds_insufficient_two

/-! ## Part II — Assumed

These are the inputs the library consumes but does not prove. Registering them as definitions keeps
them visible: any theorem whose statement mentions one of these is conditional, by construction. -/

/-- **Assumption register: Gödel's second incompleteness theorem**, in the form "`T` does not prove
its own consistency sentence". Needs an arithmetization; not in this library, not in Mathlib. -/
def AssumedGodel2 {Sent : Type} (S : ProvSystem Sent) (T : Set Sent) (conSentence : Sent) : Prop :=
  ¬ S.Prov T conSentence

/-- **Assumption register: the implication `RH → Con(T)`.** Not proved by anyone; the entire
"RH is unprovable" route is exactly as strong as this. -/
def AssumedRHImpliesCon {Sent : Type} (S : ProvSystem Sent) (T : Set Sent) (rh conSentence : Sent) :
    Prop :=
  S.Prov T (S.imp rh conSentence)

/-- **Assumption register: `Σ₁`-completeness**, restricted to the failing checks, stated for an
abstract coding `code : ℕ → Sent`. This is where arithmetization would have to enter. -/
def AssumedSigma1Completeness {Sent : Type} (S : ProvSystem Sent) (T : Set Sent)
    (check : ℕ → Bool) (code : ℕ → Sent) : Prop :=
  ∀ n : ℕ, check n = false → S.Prov T (code n)

/-- **Assumption register: the object-language "a witness refutes the universal".** -/
def AssumedWitnessRefutes {Sent : Type} (S : ProvSystem Sent) (T : Set Sent)
    (code : ℕ → Sent) (negAll : Sent) : Prop :=
  ∀ n : ℕ, S.Prov T (S.imp (code n) negAll)

/-! ## Part III — Not proved (the gaps, as statements)

Each definition here is a **proposition with no proof anywhere in this development**, and each carries
a note on how it was checked. Naming them makes the gaps auditable: `#check …` shows the exact
statement, and `Lake` will never silently "satisfy" one of them.

**Two entries were removed and one rewritten** after the external audit of 2026-10-18 (see Part V):
`OpenConjSymmetry` is now (I.18) — it was never a gap; `OpenCountsEqOfRH` is now (I.19) — it was a
small lemma; and the `log log n` entry was not an open problem but a **false** proposition, replaced
by `TaskCertifiedLogLogBounds`. -/

/-- **Gap 1.** The existence of a real-valued continuous function whose zeros are exactly the zeros of
`ζ` on the critical line. This is what makes sign-change counting meaningful. -/
def OpenRealValuedLineFunction : Prop :=
  ∃ Z : ℝ → ℝ, Continuous Z ∧
    ∀ t : ℝ, (Z t = 0 ↔ riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0)

-- **Gap 1 status (2026-10-19).** This registration is **proved**, not open. Two witnesses:
-- `LineFunction.lean` (`openRealValuedLineFunction`, toolchain-independent: distance to the closed
-- zero set, hence non-negative, hence never sign-changing) and `HardyLineFunction.lean`
-- (`openRealValuedLineFunction_via_hardyZ`), which wires it to **upstream** Mathlib's `hardyZ`
-- (shipped from v4.35.0; this project is pinned there as of 2026-10-19) — that is the object the
-- docstring above has in mind. A "sign change at every zero" successor would imply zero simplicity,
-- which is open, so it is **withdrawn** (`LineFunctionRegistry.lean`, kept as a record only).
-- The registration text itself is unchanged: this project only appends.
--

-- **Gap 2 (Backlund)** now lives in `Backlund.lean` as `BacklundBound`, together with the first
-- comparison theorem of the counting route (`stripCount_le_zeroCount`). It is still unproved.

/-- **Gap 4.** A `Π⁰₁` presentation of RH itself, i.e. an explicit `Bool`-valued check.

**Scope note (corrected after audit).** The library refutes one *scheme* for producing such a check
from Robin's criterion (`Overview.item17`), namely "take a strictly descending upper approximation of
`e^γ` and pass to the `∀ k` form". It does **not** refute the possibility that Robin's criterion has
a `Π⁰₁` presentation by some other route, and it does not refute it for RH either.

**This is a formalization target, not an open mathematical question.** It is classically known
(Turing 1953, by explicit zero-counting with certified error bounds) that RH *is* a `Π⁰₁` statement,
so a computable `check` exists; what does not exist is a formalization of it. After the audit fix
(adding `Computable`), this entry is no longer vacuously provable — the classical trivial
construction does not typecheck — but its truth is not in doubt, only its formalization. -/
def OpenPi01Presentation : Prop := Nonempty (Pi01 RiemannHypothesis)

/-- **Gap 5.** A `Π⁰₁` presentation of Robin's criterion — the narrower open question that the audit
message correctly distinguished from Gap 4. -/
def OpenPi01PresentationOfRobin : Prop := Nonempty (Pi01 robinCriterionEulerGamma)

/-- **Task (rewritten after the audit).** *Certified* rational bounds for `log log n`: a pair of
**computable** functions producing rationals that bracket `log log n` with a controlled gap.

The previous version of this entry was **false** — it asserted that no rational sits strictly between
`q n` and `log log n`, which contradicts density of `ℚ`; the refutation is compiled as
`Audit.oldEffectiveLogLogBounds_false`. Note also that *existence* of bounds is trivial (density); the
mathematical content of the task is the word `Computable` together with the certified gap. This is a
formalization task, not an open problem in the mathematical sense. -/
def TaskCertifiedLogLogBounds : Prop :=
  ∃ loNum loDen hiNum hiDen : ℕ → ℕ,
    Computable loNum ∧ Computable loDen ∧ Computable hiNum ∧ Computable hiDen ∧
      ∀ n : ℕ, 5041 ≤ n → 0 < loDen n ∧ 0 < hiDen n ∧
        (loNum n : ℝ) / (loDen n : ℝ) < Real.log (Real.log (n : ℝ)) ∧
          Real.log (Real.log (n : ℝ)) < (hiNum n : ℝ) / (hiDen n : ℝ) ∧
            (hiNum n : ℝ) / (hiDen n : ℝ) - (loNum n : ℝ) / (loDen n : ℝ) ≤ 1 / (n : ℝ)

/-- **Task (Lagarias route).** Certified rational bounds for `exp (H_n) · log (H_n)`, needed to turn
the `∀ k` matrix of (I.22) into a genuine `Bool` computation.

Same status as `TaskCertifiedLogLogBounds`: *existence* of rational bounds is trivial (density); the
content is `Computable` plus the proof, i.e. it is a formalization task, not an open problem. The
structural advantage of the Lagarias route is that no strictness has to be recovered (I.21), so this
is the only remaining obstruction on the arithmetic side. -/
def TaskCertifiedExpLogBounds : Prop :=
  ∃ num den : ℕ → ℕ, Computable num ∧ Computable den ∧
    ∀ n : ℕ, 0 < n → 0 < den n ∧
      lagariasRHS n < (num n : ℝ) / (den n : ℝ) ∧
        (num n : ℝ) / (den n : ℝ) - lagariasRHS n ≤ 1 / (2 ^ n : ℝ)

/-! ## Part IV — The negative result and its exact scope -/

/-- **(I.17)** The refuted scheme: "a strictly descending upper approximation of a constant, together
with `∀ k, f < u k · g`, yields the strict inequality `f < c · g`". False, with the numerical
counterexample `c = 0`, `u k = 1/(k+1)`, `f = 0`, `g = 1` baked into the proof.

Scope, stated precisely: this refutes that **one** way of recovering strictness. It does not refute
Robin's criterion having a `Π⁰₁` presentation (see `OpenPi01PresentationOfRobin`). -/
theorem item17 :
    ¬ ∀ (c : ℝ) (u : ℕ → ℝ) (f g : ℝ), Tendsto u atTop (𝓝 c) → (∀ k, c < u k) → 0 < g →
        (∀ k, f < u k * g) → f < c * g :=
  strict_version_refuted

/-! ## Part V — Corrections after the external audit (2026-10-18)

An external reader audited the delivered bundle and reported five issues. Their dispositions, with
the evidence kept as compiled theorems in `RHProvability/Audit.lean`:

| # | finding | disposition |
|---|---|---|
| 1 | `Pi01` had **no computability constraint**, so `Nonempty (Pi01 P)` was provable for every `P` (take `check n := if P then true else decide (n ≠ 0)`), which made "Gap 4/5" vacuous | **accepted, fixed**: `Pi01`/`Pi01From` now require `Computable check`; the old defect is preserved as `Audit.pi01Old_trivially_inhabited` |
| 2 | the `log log n` register entry was **false**, not open (it contradicted density of `ℚ`) | **accepted**: refutation compiled as `Audit.oldEffectiveLogLogBounds_false`; entry rewritten as `TaskCertifiedLogLogBounds` |
| 3 | the claim "Mathlib lacks `ζ(conj s) = conj(ζ s)`" was **wrong**; the lemma is in Mathlib | **accepted, my error** (my grep had been restricted to `Mathlib/NumberTheory/LSeries/`, violating this project's own scan rule); the lemma is now `item18` and `Audit.conj_symmetry_in_mathlib` |
| 4 | the `Re z = 0` boundary was a **small lemma**, not a genuine gap | **accepted**: proved as `riemannZeta_ne_zero_of_re_eq_zero`, so the counting invariant is the equivalence `item19` |
| 5 | documentation inconsistent (`FINAL-ASSESSMENT.md` not marked superseded; `item3` mis-described; VibeMath copy drifted) | **accepted, fixed in this revision** |

What the audit did **not** change: no theorem was weakened, no axiom was added, and the honest
boundary in the header — RH neither proved nor refuted, no evidence either way — stands. -/

/-! ## Part VI — What this route to RH is still missing

Written after an independent review (by 调研员) insisted that the chain from "the criterion is
computable" to "RH is proved" be written down with its holes labelled. It is short because the hole
is structural, not technical.

| # | item | status | whose |
|---|---|---|---|
| 1 | `RiemannHypothesis ↔ lagariasCriterion` | **not formalized here.** Measured (`NOTES-iteration11-port-probe.md`): the *statement* ports to our revision as-is (`Challenge.lean`, exit 0); the Mathlib-only part of `kimihiro64/Robin1984` (113 modules / 18,265 lines) compiles clean in the 59 modules actually tested, **zero** API-drift errors; the **proof core** (38 modules / 16,473 lines) is blocked at import time by the missing package `PrimeNumberTheoremAnd`, which is not on this machine and is pinned to a different Mathlib. The obstacle is a **missing package, not API drift** | Lagarias (2001/2002); port cost 20-40 person-days *if* `PrimeNumberTheoremAnd` vendors, or 3-6 person-months to reprove the five analytic inputs locally. **Not being paid now:** porting it would move this row from borrowed to ours, and would not cross the wall in row 2 |
| 2 | A **finiteness-theorem cut-off**: "if the criterion holds for all `n ≤ N` then it holds for all `n`", with an explicit computable `N` | **the shape cannot be a strict weakening** — see Part VII. `exists_isCutoff` proves the bare `∃ N` form is a tautology, and `isCutoff_iff_forall` proves that once the finitely many checks below `N` are in hand, the cut-off assertion is *equivalent* to the criterion | this development (Part VII) |
| 3 | Computable `exp`/`log` bounds tight enough to decide the criterion at each `n` | **in progress**: exact at `n = 2` (I.37), no general `n` yet | this development |

**Decidability is not proof.** Item 3, even completed for every `n`, yields "each `lagariasTest n` can
be evaluated", i.e. `∀ n` is verified instance by instance forever — not a proof of `∀ n`. Crossing to
a proof needs item 1 *and* item 2; item 2 is the real wall.

**Status wording (revised 2026-10-18).** This development does not approach a proof of RH. It is not,
however, standing still: Part VII *excludes* one route by theorem, and locates where the content of any
successor route would have to lie (an equality of counts, not a bound on them). The honest one-line
statement is: **one route eliminated by machine-checked theorem, one route's worth of content
identified, zero progress on RH itself.** -/

/-! ## Part VII — Route B, discharged by a theorem rather than by an opinion

A later instruction (relayed from the user) chose a different target: **find an explicit natural
number `N` such that, if the criterion holds for every `n ≤ N`, then it holds for every `n`**, then
verify the finitely many instances and read off RH. It also insisted that "no such theorem exists"
be narrowed, because such a theorem might be provable from explicit analytic bounds.

`RHProvability.Finiteness` settles the *shape* of that target, unconditionally:

* `exists_isCutoff : ∃ N, IsCutoff test N` — for an **arbitrary** predicate. So "there is an `N`"
  is not a conjecture about the criterion; it is a tautology.
* `isCutoff_iff_forall : (∀ n ≤ N, test n) → (IsCutoff test N ↔ ∀ n, test n)` — with the finitely
  many checks in hand (they are a finite computation), a cut-off at `N` is *equivalent* to the
  universal statement. Hence proving a cut-off at any `N` whose checks one has verified **is**
  proving the criterion, and postulating one is postulating the criterion. There is no third state.
* `isCutoff_iff_firstFail_le` — if the criterion fails somewhere, the admissible cut-offs are exactly
  the natural numbers at or above the *first* failure: an upper ray whose left endpoint is a property
  of the criterion, not of the proof.
* `lagariasCutoffTarget_iff_criterion` — the route-B target written out in full (a cut-off **and**
  the checks) is provably equivalent to `lagariasCriterion`. It is therefore **not** a separate open
  item and must never be listed as a hypothesis weaker than RH.

The narrowing requested is thus accepted, but it lands somewhere sharper than expected: the
finiteness theorem may well be *provable*, and that is exactly the problem — proving it proves RH.
The stuck inequality is named in `NOTES-iteration12-route-B.md` §3: Robin's unconditional error term
`0.6483/log log n` would have to be pushed to `o(1/log n)`, and that improvement *is* Robin's theorem.
(Both the constant and the order comparison are external facts recalled from the literature, **not**
machine-checked in this development.)

One direction of attack is explicitly ruled out on information grounds (not machine-checked, recorded
so that it is not retried): verifying the zeros up to height `T` bounds how **far out** a counterexample
must lie, whereas a cut-off needs a bound on how **close in** it must lie. The two directions oppose.

### Two shapes a tail can have (`RHProvability.TailShape`)

An independent reviewer's follow-up question was the right one: **would the proposed tail statement
hold automatically if RH were true?** If yes, it is the cut-off defect again. The answer differs by
shape, and both answers are machine-checked:

* **Cut-off shape.** `countsCutoff_collapse` and `countsCutoffTarget_iff_countsEq` instantiate the
  generic collapse at a *zero-counting* predicate: a cut-off on `lineCount = stripCount` is equivalent
  to `∀ n, lineCount n = stripCount n`. Because `isCutoff_iff_forall` never inspects the predicate,
  no cut-off shape escapes — arithmetic or analytic. **Same defect.**
* **Bound shape.** `backlundShape_blind` exhibits a function satisfying the `BacklundBound` shape that
  is identically zero. So the shape cannot distinguish an empty strip from a full one, cannot locate a
  zero, and cannot force two counts to be equal. `backlund_gives_upper_bounds_only` records what it
  does give: upper bounds for both counts, while `countsEq_iff_riemannHypothesis` says RH is the
  *equality*. **RH-free, hence worthless as progress** — a library hole, not an RH gap.

### The structural reason a whole class of tools stops in the same place

This is the one statement in Part VII that is meant to outlive the particular routes it was extracted
from, so it is stated separately and with its two halves labelled.

**Machine-checked half.** An upper bound never produces a lower bound. `lineCount_le_of_backlund`
delivers `lineCount T ≤ C·T·log T`; `countsEq_is_not_a_bound_statement` says RH is the *equality*
`lineCount T = stripCount T`. Reading an equality off an inequality is not a gap in execution, it is a
type error in the strategy.

**Mathematical half (not machine-checked — and corrected once, recorded here).**

An earlier version of this paragraph claimed that *no* ingredient of the analytic toolkit supplies a
lower bound for `lineCount`, and concluded "RH is two-sided, the toolbox is one-sided". **That is
factually wrong** and the correction matters, because the two versions point at different research
targets. The lower-bound family is classical and famous:

| result | statement |
|---|---|
| Hardy (1914) | infinitely many zeros of `ζ` lie on the critical line |
| Selberg (1942) | a positive proportion of the zeros lie on the line |
| Levinson (1974) | at least `1/3` of the zeros lie on the line |
| Conrey (1989) | at least `2/5` of the zeros lie on the line |

So the honest diagnosis is not "one-sided tools". It is: **the lower-bound constant is stuck.** RH asks
for that constant to be exactly `1`; the Hardy–Selberg–Levinson–Conrey family reaches about `2/5`, and
improvements since 1989 have been measured in thousandths. The obstruction for this family is
understood to lie in the length of the mollifier. *Why the constant cannot be pushed further by this
method* is a concrete mathematical question and is the natural successor question to this section.

**Sharpened test for proposals.** The earlier version of the test read "a route must name where its
lower bound comes from". That test is too weak: the lower bound exists, so the whole family above would
pass it. Sharpened: **a route must explain how the constant reaches `1`** — or name the mechanism that
closes the gap between `2/5` and `1`. A method that only re-proves a lower bound with a better constant
is progress on a different problem.

`RHProvability.OffLine` remains worth having for the formal reason given above: it makes "how many zeros
lie off the line" an object (`offLineCount`), so density statements can be stated, scoped and refused
as routes (`densityBound_does_not_force_zero`) rather than argued about verbally.

**Narrowing one overstatement.** What has been excluded here are **two shapes** — the cut-off shape and
the bound shape — not "all decompositions". `TailShape`'s own header says "a negative result about
*shapes*, not about RH". The positive side — formalizing "RH holds up to height `H`" as a theorem
rather than a computation — is the next round's committed work, and is **not** in this file yet.

**Still open, and not addressed by any of this:** RH itself. Part VII removes targets; it proves
nothing about the zeros. -/

/-! ## Regression checks

The long statements are not restated above (their right-hand sides mention auxiliary definitions the
summary does not want to duplicate); they are *checked to exist with the expected name* here, so a
rename breaks the build. -/

#check @riemannHypothesis_iff_ball_nat
#check @riemannHypothesis_iff_finset
#check @riemannHypothesis_iff_stripBox
#check @trivialZerosOnLeft
#check @not_riemannHypothesis_iff_exists_off_line
#check @robinCriterionLe_iff_forall_upper
#check @zerosOnLineBox_eq_of_counts_eq
#check @riemannHypothesis_of_stripCount_le_lineCount
#check @BacklundBound
#check @stripCount_le_zeroCount
#check @exists_isCutoff
#check @isCutoff_iff_forall
#check @lagariasCutoffTarget_iff_criterion
#check @countsCutoffTarget_iff_countsEq
#check @backlundShape_blind
#check @countsEq_is_not_a_bound_statement
#check @offLineCount
#check @stripCount_eq_lineCount_add_offLineCount
#check @riemannHypothesis_iff_offLineCount_eq_zero
#check @densityBound_does_not_force_zero

end Overview
end RHProvability
