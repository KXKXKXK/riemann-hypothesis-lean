# Riemann Hypothesis in Lean 4

A formalisation of some results *around* the Riemann Hypothesis: equivalences between its
textbook formulations, the logical skeleton that makes "is RH independent of ZFC" a well-posed
question, and one route that turned out to be a tautology.

**RH is not proved here, and nothing in this repository is evidence for or against it.**

What the repository does contain:

- several unconditional equivalences between the standard formulations of RH, machine-checked;
- a few facts that Mathlib was missing, proved from what Mathlib does have;
- the asymmetry that makes `T ⊬ ¬RH` imply RH, derived rather than assumed;
- a proof that a popular "verify finitely many cases and read off the result" scheme cannot
  work as a strict weakening of the criterion;
- certified rational bounds that decide the Lagarias criterion at `n = 2`.

The one-line summary in `RHProvability/Overview.lean` is accurate and I will not improve on it:
*one route eliminated by machine-checked theorem, one route's worth of content identified,
zero progress on RH itself.*

## Status

| | |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`) |
| Declarations | 295 theorems, 6 lemmas, 49 definitions |
| `sorry` / `admit` | none |
| user-declared `axiom` | none |

Every theorem in `Overview.lean` Part I is checked with `#print axioms` and depends at most on
`propext`, `Classical.choice`, `Quot.sound`; several depend on none.

`Overview.lean` is a compilable census of the whole development, not prose about it. If a result
disappears or changes type, `lake build` fails.

## The parts worth reading

### 1. RH is a concrete Lean statement, and three textbook forms of it are equivalent

`RiemannHypothesis` already exists in Mathlib, but as an opaque-looking predicate. The first thing
this project does is pin it to something checkable:

- `item1` — Mathlib's `RiemannHypothesis` is equivalent to the textbook critical-strip statement.
  This one is unconditional.
- `item3` — RH is equivalent to `NoZerosRightOfCriticalLine`: no zero of `ζ` inside the strip has
  real part exceeding `1/2`.
- `item19` — the counting invariant `lineCount T = stripCount T` for all `T` is *equivalent* to RH,
  not merely implied by it.

The route to `item1` runs through `item2`: every even-index Bernoulli number with positive index is
nonzero. Mathlib did not have this. It is derived here from `ζ(2k) ≠ 0` and the closed form, so it
is not circular.

### 2. The asymmetry

For a `Π⁰₁` statement `P`, if a theory `T` does not prove `¬P`, then `P` is true. `item6` is the
general form; `item7` is the RH face of it. The three hypotheses it consumes — an arithmetisation,
the witness scheme, and `Σ₁`-completeness — are not proved anywhere in this library.

This is why "RH is independent of ZFC" is not a way around proving RH: proving independence would
give RH itself, in the metatheory. The repo states this as a theorem rather than as an opinion.

### 3. A shortcut that does not work

Route B was: find an explicit `N` such that, if a criterion holds for every `n ≤ N`, it holds for
every `n`; verify the finitely many cases; read off RH.

`RHProvability/Finiteness.lean` settles the shape of this unconditionally:

- `exists_isCutoff` — `∃ N, IsCutoff test N` holds for an *arbitrary* predicate. So "there is an
  `N`" is not a conjecture about the criterion, it is a tautology.
- `isCutoff_iff_forall` — with the finitely many checks in hand, a cut-off at `N` is *equivalent*
  to the universal statement.

So proving a cut-off at any `N` whose checks are verified **is** proving the criterion, and
postulating one is postulating the criterion. There is no third state. This is the one route this
project eliminates by theorem.

An earlier note also concluded, from a machine-checked counterexample (`item17`), that strictness
cannot be recovered from a strictly descending upper approximation. `item34` does the same for the
Padé `[1/1]` lower bound for `log`: the statement is true for `y ≥ 1` and false below it, so the
domain restriction is a real one and not an artefact of the proof.

### 4. Something that works, at small `n`

`item37` is the first certified instance of a criterion check: `lagariasTest 2` is decided by a
rational bracket of width `0.007` (`item36`). The loose bracket in `item28` is not enough at `n = 2`
— `item38` proves `7/3 < σ(2) = 3`, which is why the tight bound was needed.

`item20` and `item21` together record an edge case that is easy to get wrong: at `n = 1` the
Lagarias inequality is an equality, so its strict form is false there.

**Decidability is not proof.** Deciding `lagariasTest n` for each `n` gives the universal statement
one instance at a time, forever. It does not give `∀ n`.

## What was wrong before

This project was audited by a reader who was not the author, and five claims did not survive. They
are kept as compiled theorems in `RHProvability/Audit.lean` rather than quietly deleted:

1. `Pi01` had no computability constraint, so `Nonempty (Pi01 P)` was provable for *every* `P` —
   which made two registered "gaps" vacuous. Fixed; the old defect is preserved as
   `Audit.pi01Old_trivially_inhabited`.
2. A registered bound on `log log n` was not open but **false**. Refutation: compiled.
3. The claim "Mathlib lacks `ζ(conj s) = conj(ζ s)`" was **wrong**. The lemma is in Mathlib; an
   earlier grep had been restricted to one subdirectory, violating this project's own scan rule.
4. A `Re z = 0` boundary case was described as a gap. It is a small lemma.
5. Several docstrings were inconsistent with the code.

No theorem was weakened and no axiom was added to accommodate the audit. Details are in
`Overview.lean` Part V.

## What this route is still missing

`Overview.lean` Part VI lists three items. The short version:

1. `RiemannHypothesis ↔ lagariasCriterion` is **not formalised here**. The statement ports cleanly;
   the proof core is blocked by a missing package (`PrimeNumberTheoremAnd`), not by API drift.
2. A finiteness cut-off — see above. The shape cannot be a strict weakening.
3. Computable `exp`/`log` bounds tight enough to decide the criterion at each `n`. Exact at `n = 2`;
   no general `n` yet.

Item 2 is the real wall. The stuck inequality is Robin's unconditional error term
`0.6483/log log n`, which would have to become `o(1/log n)` — and that improvement *is* Robin's
theorem. Both the constant and the order comparison are recalled from the literature, not
machine-checked.

## Route map

`docs/route-map.html` is an interactive graph of the development: every theorem, registration and
gap as a node, with edges labelled by the kind of relation (`⟺`, `⟹`, `⊣`, `⇢`). It loads from disk
with no external dependencies.

Open it directly, or pass `?lang=zh` for Chinese. Node notes carry the honest limitation for each
claim — for instance that `N(T) = O(T log T)` gives no edge to RH at all, because a bound on the
count does not imply an equality of counts.

## Build

```bash
lake exe cache get   # ~5 GB of Mathlib oleans
lake build
```

`docs/figs/` holds four plots from a side computation on the prolate spheroidal wave operator
(`reports/prolate-2026-10-20.md` in the source tree); they are not used by the Lean build.

## Layout

| path | what |
|---|---|
| `RHProvability/Overview.lean` | the census: part I proved, II assumptions, III gaps, IV negative, V audit, VI what is missing, VII route B |
| `RHProvability/Provability.lean` | abstract provability interface; `Con` is defined, not assumed |
| `RHProvability/RHFormulas.lean` | Mathlib's `RiemannHypothesis` vs the textbook statement |
| `RHProvability/BernoulliZeta.lean` | the Bernoulli non-vanishing fact Mathlib lacks |
| `RHProvability/Reflection.lean` | functional equation ⇒ no zeros right of the critical line |
| `RHProvability/Pi01.lean` | `Π⁰₁` presentation and the asymmetry |
| `RHProvability/Finiteness.lean` | why route B is a tautology |
| `RHProvability/LineCountClosed.lean` | the counting invariant as an equivalence |
| `RHProvability/TailShape.lean`, `OffLine.lean` | two more tail shapes, both excluded |
| `RHProvability/Audit.lean` | the five audit findings, as compiled theorems |
| `RHProvability/Backlund.lean`, `Robin.lean`, `Lagarias.lean`, `Numeric.lean`, `TightBounds.lean` | upstream / numerical machinery |

## References

The external results used are cited where they are used. The ones that matter most:

- Robin (1984) — the criterion and its threshold at `n ≥ 5041`.
- Lagarias (2001/2002) — the elementary equivalent.
- Bettin–Gonek (2017) — `θ = ∞` implies RH, which is why density results stop short.
- Backlund / Riemann–von Mangoldt — the `O(T log T)` zero count.

## Licence

MIT.
