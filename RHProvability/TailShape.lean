/-
# Two shapes a "tail" can have, and what each one is worth

An independent reviewer asked, before any further work on the Backlund line, the only question that
matters for a research programme: **would the statement we are trying to prove hold automatically if
RH were true?** If yes, it is the same defect as the cut-off of `RHProvability.Finiteness`
(RH-equivalent, so no intermediate progress); if no, the content has to be located and named.

This file answers that question for the two shapes on the table, and the answers are *different*:

* **Cut-off shape** ("check up to `N`, then assert the rest"). Predicate-agnostic —
  `isCutoff_iff_forall` is proved for an arbitrary `test : ℕ → Prop`, so it applies verbatim to a
  zero-counting predicate. `countsCutoff_collapse` instantiates it. **Same defect: RH-equivalent.**
* **Bound shape** (`∃ C > 0, ∃ T₀, ∀ T ≥ T₀, stripCount T ≤ C·T·log T`, i.e. `BacklundBound`). **Not**
  the same defect, and the reason is *not* that its shape is information-free — see the scope note
  below, which corrects an earlier version of this file. The reason is that the statement is
  **unconditionally true**: the classical count of zeros in the strip at height `T` is a theorem of
  the theory, valid with or without RH. A statement that holds either way cannot imply RH.

### Scope note (the earlier version of this file got this wrong)

An independent reviewer objected, correctly, to the following inference: "`backlundShape_blind`
exhibits an `f` satisfying the bound with `f ≡ 0`, therefore `BacklundBound` carries no information
about RH". The function in `BacklundBound` is **`stripCount`, fixed by `ζ`** — not an arbitrary `f`.
A witness against the *shape* does not say anything about that particular quantity; it only shows the
shape is no template for manufacturing such bounds.

That is the mirror image of the error this development had just criticised ("mistaking the shape of a
statement for its content"), so the correction is recorded rather than quietly applied:
**the main argument for "`BacklundBound` is a library gap, not an RH gap" is unconditional truth**;
`backlundShape_blind` is demoted to the rank of a remark about templates.

**Consequence for the registry.** `BacklundBound`, exactly as registered in `RHProvability.Backlund`,
is a genuine gap *for this library* (we cannot formalize the Riemann–von Mangoldt count, so we cannot
prove it), but it is **not a gap on the road to RH**: as a mathematical statement it is a theorem of
the classical theory, true with or without RH. The honest label is "library gap, RH-free". What the
count-equality route needs is not a bound but `lineCount = stripCount`, which
`countsEq_iff_riemannHypothesis` shows is RH-equivalent — i.e. the cut-off defect again.

So: after this file, both shapes tried so far are accounted for, and neither is a step towards RH.
That is a negative result about *shapes*, not about RH.
-/
import RHProvability.Finiteness
import RHProvability.Backlund
import RHProvability.LineCountClosed

namespace RHProvability

/-! ## Shape 1: a cut-off on a zero-counting predicate — same defect -/

/-- The cut-off on the count-equality predicate collapses exactly as Lagarias's did. This is the
answer to "is the zero-counting tail the same disease as the arithmetic cut-off": **for the cut-off
shape, yes, and the proof is the generic one** (`isCutoff_iff_forall`), which never looks at the
predicate. -/
theorem countsCutoff_collapse (N : ℕ)
    (hchk : ∀ n : ℕ, n ≤ N → lineCount (n : ℝ) = stripCount (n : ℝ)) :
    IsCutoff (fun n : ℕ => lineCount (n : ℝ) = stripCount (n : ℝ)) N
      ↔ ∀ n : ℕ, lineCount (n : ℝ) = stripCount (n : ℝ) :=
  isCutoff_iff_forall N hchk

/-- The same collapse written as an equivalence of the *registered target* with the conclusion, so
that a future round cannot file the cut-off as a separate gap:

`(∃ N, the count-equality cut-off at N holds ∧ the checks below N pass) ↔ (∀ n, counts are equal)`. -/
theorem countsCutoffTarget_iff_countsEq :
    (∃ N : ℕ, IsCutoff (fun n : ℕ => lineCount (n : ℝ) = stripCount (n : ℝ)) N
        ∧ ∀ n : ℕ, n ≤ N → lineCount (n : ℝ) = stripCount (n : ℝ))
      ↔ ∀ n : ℕ, lineCount (n : ℝ) = stripCount (n : ℝ) :=
  exists_isCutoff_and_checks_iff

/-! ## Shape 2: a `Backlund`-shaped bound — information-free -/

/-- **Remark about templates, not about `BacklundBound`.** The *shape* `∃ C > 0, ∃ T₀, ∀ T ≥ T₀,
f T ≤ C·T·log T` is satisfied by a function that is identically zero, so the shape alone is no way to
manufacture a bound that says anything.

**What this does not show.** It does not show that `BacklundBound` is free of information, because the
function there is `stripCount`, which `ζ` fixes. The substantive reason `BacklundBound` is not a route
to RH is in the registry note on `BacklundBound` and in the header: the statement is **unconditionally
true** (Riemann–von Mangoldt), hence true whether or not RH holds. -/
theorem backlundShape_blind :
    ∃ f : ℝ → ℝ,
      (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → f T ≤ C * T * Real.log T) ∧
        ∀ T : ℝ, f T = 0 := by
  refine ⟨fun _ => 0, ⟨1, one_pos, 1, ?_⟩, fun _ => rfl⟩
  intro T hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have : 0 ≤ 1 * T * Real.log T := mul_nonneg (mul_nonneg zero_le_one hT0) hlog
  simpa using this

/-- **What the count-equality route actually needs is an equality, not a bound.** `RH` is equivalent
to `lineCount T = stripCount T` for every `T` (`countsEq_iff_riemannHypothesis`), whereas
`BacklundBound` only produces an *upper* bound on `lineCount` (`lineCount_le_of_backlund`). An upper
bound cannot supply a lower bound, so the two statements are not on the same axis. -/
theorem countsEq_is_not_a_bound_statement :
    (∀ T : ℝ, lineCount T = stripCount T) ↔ RiemannHypothesis :=
  countsEq_iff_riemannHypothesis

/-- The registry, stated once so it cannot drift: `BacklundBound` implies an upper bound for both
counts, hence does not by itself give the equality that RH needs. This is the machine-checked part of
"BacklundBound is a library gap, not an RH gap". -/
theorem backlund_gives_upper_bounds_only (h : BacklundBound) :
    (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (lineCount T : ℝ) ≤ C * T * Real.log T) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (stripCount T : ℝ) ≤ C * T * Real.log T) :=
  ⟨lineCount_le_of_backlund h, h⟩

end RHProvability
