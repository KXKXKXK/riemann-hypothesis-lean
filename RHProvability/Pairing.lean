/-
# The off-line quartet, the same-height pairing, and the ceiling of density arguments

(v2 — revised after external review.  Changes: the reflection invariance is now explicitly restricted
to the open strip; the density model is parametrised by the *excess* of same-height pairs, so that
`o(N)`, finite, and positive-density excesses are distinguished; and a multiplicity layer
(`heightMult`, `heightsSeparated`) replaces the plain `Set` formulation, where a double zero is
invisible.)

## What is proved here

1. **The orbit.**  Inside the open strip `0 < Re s < 1` the zero set of `ζ` is invariant under
   `ρ ↦ 1 - ρ` (`riemannZeta_zero_reflect`, file `Reflection.lean`) and under `ρ ↦ \bar ρ`
   (`riemannZeta_conj`, real Dirichlet coefficients).  For `ρ = 1/2 + δ + iγ` the orbit is the
   rectangle `{1/2 ± δ ± iγ}`; **all four points are at distance `|δ|` from the critical line**
   (`quartet_equidistant`).  The invariance is *false* outside the strip: the trivial zero `-2(n+1)`
   reflects to `1 + 2(n+1)`, where `ζ ≠ 0` (`trivial_zero_reflection_not_a_zero`).

2. **The pairing.**  In the upper half plane the useful involution is `ρ ↦ 1 - \bar ρ` (`partner`); it
   preserves the height and reflects the real part.  Hence an off-line zero forces a second, distinct
   zero at *exactly* the same height (`exists_same_height_of_off_line`).

3. **Multiplicities.**  With heights counted with multiplicity (`heightMult`), "no two zeros at the
   same height" is equivalent to "all zeros on the critical line **and** all zeros simple"
   (`heightsSeparated_iff`).  The set-level statement only gives the first half; a double zero is a
   single element of a `Set`.  Note that RH is *not* known to imply simplicity, so this target is
   strictly stronger than RH.

4. **The arithmetic ceiling.**  If the number of ordered same-height pairs is `N + 2·M(N)` (one
   off-line zero contributes `+2`), the normalised density is `1 + 2·M(N)/N`
   (`sameHeightDensity`).  If `M = o(N)` (in particular for a *fixed* number of quartets) this tends
   to `1` (`density_tendsto_one_of_excess_littleO`), which is exactly the density-one conclusion of the
   pair-correlation literature; a positive density `M ~ cN` instead gives `1 + 2c`
   (`density_tendsto_one_add_two_c`), which such a conclusion *would* exclude.  So density statements
   exclude positive-density off-line sets and nothing more.

**Scope.**  §1–§4 are implications from hypotheses.  The density function is a *model* of the
normalised same-height count, not an identity for `ζ`: its limit is a consequence of the definition.
Nothing here says whether `ζ` has off-line zeros, and §3's literature facts (which theorem assumes
what, with which error term) are external input that is not formalised.
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RHProvability.Reflection

namespace RHProvability

open Complex Filter
open scoped Real ComplexConjugate

/-! ## 1. The symmetry group and the four-point orbit -/

/-- `ρ ↦ 1 - ρ`: the reflexion in the critical line.  For zeros of `ζ` inside the open strip this map
preserves the zero set (`riemannZeta_zero_reflect`); outside the strip it does not
(`trivial_zero_reflection_not_a_zero`). -/
def reflLine (s : ℂ) : ℂ := 1 - s

/-- `ρ ↦ \bar ρ`: complex conjugation, a symmetry of the zero set because the Dirichlet coefficients
of `ζ` are real (`riemannZeta_conj`). -/
def reflReal (s : ℂ) : ℂ := conj s

/-- `ρ ↦ 1 - \bar ρ`: the **same-height partner**.  It is the composition of the two reflexions, it is
an involution, and it is the only nontrivial element of the group that preserves the height. -/
def partner (s : ℂ) : ℂ := 1 - conj s

@[simp] theorem partner_re (s : ℂ) : (partner s).re = 1 - s.re := by
  simp [partner]

@[simp] theorem partner_im (s : ℂ) : (partner s).im = s.im := by
  simp [partner]

@[simp] theorem partner_partner (s : ℂ) : partner (partner s) = s := by
  simp [partner]

/-- The same-height partner fixes exactly the critical line. -/
theorem partner_eq_self_iff {s : ℂ} : partner s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre : (partner s).re = s.re := by rw [h]
    rw [partner_re] at hre
    linarith
  · intro h
    refine Complex.ext ?_ ?_
    · rw [partner_re]; linarith
    · rw [partner_im]

/-- The four points forced by the two reflexions. -/
noncomputable def quartet (s : ℂ) : Finset ℂ := {s, 1 - s, conj s, 1 - conj s}

theorem mem_quartet {s z : ℂ} :
    z ∈ quartet s ↔ z = s ∨ z = 1 - s ∨ z = conj s ∨ z = 1 - conj s := by
  simp [quartet]

/-- Squared Euclidean distance in the `(σ,t)` plane. -/
def dist2 (z w : ℂ) : ℝ := (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2

theorem dist2_comm (z w : ℂ) : dist2 z w = dist2 w z := by
  simp only [dist2]; ring

/-- **All four points are at the same distance `|δ|` from the critical line.** -/
theorem quartet_equidistant {s z : ℂ} (hz : z ∈ quartet s) :
    (z.re - 1 / 2) ^ 2 = (s.re - 1 / 2) ^ 2 := by
  simp only [quartet, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with h | h | h | h
  · subst h; ring
  · subst h; simp only [Complex.sub_re, Complex.one_re]; ring
  · subst h; simp only [Complex.conj_re]
  · subst h; simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; ring

/-- Vertical pair `{ρ, \bar ρ}`: distance `2|γ|`. -/
theorem dist2_vertical (s : ℂ) : dist2 s (conj s) = 4 * s.im ^ 2 := by
  simp only [dist2, Complex.conj_re, Complex.conj_im]; ring

/-- Horizontal pair `{ρ, 1 - \bar ρ}`: **same height**, distance `2|δ|`. -/
theorem dist2_horizontal (s : ℂ) : dist2 s (1 - conj s) = 4 * (s.re - 1 / 2) ^ 2 := by
  simp only [dist2, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Diagonal pair `{ρ, 1 - ρ}`: distance `2√(δ²+γ²)`. -/
theorem dist2_diagonal (s : ℂ) :
    dist2 s (1 - s) = 4 * ((s.re - 1 / 2) ^ 2 + s.im ^ 2) := by
  simp only [dist2, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- The mirror images of the three distances, from the lower half plane. -/
theorem dist2_vertical_lower (s : ℂ) : dist2 (1 - s) (1 - conj s) = 4 * s.im ^ 2 := by
  simp only [dist2, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem dist2_horizontal_lower (s : ℂ) :
    dist2 (conj s) (1 - s) = 4 * (s.re - 1 / 2) ^ 2 := by
  simp only [dist2, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem dist2_diagonal_lower (s : ℂ) :
    dist2 (conj s) (1 - conj s) = 4 * ((s.re - 1 / 2) ^ 2 + s.im ^ 2) := by
  simp only [dist2, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-! ## 2. The pairing, abstractly -/

/-- The same-height partner of a zero is a zero, whenever the zero set is invariant under both
reflexions. -/
theorem partner_mem {Z : Set ℂ} (hcompl : ∀ z ∈ Z, 1 - z ∈ Z)
    (hconj : ∀ z ∈ Z, conj z ∈ Z) {s : ℂ} (hs : s ∈ Z) : partner s ∈ Z := by
  have h1 : conj s ∈ Z := hconj s hs
  have h2 : 1 - conj s ∈ Z := hcompl (conj s) h1
  simpa only [partner] using h2

/-- **The pairing lemma** (positions only).  An off-line zero forces a second, distinct zero at
exactly the same height. -/
theorem exists_same_height_of_off_line {Z : Set ℂ} (hcompl : ∀ z ∈ Z, 1 - z ∈ Z)
    (hconj : ∀ z ∈ Z, conj z ∈ Z) {s : ℂ} (hs : s ∈ Z) (hoff : s.re ≠ 1 / 2) :
    ∃ s' ∈ Z, s' ≠ s ∧ s'.im = s.im := by
  exact ⟨partner s, partner_mem hcompl hconj hs,
    fun h => hoff (partner_eq_self_iff.mp h), partner_im s⟩

/-- **Positions version**: if no two distinct zero *positions* share a height, every position is on
the critical line.  This is the half of `heightsSeparated_iff` that a `Set` can see: it says nothing
about multiplicities, hence nothing about simplicity. -/
theorem onLine_of_separated_heights {Z : Set ℂ} (hcompl : ∀ z ∈ Z, 1 - z ∈ Z)
    (hconj : ∀ z ∈ Z, conj z ∈ Z)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z.im = z'.im → z = z') {s : ℂ} (hs : s ∈ Z) :
    s.re = 1 / 2 := by
  have hp : partner s ∈ Z := partner_mem hcompl hconj hs
  exact partner_eq_self_iff.mp (hsep (partner s) hp s hs (partner_im s))

/-! ## 3. Multiplicities: `Set` is not enough

A double zero at `1/2 + iγ` is a single element of a `Set ℂ`, so the `Set`-level hypothesis above
cannot see it.  The next layer represents a zero configuration as a finite set `Z` of positions
together with a multiplicity function `m` supported on `Z`; `heightMult` is the multiplicity of a
height. -/

/-- `heightMult Z m t`: multiplicity of the height `t`. -/
noncomputable def heightMult (Z : Finset ℂ) (m : ℂ → ℕ) (t : ℝ) : ℕ :=
  ∑ z ∈ Z.filter (fun z => z.im = t), m z

/-- **No two zeros at the same height, counted with multiplicity.** -/
def heightsSeparated (Z : Finset ℂ) (m : ℂ → ℕ) : Prop := ∀ t : ℝ, heightMult Z m t ≤ 1

/-- Every zero of the configuration lies on the critical line. -/
def allOnLine (m : ℂ → ℕ) : Prop := ∀ z : ℂ, m z ≠ 0 → z.re = 1 / 2

/-- Every zero of the configuration is simple. -/
def allSimple (m : ℂ → ℕ) : Prop := ∀ z : ℂ, m z ≤ 1

/-- **Multiplicity layer, direction 1: separated heights force simplicity.**  (The `Set`-level
statement cannot see this: a double zero is one element.) -/
theorem allSimple_of_heightsSeparated {Z : Finset ℂ} {m : ℂ → ℕ}
    (hsupp : ∀ z, m z ≠ 0 → z ∈ Z) (hsep : heightsSeparated Z m) : allSimple m := by
  intro z
  by_contra h
  have h2 : 2 ≤ m z := by omega
  have hmz : m z ≠ 0 := by omega
  have hzZ : z ∈ Z := hsupp z hmz
  have hzF : z ∈ Z.filter (fun w => w.im = z.im) := Finset.mem_filter.mpr ⟨hzZ, rfl⟩
  have hle : m z ≤ heightMult Z m z.im := by
    unfold heightMult
    exact Finset.single_le_sum (f := fun w => m w) (fun w _ => Nat.zero_le _) hzF
  have := hsep z.im
  omega

/-- **Multiplicity layer, direction 2: separated heights force the critical line.** -/
theorem allOnLine_of_heightsSeparated {Z : Finset ℂ} {m : ℂ → ℕ}
    (hsupp : ∀ z, m z ≠ 0 → z ∈ Z) (hpos : ∀ z, m (partner z) = m z)
    (hsep : heightsSeparated Z m) : allOnLine m := by
  intro z hmz
  by_contra hre
  have hpz : partner z ∈ Z := by
    apply hsupp
    rw [hpos z]
    exact hmz
  have hzZ : z ∈ Z := hsupp z hmz
  have hne : partner z ≠ z := fun h => hre (partner_eq_self_iff.mp h)
  have hzF : z ∈ Z.filter (fun w => w.im = z.im) := Finset.mem_filter.mpr ⟨hzZ, rfl⟩
  have hpF : partner z ∈ Z.filter (fun w => w.im = z.im) :=
    Finset.mem_filter.mpr ⟨hpz, partner_im z⟩
  have hsub : ({z, partner z} : Finset ℂ) ⊆ Z.filter (fun w => w.im = z.im) := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hzF
    · exact hpF
  have hnn : ∀ w ∈ Z.filter (fun w => w.im = z.im),
      w ∉ ({z, partner z} : Finset ℂ) → 0 ≤ m w := fun _ _ _ => Nat.zero_le _
  have hge : m z + m (partner z) ≤ heightMult Z m z.im := by
    have hpair : (∑ w ∈ ({z, partner z} : Finset ℂ), m w) = m z + m (partner z) :=
      Finset.sum_pair (fun h => hne h.symm)
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have h2 : 2 ≤ heightMult Z m z.im := by
    have : m (partner z) = m z := hpos z
    omega
  have := hsep z.im
  omega

/-- **The equivalence.**  With multiplicities counted, "no two zeros at the same height" is exactly
"all zeros on the critical line *and* all zeros simple".  Since RH is not known to imply simplicity,
this target is strictly stronger than RH. -/
theorem heightsSeparated_iff {Z : Finset ℂ} {m : ℂ → ℕ}
    (hsupp : ∀ z, m z ≠ 0 → z ∈ Z) (hpos : ∀ z, m (partner z) = m z) :
    heightsSeparated Z m ↔ allOnLine m ∧ allSimple m := by
  constructor
  · intro hsep
    exact ⟨allOnLine_of_heightsSeparated hsupp hpos hsep, allSimple_of_heightsSeparated hsupp hsep⟩
  · intro ⟨hline, hsimple⟩
    intro t
    have hsum : heightMult Z m t = m ⟨1 / 2, t⟩ := by
      unfold heightMult
      refine Finset.sum_eq_single (⟨1 / 2, t⟩ : ℂ) ?_ ?_
      · intro b hb hba
        by_contra hb0
        exact hba (Complex.ext (hline b hb0) (Finset.mem_filter.mp hb).2)
      · intro hmem
        by_contra h0
        exact hmem (Finset.mem_filter.mpr ⟨hsupp _ h0, rfl⟩)
    rw [hsum]
    exact hsimple _

/-! ## 4. For the actual zeros of `ζ` -/

/-- The same-height partner of a zero of `ζ` in the open critical strip is again a zero. -/
theorem riemannZeta_partner_zero {s : ℂ} (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) : riemannZeta (partner s) = 0 := by
  have hconj : riemannZeta (conj s) = 0 := by
    rw [riemannZeta_conj, hs]
    simp
  have h0' : 0 < (conj s).re := by simpa using h0
  have h1' : (conj s).re < 1 := by simpa using h1
  have h := (riemannZeta_zero_reflect h0' h1').mpr hconj
  simpa only [partner] using h

/-- **Concrete pairing for `ζ`**: an off-line zero in the strip has a distinct zero of `ζ` at
exactly the same height. -/
theorem riemannZeta_exists_same_height {s : ℂ} (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (hoff : s.re ≠ 1 / 2) :
    ∃ s' : ℂ, riemannZeta s' = 0 ∧ s' ≠ s ∧ s'.im = s.im := by
  exact ⟨partner s, riemannZeta_partner_zero hs h0 h1,
    fun h => hoff (partner_eq_self_iff.mp h), partner_im s⟩

/-- **The reflexion does not preserve the zero set outside the strip.**  The trivial zero `-2(n+1)`
reflects to `1 + 2(n+1)`, where `ζ ≠ 0`; so the quartet argument must be stated inside
`0 < Re s < 1`, and trivial zeros have no such orbit. -/
theorem trivial_zero_reflection_not_a_zero (n : ℕ) :
    riemannZeta (1 - (-2 * ((n : ℂ) + 1))) ≠ 0 := by
  have h : (1 - (-2 * ((n : ℂ) + 1))) = 1 + 2 * ((n : ℂ) + 1) := by ring
  rw [h]
  apply riemannZeta_ne_zero_of_one_le_re
  have hcast : (1 + 2 * ((n : ℂ) + 1)) = ((1 + 2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-! ## 5. The arithmetic ceiling: which excesses are compatible with density one -/

/-- `sameHeightDensity M N = 1 + 2·M(N)/N`: the normalised same-height pair count when there are
`N` diagonal pairs and `2·M(N)` extra ordered pairs (each off-line zero contributes `2`).  This is a
**model** of the normalised count, not an identity for `ζ`. -/
noncomputable def sameHeightDensity (M : ℝ → ℝ) (N : ℝ) : ℝ := 1 + 2 * (M N / N)

/-- A **fixed** number of quartets (or any excess with `M = o(N)`) still gives density `1`. -/
theorem density_tendsto_one_of_excess_littleO {M : ℝ → ℝ}
    (hM : Filter.Tendsto (fun N : ℝ => M N / N) Filter.atTop (nhds 0)) :
    Filter.Tendsto (sameHeightDensity M) Filter.atTop (nhds 1) := by
  unfold sameHeightDensity
  have h2 : Filter.Tendsto (fun N : ℝ => 2 * (M N / N)) Filter.atTop (nhds 0) := by
    simpa using hM.const_mul 2
  have h1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa using h1.add h2

/-- A **positive density** `M ~ cN` of off-line zeros gives density `1 + 2c ≠ 1`. -/
theorem density_tendsto_one_add_two_c (c : ℝ) :
    Filter.Tendsto (fun N : ℝ => 1 + 2 * (c * N / N)) Filter.atTop (nhds (1 + 2 * c)) := by
  have hEq : (fun _ : ℝ => 1 + 2 * c) =ᶠ[Filter.atTop] (fun N : ℝ => 1 + 2 * (c * N / N)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have hN' : N ≠ 0 := ne_of_gt hN
    rw [mul_div_assoc, div_self hN', mul_one]
  exact (tendsto_const_nhds (x := 1 + 2 * c)).congr' hEq

/-- A **fixed** number of quartets (here one) still gives density `1`. -/
theorem density_one_with_one_quartet :
    Filter.Tendsto (fun N : ℝ => 1 + 2 * ((1 : ℝ) / N)) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun N : ℝ => (1 : ℝ) / N) Filter.atTop (nhds 0) := by
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 1
    simpa [div_eq_mul_inv] using this
  have h2 : Filter.Tendsto (fun N : ℝ => 2 * ((1 : ℝ) / N)) Filter.atTop (nhds 0) := by
    simpa using h.const_mul 2
  have h1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa using h1.add h2

/-- **The ceiling, formally.**  A fixed number of off-line quartets gives density `1`; a positive
density `c` gives `1 + 2c`.  So a density-one statement excludes positive-density off-line sets and
nothing more — in particular it is compatible with an isolated off-line quartet. -/
theorem ceiling :
    (Filter.Tendsto (fun N : ℝ => 1 + 2 * ((1 : ℝ) / N)) Filter.atTop (nhds 1)) ∧
      (Filter.Tendsto (fun N : ℝ => 1 + 2 * ((1 / 2 : ℝ) * N / N)) Filter.atTop (nhds 2)) ∧
        (∀ N : ℝ, 0 < N → 1 < 1 + 2 * ((1 : ℝ) / N)) := by
  refine ⟨density_one_with_one_quartet, ?_, ?_⟩
  · have h := density_tendsto_one_add_two_c (1 / 2)
    have h2 : (1 : ℝ) + 2 * (1 / 2) = 2 := by norm_num
    rwa [h2] at h
  · intro N hN
    have hpos : 0 < (1 : ℝ) / N := div_pos (by norm_num) hN
    linarith

/-- Size check at `T = 10^6`: `N(T) ≈ 1.9063 · 10^6`, so one quartet shifts the density by
`2/N < 1.1 · 10^{-6}`. -/
theorem density_shift_at_T_1e6 : (2 : ℝ) / 1906299.5767 < 1.1e-6 := by norm_num

end RHProvability
