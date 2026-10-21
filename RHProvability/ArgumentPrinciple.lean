/-
# The argument principle, zero-free case: the boundary integral of `logDeriv f` vanishes

This is the first brick of block 1 (see `NOTES-iteration13-rh-up-to-height.md` §5). The target for an
explicit RH verification is: certify that a rectangle contains exactly the zeros we think it does. The
tool is the argument principle. The **zero-free half** of it is the statement proved here:

> if `f` is analytic on a neighbourhood of the closed disk and nonvanishing there, then
> `∮_{|z-c|=R} f'/f = 0`.

That is what a verification certificate needs in the case "no zeros in this box": the boundary
integral is `0`, so the box contributes nothing to the count.

## Why this needs no logarithm

Mathlib's `Complex.log` is only defined on the `slitPlane`, so the identity
`logDeriv f = deriv (log ∘ f)` (`Complex.deriv_log_comp_eq_logDeriv`,
`Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean:127`) is not available for an arbitrary
nonvanishing analytic `f` — its values may cross the negative real axis. The honest conclusion is that
the *analytic logarithm lifting* (`f` nonvanishing analytic ⇒ `f = exp g` locally) is what the
logarithm route would need, and Mathlib does not have it.

**But the logarithm is not needed.** `logDeriv f = deriv f / f` is a quotient of two analytic
functions, analytic wherever `f ≠ 0`. Feeding that to Cauchy–Goursat
(`circleIntegral_eq_zero_of_differentiable_on_off_countable`,
`Mathlib/Analysis/Complex/CauchyIntegral.lean:440`) gives the vanishing directly.

The counting half (`∫ = 2πi · #zeros`) is **not** here: it needs `order`/divisor machinery.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CanonicalDecomposition

namespace RHProvability

open Complex Metric Filter
open scoped Topology

/-- **The zero-free case of the argument principle.** If `f` is analytic and nonvanishing on a
neighbourhood of the closed disk around `c` of radius `R`, then the boundary integral of its
logarithmic derivative vanishes.

This is a genuine statement (it does not follow from RH, and it is not RH-equivalent): it is a piece of
complex analysis, and it is the half of the argument principle that a Turing-method certificate needs
when a box is asserted to contain no zeros. -/
theorem circleIntegral_logDeriv_eq_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ closedBall c R, AnalyticAt ℂ f z) (hne : ∀ z ∈ closedBall c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) = 0 := by
  have hlog : ∀ z ∈ closedBall c R, AnalyticAt ℂ (logDeriv f) z := by
    intro z hz
    have h1 : AnalyticAt ℂ (deriv f) z := (hf z hz).deriv
    have h2 : AnalyticAt ℂ (fun w => deriv f w / f w) z := h1.div (hf z hz) (hne z hz)
    exact h2
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR (s := ∅)
    Set.countable_empty ?_ ?_
  · intro z hz
    exact (hlog z hz).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z ∈ closedBall c R := ball_subset_closedBall (Set.mem_of_mem_sdiff hz)
    exact (hlog z hz').differentiableAt

/-- **The counting-use form: a nonvanishing boundary integral forces a zero inside.** Contrapositive of
`circleIntegral_logDeriv_eq_zero`. This is the shape a verification certificate consumes: to prove a
box contains a zero, it is enough to prove the boundary integral is nonzero. -/
theorem exists_zero_of_circleIntegral_logDeriv_ne_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ closedBall c R, AnalyticAt ℂ f z)
    (hint : (∮ z in C(c, R), logDeriv f z) ≠ 0) :
    ∃ z ∈ closedBall c R, f z = 0 := by
  by_contra hcon
  push Not at hcon
  exact hint (circleIntegral_logDeriv_eq_zero hR hf hcon)

/-! ## Step 1 of the counting half: the local factorization at a zero -/

/-- **Local factorization at a zero.** If `f` is analytic at `a` and the order of `f` at `a` is `n`, then
`f` is locally `(z - a)^n · g` with `g` analytic and `g a ≠ 0`.

This is the first of the three steps needed to turn `∮ logDeriv f` into `2πi · (sum of orders)`: it
converts "a zero of multiplicity `n`" into an explicit power factor times a nonvanishing function.
Extracted from `AnalyticAt.analyticOrderAt_eq_natCast`
(`Mathlib/Analysis/Analytic/Order.lean:87`), which had the machinery but is stated as an `iff` with a
`•`, so it is not directly usable downstream. -/
theorem exists_factorization_of_analyticOrderAt {f : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f a) (hn : analyticOrderAt f a = n) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧ ∀ᶠ z in 𝓝 a, f z = (z - a) ^ n * g z := by
  obtain ⟨g, hg, hgne, hge⟩ := (hf.analyticOrderAt_eq_natCast (n := n)).mp hn
  exact ⟨g, hg, hgne, by simpa [smul_eq_mul] using hge⟩

/-! ## Step 3a of the counting half: the residue of a simple pole -/

/-- **A simple pole contributes `2πi` per unit residue.** For a point `a` strictly inside the circle,
`∮_{C(c,R)} n / (z - a) dz = 2πi·n`.

This is the term that a zero of multiplicity `n` contributes to `∮ logDeriv f`; combined with
`circleIntegral_logDeriv_eq_zero` (the zero-free case) it is what an argument-principle count is
assembled from. -/
theorem circleIntegral_residue {c a : ℂ} {R : ℝ} {n : ℂ} (ha : a ∈ ball c R) :
    (∮ z in C(c, R), n / (z - a)) = 2 * ((Real.pi : ℝ) : ℂ) * I * n := by
  have hfun : (fun z : ℂ => n / (z - a)) = fun z => (z - a)⁻¹ • n := by
    funext z
    rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [hfun, circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball ha]
  simp only [smul_eq_mul]

/-! ## Step 2 of the counting half: the logarithmic derivative of a power factor -/

/-- **`logDeriv` of a power factor.** Away from `a`, the logarithmic derivative of `(· - a)^k` is
`k / (· - a)`. This is the term that carries the multiplicity in `∮ logDeriv f`. -/
theorem logDeriv_zpow_sub {a z : ℂ} {k : ℤ} (hz : z ≠ a) :
    logDeriv (fun w : ℂ => (w - a) ^ k) z = (k : ℂ) / (z - a) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => w - a) z := differentiableAt_id.sub_const a
  rw [logDeriv_fun_zpow hdiff k, logDeriv_apply]
  have hderiv : deriv (fun w : ℂ => w - a) z = 1 := by
    simp
  rw [hderiv, mul_one_div]

/-- **A finite set of poles contributes `2πi` times the sum of its residues.** For points strictly
inside the circle,
`∮_{C(c,R)} ∑_a k_a/(z-a) dz = 2πi · ∑_a k_a`.

This is the assembly step of the argument principle: once `logDeriv f` is locally `∑ k_a/(z-a)` plus a
logarithmic derivative with no poles, this theorem produces the `2πi · (total multiplicity)` term. -/
theorem circleIntegral_finset_residue (s : Finset ℂ) (k : ℂ → ℤ) {c : ℂ} {R : ℝ}
    (hs : ∀ a ∈ s, a ∈ ball c R) :
    (∮ z in C(c, R), ∑ a ∈ s, (k a : ℂ) / (z - a))
      = 2 * ((Real.pi : ℝ) : ℂ) * I * (∑ a ∈ s, (k a : ℂ)) := by
  classical
  rw [circleIntegral.integral_fun_sum]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a ha => circleIntegral_residue (hs a ha)
  · intro a ha
    have hlt : ‖a - c‖ < R := by
      have h1 : dist a c < R := mem_ball.mp (hs a ha)
      rwa [dist_eq_norm] at h1
    have hR : 0 ≤ R := le_of_lt (lt_of_le_of_lt (norm_nonneg _) hlt)
    have hne : ∀ z ∈ sphere c R, z - a ≠ 0 := by
      intro z hz hzero
      have h1 : ‖z - c‖ = R := by
        have h2 : dist z c = R := mem_sphere.mp hz
        rwa [dist_eq_norm] at h2
      have hza : z = a := sub_eq_zero.mp hzero
      subst hza
      linarith
    have hcont : ContinuousOn (fun z : ℂ => (k a : ℂ) / (z - a)) (sphere c R) :=
      ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const) hne
    exact ContinuousOn.circleIntegrable hR hcont

/-! ## The bridge: replacing a function by an equal-on-a-codiscrete-set one -/

/-- **Log-derivative integrals are unchanged by an identity-theorem upgrade.**

An independent auditor caught the following, and it is worth recording: one cannot argue that two
functions differing on a *finite* set have equal `∮ logDeriv`, because `logDeriv` involves `deriv` — the
integrand itself changes when a point changes, and `circleIntegral.integral_congr` is pointwise, not
almost-everywhere.

The correct route is an **identity theorem**: if `f` and `h` are analytic on a preconnected open `U`
containing the circle, and they agree frequently near a point of `U`, then they agree on all of `U`;
then `logDeriv f = logDeriv h` on the circle, and the pointwise congruence lemma applies.

This is the bridge needed to use Mathlib's canonical decomposition
(`MeromorphicOn.exists_canonicalDecomp`, `Analysis/Complex/CanonicalDecomposition.lean:312`), whose
equality holds only modulo `codiscreteWithin`. -/
theorem circleIntegral_logDeriv_congr_of_analyticOnNhd {U : Set ℂ} {f h : ℂ → ℂ} {R : ℝ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hh : AnalyticOnNhd ℂ h U) (hU : IsPreconnected U) (hUo : IsOpen U)
    (h₀ : z₀ ∈ U) (hfr : ∃ᶠ z in 𝓝[≠] z₀, f z = h z) (hsphere : sphere (0 : ℂ) R ⊆ U)
    (hR : 0 ≤ R) :
    (∮ z in C(0, R), logDeriv f z) = ∮ z in C(0, R), logDeriv h z := by
  have hEq : Set.EqOn f h U := hf.eqOn_of_preconnected_of_frequently_eq hh hU h₀ hfr
  refine circleIntegral.integral_congr hR fun z hz => ?_
  have hzU : z ∈ U := hsphere hz
  have hnhds : f =ᶠ[𝓝 z] h := by
    filter_upwards [hUo.mem_nhds hzU] with w hw using hEq hw
  exact (logDeriv_congr_nhds hnhds).self_of_nhds

/-! ## The last ingredient: the integral of an affine denominator's logarithmic derivative -/

/-- **The nonvanishing factor contributes nothing.** For `‖w‖ < R`, the function `z ↦ R² - w̄ z` is
analytic and nowhere zero on the closed disk, so by `circleIntegral_logDeriv_eq_zero` its log-derivative
integrates to `0`.

This is exactly the contribution of the *denominator* of the canonical factor
`canonicalFactor R w = (R² - w̄·)/ (R·(· - w))`; the numerator contributes `2πi` through
`circleIntegral_residue`, giving the canonical factor's total `∓2πi`. -/
theorem circleIntegral_logDeriv_affine_eq_zero {w : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w‖ < R) :
    (∮ z in C(0, R), logDeriv (fun z : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) z) = 0 := by
  refine circleIntegral_logDeriv_eq_zero hR.le (fun z _ => ?_) (fun z hz => ?_)
  · exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  · intro hzero
    have hzn : ‖z‖ ≤ R := by
      have h := mem_closedBall.mp hz
      rwa [dist_eq_norm, sub_zero] at h
    have heq : (R : ℂ) ^ 2 = (starRingEnd ℂ) w * z := sub_eq_zero.mp hzero
    have hn : ‖(R : ℂ) ^ 2‖ = ‖(starRingEnd ℂ) w * z‖ := by rw [heq]
    rw [norm_pow, Complex.norm_real, norm_mul, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos hR] at hn
    have h2 : ‖w‖ * ‖z‖ ≤ ‖w‖ * R := mul_le_mul_of_nonneg_left hzn (norm_nonneg _)
    have h3 : ‖w‖ * R < R * R := mul_lt_mul_of_pos_right hw hR
    nlinarith [hn, h2, h3]

/-! ## The canonical factor's logarithmic derivative, pointwise on the circle -/

/-- **`logDeriv` of the canonical factor, explicitly.** For `‖w‖ < R` and `z` on the circle of radius
`R`,

`logDeriv (canonicalFactor R w) z = -w̄/(R² - w̄ z) - 1/(z - w)`.

The first term is the logarithmic derivative of the numerator `z ↦ R² - w̄ z`, whose circle integral
vanishes by `circleIntegral_logDeriv_affine_eq_zero`; the second is a simple pole at `w`, contributing
`2πi` by `circleIntegral_residue`. Hence the total is `-2πi`. -/
theorem logDeriv_canonicalFactor_apply {w z : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w‖ < R)
    (hz : z ∈ sphere (0 : ℂ) R) :
    logDeriv (Complex.canonicalFactor R w) z =
      -((starRingEnd ℂ) w) / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) - 1 / (z - w) := by
  have hzn : ‖z‖ = R := by
    have h := mem_sphere.mp hz
    rwa [dist_eq_norm, sub_zero] at h
  have hzw : z - w ≠ 0 := by
    intro h
    have h' : z = w := sub_eq_zero.mp h
    rw [h'] at hzn
    linarith
  have hzN : (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0 := by
    intro hzero
    have heq : (R : ℂ) ^ 2 = (starRingEnd ℂ) w * z := sub_eq_zero.mp hzero
    have hn : ‖(R : ℂ) ^ 2‖ = ‖(starRingEnd ℂ) w * z‖ := by rw [heq]
    rw [norm_pow, Complex.norm_real, norm_mul, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos hR, hzn] at hn
    have h2 : ‖w‖ * R < R * R := mul_lt_mul_of_pos_right hw hR
    nlinarith [hn, h2]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hDne : (R : ℂ) * (z - w) ≠ 0 := mul_ne_zero hR0 hzw
  have hderivN : HasDerivAt (fun y : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * y)
      (0 - (starRingEnd ℂ) w * 1) z :=
    (hasDerivAt_const (x := z) ((R : ℂ) ^ 2)).sub ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) w))
  have hderivD : HasDerivAt (fun y : ℂ => (R : ℂ) * (y - w)) ((R : ℂ) * 1) z :=
    ((hasDerivAt_id z).sub_const w).const_mul ((R : ℂ))
  have hsplit : logDeriv (fun y : ℂ => ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * y) / ((R : ℂ) * (y - w))) z
      = logDeriv (fun y : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * y) z
        - logDeriv (fun y : ℂ => (R : ℂ) * (y - w)) z :=
    logDeriv_div z hzN hDne hderivN.differentiableAt hderivD.differentiableAt
  have hcf : Complex.canonicalFactor R w
      = fun y : ℂ => ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * y) / ((R : ℂ) * (y - w)) := by
    funext y
    exact Complex.canonicalFactor_apply R w y
  rw [hcf, hsplit, logDeriv_apply, logDeriv_apply, hderivN.deriv, hderivD.deriv]
  field_simp
  ring

/-- **A canonical factor contributes `-2πi`.** For `‖w‖ < R`,

`∮_{C(0,R)} logDeriv (canonicalFactor R w) = -2πi`.

The sign is consistent with `canonicalFactor` having a *simple pole* at `w`
(`meromorphicOrderAt_canonicalFactor = -1`), while the canonical decomposition uses the exponent
`-divisor`, so each unit of multiplicity contributes `+2πi` to the count.

This is the last ingredient of the argument-principle counting formula. -/
theorem circleIntegral_logDeriv_canonicalFactor {w : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w‖ < R) :
    (∮ z in C(0, R), logDeriv (Complex.canonicalFactor R w) z)
      = -(2 * ((Real.pi : ℝ) : ℂ) * I) := by
  -- nonvanishing of the numerator and of `z - w` on the circle
  have hNne : ∀ z ∈ sphere (0 : ℂ) R, (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0 := by
    intro z hz
    have hzn : ‖z‖ = R := by
      have h := mem_sphere.mp hz
      rwa [dist_eq_norm, sub_zero] at h
    intro hzero
    have heq : (R : ℂ) ^ 2 = (starRingEnd ℂ) w * z := sub_eq_zero.mp hzero
    have hn : ‖(R : ℂ) ^ 2‖ = ‖(starRingEnd ℂ) w * z‖ := by rw [heq]
    rw [norm_pow, Complex.norm_real, norm_mul, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos hR, hzn] at hn
    have h2 : ‖w‖ * R < R * R := mul_lt_mul_of_pos_right hw hR
    nlinarith [hn, h2]
  have hwne : ∀ z ∈ sphere (0 : ℂ) R, z - w ≠ 0 := by
    intro z hz
    have hzn : ‖z‖ = R := by
      have h := mem_sphere.mp hz
      rwa [dist_eq_norm, sub_zero] at h
    intro h
    have h' : z = w := sub_eq_zero.mp h
    rw [h'] at hzn
    linarith
  have hAint : CircleIntegrable (fun z : ℂ => -((starRingEnd ℂ) w) /
      ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z)) 0 R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    have hcont : ContinuousOn (fun z : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) (sphere (0 : ℂ) R) := by
      fun_prop
    exact ContinuousOn.div
      (continuousOn_const : ContinuousOn (fun _ : ℂ => -((starRingEnd ℂ) w)) (sphere (0 : ℂ) R))
      hcont hNne
  have hBint : CircleIntegrable (fun z : ℂ => 1 / (z - w)) 0 R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    have hcont : ContinuousOn (fun z : ℂ => z - w) (sphere (0 : ℂ) R) := by fun_prop
    exact ContinuousOn.div
      (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (sphere (0 : ℂ) R))
      hcont hwne
  have hNlog : (∮ z in C(0, R), logDeriv (fun y : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * y) z) = 0 :=
    circleIntegral_logDeriv_affine_eq_zero hR hw
  have hkey : (fun z : ℂ => -((starRingEnd ℂ) w) / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z))
      = fun z => logDeriv (fun y : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * y) z := by
    funext z
    have hderiv : HasDerivAt (fun y : ℂ => (R : ℂ) ^ 2 - (starRingEnd ℂ) w * y)
        (0 - (starRingEnd ℂ) w * 1) z :=
      (hasDerivAt_const (x := z) ((R : ℂ) ^ 2)).sub ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) w))
    rw [logDeriv_apply, hderiv.deriv]
    by_cases hz : ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) = 0
    · simp [hz]
    · field_simp
      ring
  have h1 : (∮ z in C(0, R), -((starRingEnd ℂ) w) /
      ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z)) = 0 := by
    rw [hkey, hNlog]
  have h2 : (∮ z in C(0, R), 1 / (z - w)) = 2 * ((Real.pi : ℝ) : ℂ) * I := by
    have := circleIntegral_residue (c := 0) (a := w) (R := R) (n := 1) (by simpa using hw)
    simpa using this
  rw [circleIntegral.integral_congr hR.le (fun z hz => logDeriv_canonicalFactor_apply hR hw hz),
    circleIntegral.integral_sub hAint hBint, h1, h2]
  ring

end RHProvability
