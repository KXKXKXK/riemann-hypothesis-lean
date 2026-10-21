/-
# The first certified instance of a criterion check

`TightBounds.lagariasRHS_two_tight` brackets the Lagarias right-hand side at `n = 2`:
`3314/1000 ≤ H_2 + exp(H_2)·log(H_2) ≤ 3321/1000`. Since `σ(2) = 3 < 3.314`, the certified arithmetic
**decides** the criterion at `n = 2`: `lagariasTest 2` holds.

This is the first input on which the check actually runs end-to-end: rational bounds on `log` and
`exp` → composition (`lagariasRHS_bounds`) → comparison with `σ`. It is one instance, not a decision
procedure for all `n`, and it does not use any unproved equivalence with RH.

For contrast, the *loose* bounds from `Numeric.lagariasRHS_two_bounds`
(`7/3 ≤ RHS 2 ≤ 19/2`) do **not** decide it: the lower end `7/3` is below `σ(2) = 3`.
-/
import RHProvability.TightBounds

namespace RHProvability

/-- **The Lagarias criterion passes at `n = 2`, by certified rational arithmetic.**

Numerically the right-hand side is `≈ 3.317`, comfortably above `σ(2) = 3`; the machine-checked
bracket `[3.314, 3.321]` is tight enough to separate them. -/
theorem lagariasTest_two : lagariasTest 2 := by
  unfold lagariasTest
  have hb := lagariasRHS_two_tight.1
  have hσ : (sigmaNat 2 : ℝ) = 3 := by
    rw [sigmaNat_two]
    norm_num
  rw [hσ]
  linarith

/-- The loose bounds do **not** suffice at `n = 2`: with the old bracket the lower end is `7/3 < 3`,
so the same argument fails. This records why tightening (task-6) was necessary. -/
theorem loose_bounds_insufficient_two : (7 / 3 : ℝ) < (sigmaNat 2 : ℝ) := by
  rw [sigmaNat_two]
  norm_num

end RHProvability
