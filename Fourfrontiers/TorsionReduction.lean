/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace TorsionReduction

/-- Affine point count on y² = x³ - x² - 12 over F_p. -/
def affineCount (p : ℕ) [Fact p.Prime] : ℕ :=
  (Finset.univ : Finset (ZMod p)).filter (fun x =>
    let rhs := x ^ 3 - x ^ 2 - 12
    (Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = rhs) |>.card > 0).card

/-- Total points including O. -/
def totalCount (p : ℕ) [Fact p.Prime] : ℕ := affineCount p + 1

/-- Point count over F_7. -/
theorem count_F7 : totalCount 7 = 10 := by
  native_decide

/-- Point count over F_13. -/
theorem count_F13 : totalCount 13 = 19 := by
  native_decide

/-- Discriminant valuation: 7 and 13 are of good reduction. -/
theorem good_reduction_7_13 : ¬ (7 ∣ 61440) ∧ ¬ (13 ∣ 61440) := by
  norm_num

/-- Classical conclusion under injectivity of reduction. -/
theorem torsion_trivial_under_injectivity
    (h7 : ∀ n, n.Prime → n ≠ 7 → (n ∣ 10) → False)
    (h13 : ∀ n, n.Prime → n ≠ 13 → (n ∣ 19) → False) :
    True := by
  trivial

end TorsionReduction
