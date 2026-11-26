/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Fourfrontiers.HeightDuplication
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Sqrt
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Fourfrontiers.Curve3936b1

open HeightDuplication

def E : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1
  a₃ := 0
  a₄ := 0
  a₆ := -12

def multHeight (x : ℚ) : ℕ :=
  max x.num.natAbs x.den

theorem multHeight_pos (x : ℚ) : 1 ≤ multHeight x :=
  le_max_of_le_right x.pos

theorem P0_nonsingular : E.toAffine.Nonsingular 4 6 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  left
  simp [E, WeierstrassCurve.Affine.equation_iff]
  norm_num

def P0 : E.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some _ _ P0_nonsingular

theorem P0_ne_zero : P0 ≠ 0 := by
  simp [P0]

theorem doubling_x_eq_dupNum_div_dupDen {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x ^ 2 - 12) (hy0 : y ≠ 0) :
    ((3 * x ^ 2 - 2 * x) / (2 * y)) ^ 2 + 1 - 2 * x =
      (dupNum x.num x.den : ℚ) / (dupDen x.num x.den : ℚ) := by
  have hx_den_pos : (0 : ℚ) < x.den := Nat.cast_pos.mpr x.pos
  have hx_eq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0
  have h1 : ((3 * x ^ 2 - 2 * x) / (2 * y)) ^ 2 + 1 - 2 * x =
      (x ^ 4 + 96 * x - 48) / (4 * (x ^ 3 - x ^ 2 - 12)) := by
    rw [← hcurve]
    field_simp [hy0, hy2]
    linear_combination 4 * (2 * x - 1) * hcurve
  rw [h1]
  unfold dupNum dupDen
  push_cast
  rw [hx_eq]
  have hden_ne : 4 * ((x.num : ℚ) / (x.den : ℚ)) ^ 3 -
      4 * ((x.num : ℚ) / (x.den : ℚ)) ^ 2 - 48 ≠ 0 := by
    have : (x ^ 3 - x ^ 2 - 12 : ℚ) ≠ 0 := by rw [← hcurve]; exact hy2
    rw [hx_eq] at this
    intro h0; apply this; linarith
  field_simp [ne_of_gt hx_den_pos]
  ring

/-- Main Torsion Theorem: `E(ℚ)_tors = {O}` on `E : y² = x³ - x² - 12`. -/
theorem torsion_trivial (P : E.toAffine.Point) (hP : IsOfFinOrder P) : P = 0 := by
  cases P with
  | zero => rfl
  | some hns =>
    exfalso
    set Q : E.toAffine.Point := WeierstrassCurve.Affine.Point.some _ _ hns
    have hpos : 0 < addOrderOf Q := addOrderOf_pos_iff.mpr hP
    let f : ℕ → Fin (addOrderOf Q) :=
      fun k => ⟨(2 ^ k) % addOrderOf Q, Nat.mod_lt _ hpos⟩
    obtain ⟨k₁, k₂, hne, hmod_eq⟩ := Finite.exists_ne_map_eq_of_infinite f
    have hmod : (2 ^ k₁) % addOrderOf Q = (2 ^ k₂) % addOrderOf Q :=
      congrArg Fin.val hmod_eq
    have hpt_eq : (2 ^ k₁) • Q = (2 ^ k₂) • Q := by
      rw [← mod_addOrderOf_nsmul Q (2 ^ k₁), ← mod_addOrderOf_nsmul Q (2 ^ k₂), hmod]
    exact hne (pow_two_nsmul_injective hns hpt_eq)

theorem P0_infinite_order : ¬ IsOfFinOrder P0 := by
  intro hfin
  exact P0_ne_zero (torsion_trivial P0 hfin)

#print axioms torsion_trivial
#print axioms P0_infinite_order

end Fourfrontiers.Curve3936b1
