/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Frohman
-/
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Height lower bounds for the duplication map on the elliptic curve 3936b1

The Bézout identities isolating pure seventh powers are verified by `ring`.
The GCD of the two forms divides 15744 under the coprimality hypothesis.
-/

namespace HeightDuplication

def dupNum (a u : ℤ) : ℤ := a ^ 4 + 96 * a * u ^ 3 - 48 * u ^ 4
def dupDen (a u : ℤ) : ℤ := 4 * u * (a ^ 3 - a ^ 2 * u - 12 * u ^ 3)

theorem dup_bezout_a7 (a u : ℤ) :
    (82 * a ^ 3 - 60 * a ^ 2 * u + 12 * a * u ^ 2 - 864 * u ^ 3) * dupNum a u +
      (15 * a ^ 3 + 12 * a ^ 2 * u - 1740 * a * u ^ 2 + 864 * u ^ 3) * dupDen a u =
      82 * a ^ 7 := by
  unfold dupNum dupDen
  ring

theorem dup_bezout_u7 (a u : ℤ) :
    (12 * a ^ 2 * u - 8 * a * u ^ 2 - 4 * u ^ 3) * dupNum a u +
      (-3 * a ^ 3 - a ^ 2 * u - 324 * u ^ 3) * dupDen a u =
      15744 * u ^ 7 := by
  unfold dupNum dupDen
  ring

theorem dup_gcd_dvd (a u : ℤ) (hcop : Int.gcd a u = 1) :
    (Int.gcd (dupNum a u) (dupDen a u) : ℤ) ∣ 15744 := by
  set g : ℤ := (Int.gcd (dupNum a u) (dupDen a u) : ℤ)
  have hgN : g ∣ dupNum a u := Int.gcd_dvd_left _ _
  have hgD : g ∣ dupDen a u := Int.gcd_dvd_right _ _
  have hga7 : g ∣ 82 * a ^ 7 := by
    rw [← dup_bezout_a7 a u]
    exact dvd_add (dvd_mul_of_dvd_right hgN _) (dvd_mul_of_dvd_right hgD _)
  have hgu7 : g ∣ 15744 * u ^ 7 := by
    rw [← dup_bezout_u7 a u]
    exact dvd_add (dvd_mul_of_dvd_right hgN _) (dvd_mul_of_dvd_right hgD _)
  have hga7' : g ∣ 15744 * a ^ 7 := by
    have : 82 * 192 = 15744 := by norm_num
    exact dvd_trans hga7 (dvd_mul_of_dvd_left (dvd_of_eq this) _)
  have hcop7 : IsCoprime (a ^ 7) (u ^ 7) := by
    rw [IsCoprime.pow_left, IsCoprime.pow_right]
    exact Int.isCoprime_iff_gcd_eq_one.mpr hcop
  rcases hcop7 with ⟨s, t, hbez⟩
  have hid : (15744 : ℤ) = s * (15744 * a ^ 7) + t * (15744 * u ^ 7) := by
    calc (15744 : ℤ) = 15744 * (s * a ^ 7 + t * u ^ 7) := by rw [← hbez]; ring
      _ = s * (15744 * a ^ 7) + t * (15744 * u ^ 7) := by ring
  rw [hid]
  exact dvd_add (dvd_mul_of_dvd_right hga7' _) (dvd_mul_of_dvd_right hgu7 _)

end HeightDuplication
