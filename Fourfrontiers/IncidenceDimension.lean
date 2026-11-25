/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Frohman
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace IncidenceDimension

def dimQuinticSpace : ℕ := Nat.choose 9 4 - 1

lemma dimQuinticSpace_eq : dimQuinticSpace = 125 := by decide

def dimCurveModuli (d : ℕ) : ℕ := 5 * (d + 1) - 1 - 3

lemma dimCurveModuli_eq (d : ℕ) : dimCurveModuli d = 5 * d + 1 := by
  unfold dimCurveModuli
  omega

def fiberCodim (d h1 : ℕ) : ℕ := (5 * d + 1) - h1

def incidenceStratumDim (d codimStratum h1 : ℕ) : ℕ :=
  (dimCurveModuli d - codimStratum) + (dimQuinticSpace - fiberCodim d h1)

theorem incidence_dim_eq_125 (d : ℕ) (hd : 5 * d + 1 ≤ 125) :
    incidenceStratumDim d 0 0 = 125 := by
  unfold incidenceStratumDim fiberCodim
  rw [dimCurveModuli_eq, dimQuinticSpace_eq]
  omega

end IncidenceDimension
