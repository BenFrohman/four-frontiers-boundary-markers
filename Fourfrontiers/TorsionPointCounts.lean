/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
namespace BenchmarkEllipticCurve

/-- Affine curve equation y^{2} ≡ x^{3} - x^{2} - 12 (mod p) over Fin p. -/
def onAffineCurve (p : Nat) [NeZero p] (pt : Fin p × Fin p) : Bool :=
  let (x, y) := pt
  y * y == x * x * x - x * x - (12 : Fin p)

/-- Exhaustive enumeration of all pairs (x, y) ∈ Fin p × Fin p on the affine curve. -/
def affinePoints (p : Nat) [NeZero p] : List (Fin p × Fin p) :=
  (List.finRange p).flatMap fun x =>
    (List.finRange p).filterMap fun y =>
      if onAffineCurve p (x, y) then some (x, y) else none

/-- Total projective point count #E(𝔽_p) = #E_aff(𝔽_p) + 1 (including 𝒪). -/
def projectivePointCount (p : Nat) [NeZero p] : Nat :=
  (affinePoints p).length + 1

theorem card_E_F7 : projectivePointCount 7 = 7 := by
  decide

theorem card_E_F13 : projectivePointCount 13 = 19 := by
  decide

theorem local_torsion_bound_data :
    Nat.gcd (projectivePointCount 7) (projectivePointCount 13) = 1 ∧
    Nat.gcd 7 (projectivePointCount 13) = 1 ∧
    Nat.gcd 13 (projectivePointCount 7) = 1 ∧
    62976 % 7 ≠ 0 ∧
    62976 % 13 ≠ 0 := by
  decide

end BenchmarkEllipticCurve
