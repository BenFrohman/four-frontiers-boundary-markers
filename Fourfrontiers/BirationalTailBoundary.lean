/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib.Tactic.Omega

namespace ClemensConjecture

structure QuinticThreefoldClemensData where
  ClemensAt : ℕ → Prop
  SmoothClemensAt : ℕ → Prop
  SingularClemensAt : ℕ → Prop
  clemens_iff_smooth_and_singular :
    ∀ d, ClemensAt d ↔ SmoothClemensAt d ∧ SingularClemensAt d
  cotterill_le_11 : ∀ d, 1 ≤ d → d ≤ 11 → ClemensAt d
  ballico_fontanari_12 : SmoothClemensAt 12

/-- Uninhabited open frontier Prop. Equivalent to the Clemens Conjecture. -/
def BirationalTailCondition (Q : QuinticThreefoldClemensData) : Prop :=
  Q.SingularClemensAt 12 ∧ (∀ d, 13 ≤ d → Q.ClemensAt d)

theorem clemens_iff_birational_tail (Q : QuinticThreefoldClemensData) :
    (∀ d, 1 ≤ d → Q.ClemensAt d) ↔ BirationalTailCondition Q := by
  unfold BirationalTailCondition
  constructor
  · intro hall
    exact ⟨((Q.clemens_iff_smooth_and_singular 12).mp (hall 12 (by omega))).2,
           fun d hd => hall d (by omega)⟩
  · rintro ⟨hsing12, hge13⟩ d hd1
    by_cases h11 : d ≤ 11
    · exact Q.cotterill_le_11 d hd1 h11
    · by_cases h12 : d = 12
      · subst h12
        exact (Q.clemens_iff_smooth_and_singular 12).mpr ⟨Q.ballico_fontanari_12, hsing12⟩
      · exact hge13 d (by omega)

#print axioms clemens_iff_birational_tail

end ClemensConjecture
