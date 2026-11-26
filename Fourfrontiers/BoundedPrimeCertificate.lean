/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

namespace P2Q

/-- The cubic polynomial f(p) = p³ - p² - 12 arising from the p²q reduction. -/
def fCubic (p : ℕ) : ℕ := p ^ 3 - p ^ 2 - 12

/-- Computable trial-division check: returns true iff n is NOT of the form r² * s
    for any distinct primes r ≠ s. -/
def isNotP2Q (n : ℕ) : Bool :=
  if n ≤ 1 then true
  else
    let limit := Nat.sqrt n
    (List.range (limit + 1)).all fun r =>
      if r < 2 then true
      else if r * r ∣ n then
        let s := n / (r * r)
        if r * r * s == n ∧ r ≠ s ∧ Nat.Prime r ∧ Nat.Prime s then false
        else true
      else true

/-- Concrete computable predicate P₂ p: fCubic p avoids the p²q factorization. -/
def P2 (p : ℕ) : Prop :=
  isNotP2Q (fCubic p) = true

instance (p : ℕ) : Decidable (P2 p) :=
  inferInstanceAs (Decidable (isNotP2Q (fCubic p) = true))

/-- Concrete computable predicate P₃ p. -/
def P3 (p : ℕ) : Prop :=
  p % 4 = 3 → isNotP2Q (fCubic p) = true

instance (p : ℕ) : Decidable (P3 p) :=
  inferInstanceAs (Decidable (p % 4 = 3 → isNotP2Q (fCubic p) = true))

structure BoundedPrimeCertificate (Pred2 Pred3 : ℕ → Prop) (B : ℕ) where
  cert2 : ∀ p < B, Nat.Prime p → Pred2 p
  cert3 : ∀ p < B, Nat.Prime p → Pred3 p

def checkAllPrimesBelow (B : ℕ) : Bool :=
  (List.range B).all fun p =>
    if Nat.Prime p then
      isNotP2Q (fCubic p) && (decide (p % 4 ≠ 3) || isNotP2Q (fCubic p))
    else true

theorem bounded_certificate_of_check {B : ℕ} (h : checkAllPrimesBelow B = true) :
    BoundedPrimeCertificate P2 P3 B := by
  unfold checkAllPrimesBelow at h
  rw [List.all_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro p hpB hpPrime
    have hstep := h p (List.mem_range.mpr hpB)
    simp only [hpPrime, ↓reduceIte, Bool.and_eq_true] at hstep
    exact hstep.1
  · intro p hpB hpPrime _
    have hstep := h p (List.mem_range.mpr hpB)
    simp only [hpPrime, ↓reduceIte, Bool.and_eq_true] at hstep
    exact hstep.1

theorem cert_below_100 : BoundedPrimeCertificate P2 P3 100 :=
  bounded_certificate_of_check (by decide)

#print axioms cert_below_100

end P2Q
