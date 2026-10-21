import RequestProject.Yau.Basic.Setup

/-! # Lifting homogeneous derivations of negative degree: Lemma B.3 -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma mk_mem_gradedPiece {p : Poly n} {m : ℕ} (hp : p.IsWeightedHomogeneous w m) :
    Ideal.Quotient.mk (jacobianIdeal f) p ∈ gradedPiece w f m := by
  rw [gradedPiece, if_pos (by positivity)]
  exact ⟨p, by simpa using hp, rfl⟩

lemma mem_gradedPiece_neg {a : MilnorAlgebra f} {m : ℤ} (hm : m < 0)
    (ha : a ∈ gradedPiece w f m) : a = 0 := by
  rw [gradedPiece, if_neg (by omega)] at ha
  simpa using ha

lemma mem_gradedPiece_nat {a : MilnorAlgebra f} {m : ℕ}
    (ha : a ∈ gradedPiece w f m) : ∃ p : Poly n, p.IsWeightedHomogeneous w m ∧
      Ideal.Quotient.mk (jacobianIdeal f) p = a := by
  rw [gradedPiece, if_pos (by positivity)] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact ⟨p, by simpa using hp, rfl⟩

/-- Every degree-`-s` derivation of the Milnor algebra lifts to a polynomial derivation `D = ∑ h_j ∂_j`, with `h_j` homogeneous of degree `w_j-s`. -/
lemma lift_of_deg {s : ℕ}
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f (-(s : ℤ)) δ) :
    ∃ h : Fin n → Poly n, IsNegHomog w s h ∧
      ∀ p, Ideal.Quotient.mk (jacobianIdeal f) (polyDer h p) =
        δ (Ideal.Quotient.mk (jacobianIdeal f) p) := by
  have key : ∀ i, ∃ hi : Poly n, hi.IsWeightedHomogeneous w (w i - s) ∧ (w i < s → hi = 0) ∧
      Ideal.Quotient.mk (jacobianIdeal f) hi =
        δ (Ideal.Quotient.mk (jacobianIdeal f) (X i)) := by
    intro i
    have hmem := hδ (w i) _ (mk_mem_gradedPiece (isWeightedHomogeneous_X ℂ w i))
    by_cases hi : w i < s
    · refine ⟨0, isWeightedHomogeneous_zero _ _ _, fun _ => rfl, ?_⟩
      rw [map_zero, mem_gradedPiece_neg (by omega) hmem]
    · rw [show ((w i : ℕ) : ℤ) + -(s : ℤ) = ((w i - s : ℕ) : ℤ) by omega] at hmem
      obtain ⟨p, hp, hpe⟩ := mem_gradedPiece_nat hmem
      exact ⟨p, hp, fun h => absurd h hi, hpe⟩
  choose h hh1 hh2 hh3 using key
  refine ⟨h, fun j => ⟨hh1 j, hh2 j⟩, fun p => ?_⟩
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [derivation_C, map_zero]
    rw [show Ideal.Quotient.mk (jacobianIdeal f) (C a) =
      algebraMap ℂ (MilnorAlgebra f) a from rfl, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    rw [Derivation.leibniz, map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, hp, mkDerivation_X, hh3 k, smul_eq_mul, smul_eq_mul]

end Yau
