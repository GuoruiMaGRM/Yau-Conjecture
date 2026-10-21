import RequestProject.Yau.Appendix.Isolated

/-!
# Rational weights

The paper permits positive rational weights and reduces them to integer weights by
multiplying by a common positive integer. This file formalizes that reduction,
including rationally indexed homogeneous components and degrees of derivations.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The degree-`m` component of the Milnor algebra for rational weights `w` and `m ∈ ℚ`. -/
def gradedPieceRat (w : Fin n → ℚ) (f : Poly n) (m : ℚ) : Submodule ℂ (MilnorAlgebra f) :=
  (weightedHomogeneousSubmodule ℂ w m).map (Ideal.Quotient.mkₐ ℂ (jacobianIdeal f)).toLinearMap

/-- A derivation has rational degree `k` if it sends `A_j` to `A_{j+k}` for every rational `j`. -/
def IsDerivationOfDegreeRat (w : Fin n → ℚ) (f : Poly n) (k : ℚ)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f)) : Prop :=
  ∀ j : ℚ, ∀ a ∈ gradedPieceRat w f j, δ a ∈ gradedPieceRat w f (j + k)

lemma weight_cast_of_scaled {w : Fin n → ℚ} {w' : Fin n → ℕ} {N : ℕ}
    (hW : ∀ i, (w' i : ℚ) = N * w i) (μ : Fin n →₀ ℕ) :
    ((Finsupp.weight w' μ : ℕ) : ℚ) = N * Finsupp.weight w μ := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum, hW, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma exists_int_of_den_dvd {q : ℚ} {N : ℕ} (h : q.den ∣ N) : ∃ z : ℤ, (z : ℚ) = N * q := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * q.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]; ring

/-- Clearing denominators: one positive integer makes all the weights and `k` integral. -/
lemma exists_clearing (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) (k : ℚ) :
    ∃ N : ℕ, 0 < N ∧ (∃ w' : Fin n → ℕ, (∀ i, 0 < w' i) ∧ ∀ i, (w' i : ℚ) = N * w i) ∧
      ∃ k' : ℤ, (k' : ℚ) = N * k := by
  set N : ℕ := k.den * ∏ i, (w i).den
  have hN : 0 < N := Nat.mul_pos k.den_pos (Finset.prod_pos fun i _ => (w i).den_pos)
  have hdvd : ∀ i, (w i).den ∣ N := fun i =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  choose z hz using fun i => exists_int_of_den_dvd (hdvd i)
  have hzpos : ∀ i, 0 < z i := fun i => by
    have : (0 : ℚ) < z i := by rw [hz i]; exact mul_pos (by exact_mod_cast hN) (hw i)
    exact_mod_cast this
  refine ⟨N, hN, ⟨fun i => (z i).toNat, fun i => show 0 < (z i).toNat by have := hzpos i; omega, fun i => ?_⟩,
    exists_int_of_den_dvd (Dvd.intro _ rfl)⟩
  rw [← hz i]
  have : (((z i).toNat : ℤ) : ℚ) = (z i : ℚ) := by rw [Int.toNat_of_nonneg (hzpos i).le]
  exact_mod_cast this

lemma isWH_nat_of_rat {w : Fin n → ℚ} {w' : Fin n → ℕ} {N : ℕ}
    (hW : ∀ i, (w' i : ℚ) = N * w i) {p : Poly n} {m : ℚ} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w m) (he : (e : ℚ) = N * m) :
    p.IsWeightedHomogeneous w' e := fun μ hμ => by
  have h1 := weight_cast_of_scaled hW μ
  rw [hp hμ, ← he] at h1
  exact_mod_cast h1

lemma isWH_rat_of_nat {w : Fin n → ℚ} {w' : Fin n → ℕ} {N : ℕ} (hN : 0 < N)
    (hW : ∀ i, (w' i : ℚ) = N * w i) {p : Poly n} {m : ℚ} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w' e) (he : (e : ℚ) = N * m) :
    p.IsWeightedHomogeneous w m := fun μ hμ => by
  have h1 := weight_cast_of_scaled hW μ
  rw [hp hμ, he] at h1
  exact (mul_left_cancel₀ (by exact_mod_cast hN.ne') h1).symm

/-- With nonnegative weights, a weighted homogeneous polynomial of negative degree is zero. -/
lemma eq_zero_of_isWH_neg {w : Fin n → ℚ} (hw : ∀ i, 0 ≤ w i) {p : Poly n} {m : ℚ}
    (hp : p.IsWeightedHomogeneous w m) (hm : m < 0) : p = 0 := by
  ext μ
  by_contra h
  have h1 := hp h
  have h2 : 0 ≤ Finsupp.weight w μ := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun i _ => smul_nonneg (Nat.zero_le _) (hw i)
  linarith

/-- The main theorem for positive rational weights, under `VarchenkoHypothesis`. Clearing denominators preserves the sign of the derivation degree. -/
theorem yau_conjecture_rat (hV : VarchenkoHypothesis) (w : Fin n → ℚ) (d : ℚ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℚ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegreeRat w f k δ) : δ = 0 := by
  obtain ⟨N, hN, ⟨w', hw', hW⟩, k', hk'⟩ := exists_clearing w hw k
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hk'neg : k' < 0 := by
    have : (k' : ℚ) < 0 := by rw [hk']; exact mul_neg_of_pos_of_neg hNq hk
    exact_mod_cast this
  obtain ⟨d', hf'⟩ : ∃ d' : ℕ, f.IsWeightedHomogeneous w' d' := by
    by_cases hf0 : f = 0
    · exact ⟨0, hf0 ▸ isWeightedHomogeneous_zero _ _ _⟩
    · obtain ⟨μ, hμ⟩ : ∃ μ, μ ∈ f.support := by
        by_contra h; push_neg at h
        exact hf0 (by ext μ; simpa using h μ)
      refine ⟨Finsupp.weight w' μ, isWH_nat_of_rat hW hf ?_⟩
      rw [weight_cast_of_scaled hW μ, hf (mem_support_iff.mp hμ)]
  have hiso := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw' hf' hcrit
  refine yau_conjecture hV w' d' f hw' hf' hiso k' hk'neg δ ?_
  intro j a ha
  simp only [gradedPiece, Nat.cast_nonneg, if_true, Int.toNat_natCast] at ha
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
  have hpQ : p ∈ weightedHomogeneousSubmodule ℂ w ((j : ℚ) / N) := by
    rw [mem_weightedHomogeneousSubmodule]
    exact isWH_rat_of_nat hN hW hp (by field_simp)
  obtain ⟨q, hq, hqeq⟩ := Submodule.mem_map.mp (hδ _ _ (Submodule.mem_map_of_mem hpQ))
  rw [← hqeq]
  rw [mem_weightedHomogeneousSubmodule] at hq
  have hdeg : ((j : ℤ) + k' : ℚ) = N * ((j : ℚ) / N + k) := by
    push_cast; rw [mul_add, hk']; field_simp
  by_cases h : 0 ≤ (j : ℤ) + k'
  · rw [gradedPiece, if_pos h]
    refine Submodule.mem_map_of_mem ?_
    rw [mem_weightedHomogeneousSubmodule]
    refine isWH_nat_of_rat hW hq ?_
    rw [← hdeg]
    have : ((((j : ℤ) + k').toNat : ℤ) : ℚ) = ((j : ℤ) + k' : ℤ) := by
      rw [Int.toNat_of_nonneg h]
    exact_mod_cast this
  · have hneg : (j : ℚ) / N + k < 0 := by
      have : ((j : ℤ) + k' : ℚ) < 0 := by exact_mod_cast (not_le.mp h)
      rw [hdeg] at this
      by_contra hc
      exact absurd this (not_lt.mpr (mul_nonneg hNq.le (not_lt.mp hc)))
    rw [eq_zero_of_isWH_neg (fun i => (hw i).le) hq hneg]
    simp

end Yau
