import Mathlib

/-!
# The convergent power series ring `ℂ{x₁,…,xₙ}`

A formal power series converges near the origin exactly when its coefficients
have a geometric bound `‖c_α‖ ≤ C R^{|α|}`. This coefficient characterization
defines the analytic local ring as a `ℂ`-subalgebra of `ℂ[[x]]`.
-/

open MvPowerSeries

noncomputable section

namespace Yau

variable {n : ℕ}

/-- A geometric coefficient bound `‖c_α‖ ≤ C R^{|α|}`, expressing a positive radius of convergence. -/
def IsConvergent (F : MvPowerSeries (Fin n) ℂ) : Prop :=
  ∃ C R : ℝ, 0 ≤ R ∧ ∀ α : Fin n →₀ ℕ, ‖coeff α F‖ ≤ C * R ^ α.degree

lemma IsConvergent.nonneg_const {F : MvPowerSeries (Fin n) ℂ} {C R : ℝ}
    (h : ∀ α : Fin n →₀ ℕ, ‖coeff α F‖ ≤ C * R ^ α.degree) : 0 ≤ C := by
  have := h 0
  simp only [map_zero, pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

/-- The number of decompositions `β+γ=α` is at most `2^{|α|}`. -/
lemma card_antidiagonal_le (α : Fin n →₀ ℕ) :
    ((Finset.antidiagonal α).card : ℝ) ≤ 2 ^ α.degree := by
  classical
  have h1 : (Finset.antidiagonal α).card ≤ (Finset.Iic α).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_antidiagonal] at hp
      rw [Finset.mem_coe, Finset.mem_Iic]
      rw [← hp]; exact le_self_add
    · intro p hp q hq h
      rw [Finset.mem_coe, Finset.mem_antidiagonal] at hp hq
      ext1
      · exact h
      · rw [← hp, h] at hq; exact (add_left_cancel hq).symm
  have h2 : (Finset.Iic α).card ≤ 2 ^ α.degree := by
    rw [Finsupp.card_Iic, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod'
    intro i _
    simp only [Nat.card_Iic]
    exact Nat.lt_two_pow_self
  exact_mod_cast h1.trans h2

lemma isConvergent_mul {F G : MvPowerSeries (Fin n) ℂ} (hF : IsConvergent F)
    (hG : IsConvergent G) : IsConvergent (F * G) := by
  classical
  obtain ⟨C₁, R₁, hR₁, h₁⟩ := hF
  obtain ⟨C₂, R₂, hR₂, h₂⟩ := hG
  have hC₁ := IsConvergent.nonneg_const h₁
  have hC₂ := IsConvergent.nonneg_const h₂
  set R := max R₁ R₂
  have hR : 0 ≤ R := le_max_of_le_left hR₁
  refine ⟨C₁ * C₂, 2 * R, by positivity, fun α => ?_⟩
  rw [coeff_mul]
  calc ‖∑ p ∈ Finset.antidiagonal α, coeff p.1 F * coeff p.2 G‖
      ≤ ∑ p ∈ Finset.antidiagonal α, ‖coeff p.1 F * coeff p.2 G‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal α, C₁ * C₂ * R ^ α.degree := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        rw [norm_mul, ← hp, map_add, pow_add]
        calc ‖coeff p.1 F‖ * ‖coeff p.2 G‖ ≤ (C₁ * R₁ ^ p.1.degree) * (C₂ * R₂ ^ p.2.degree) :=
              mul_le_mul (h₁ _) (h₂ _) (norm_nonneg _)
                (by have := h₁ p.1; linarith [norm_nonneg (coeff p.1 F)])
          _ ≤ (C₁ * R ^ p.1.degree) * (C₂ * R ^ p.2.degree) := by
              gcongr
              · exact le_max_left _ _
              · exact le_max_right _ _
          _ = _ := by ring
    _ = (Finset.antidiagonal α).card * (C₁ * C₂ * R ^ α.degree) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ α.degree * (C₁ * C₂ * R ^ α.degree) := by
        gcongr; exact card_antidiagonal_le α
    _ = C₁ * C₂ * (2 * R) ^ α.degree := by ring

lemma isConvergent_add {F G : MvPowerSeries (Fin n) ℂ} (hF : IsConvergent F)
    (hG : IsConvergent G) : IsConvergent (F + G) := by
  obtain ⟨C₁, R₁, hR₁, h₁⟩ := hF
  obtain ⟨C₂, R₂, hR₂, h₂⟩ := hG
  have hC₁ := IsConvergent.nonneg_const h₁
  have hC₂ := IsConvergent.nonneg_const h₂
  refine ⟨C₁ + C₂, max R₁ R₂, le_max_of_le_left hR₁, fun α => ?_⟩
  rw [map_add]
  calc ‖coeff α F + coeff α G‖ ≤ ‖coeff α F‖ + ‖coeff α G‖ := norm_add_le _ _
    _ ≤ C₁ * R₁ ^ α.degree + C₂ * R₂ ^ α.degree := add_le_add (h₁ α) (h₂ α)
    _ ≤ C₁ * (max R₁ R₂) ^ α.degree + C₂ * (max R₁ R₂) ^ α.degree := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = _ := by ring

lemma isConvergent_C (a : ℂ) : IsConvergent (C a : MvPowerSeries (Fin n) ℂ) := by
  classical
  refine ⟨‖a‖, 1, zero_le_one, fun α => ?_⟩
  rw [one_pow, mul_one, coeff_C]
  split_ifs <;> simp

/-- The convergent power series ring `𝒪 = ℂ{x₁,…,xₙ}`. -/
def ConvSeries (n : ℕ) : Subalgebra ℂ (MvPowerSeries (Fin n) ℂ) where
  carrier := {F | IsConvergent F}
  mul_mem' := isConvergent_mul
  add_mem' := isConvergent_add
  algebraMap_mem' a := by
    simpa [MvPowerSeries.algebraMap_apply'] using isConvergent_C (n := n) a

/-- Polynomials are convergent power series. -/
lemma isConvergent_coe (p : MvPolynomial (Fin n) ℂ) : IsConvergent (p : MvPowerSeries (Fin n) ℂ) := by
  classical
  refine ⟨∑ β ∈ p.support, ‖p.coeff β‖, 1, zero_le_one, fun α => ?_⟩
  rw [one_pow, mul_one, MvPolynomial.coeff_coe]
  by_cases h : α ∈ p.support
  · exact Finset.single_le_sum (f := fun β => ‖p.coeff β‖) (fun _ _ => norm_nonneg _) h
  · rw [MvPolynomial.notMem_support_iff.mp h, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The inclusion `ℂ[x] → ℂ{x}`. -/
def polyToConv : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ConvSeries n :=
  (MvPolynomial.coeToMvPowerSeries.algHom ℂ).codRestrict (ConvSeries n)
    (fun p => isConvergent_coe p)

@[simp] lemma polyToConv_coe (p : MvPolynomial (Fin n) ℂ) :
    ((polyToConv p : ConvSeries n) : MvPowerSeries (Fin n) ℂ) = p := by
  rfl

end Yau
