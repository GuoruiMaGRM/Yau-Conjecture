import RequestProject.Yau.Appendix.Isolated
import RequestProject.Yau.Appendix.AnalyticMilnor

/-!
# The comparison `ℂ[x]/J ≅ ℂ{x}/Jℂ{x}`

For a weighted homogeneous polynomial with positive weights and an isolated critical
point at the origin, its polynomial and analytic Milnor algebras are naturally
isomorphic as `ℂ`-algebras, as in Lemma A.1.
-/

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- A power of each variable belongs to the Jacobian ideal. -/
lemma exists_pow_X_mem_jacobianIdeal (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (h : HasIsolatedCriticalPoint f) (j : Fin n) :
    ∃ N : ℕ, (MvPolynomial.X j : Poly n) ^ N ∈ jacobianIdeal f :=
  exists_pow_X_mem_jac (critical_eq_zero_of_isolated hw hf h.2) j

/-- Lemma A.1: the polynomial and analytic Milnor algebras are isomorphic as `ℂ`-algebras. -/
def milnorAlgebraEquivAnalytic (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (h : HasIsolatedCriticalPoint f) :
    MilnorAlgebra f ≃ₐ[ℂ] ConvSeries n ⧸ convIdeal (jacobianIdeal f) :=
  quotientEquivConv (exists_pow_X_mem_jacobianIdeal hw hf h)

/-- The isomorphism is induced by the inclusion `ℂ[x] → ℂ{x}`. -/
theorem milnorAlgebraEquivAnalytic_mk (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (h : HasIsolatedCriticalPoint f) (p : Poly n) :
    milnorAlgebraEquivAnalytic hw hf h (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (polyToConv p) :=
  rfl

/-- If the Milnor algebra is finite dimensional, a power of each variable belongs to `J`. -/
lemma exists_pow_X_mem_jac_of_iso (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (j : Fin n) :
    ∃ N : ℕ, (MvPolynomial.X j : Poly n) ^ N ∈ jacobianIdeal f := by
  by_cases hJ : jacobianIdeal f = ⊤
  · exact ⟨0, by rw [hJ]; exact Submodule.mem_top⟩
  · exact exists_pow_X_mem_jacobianIdeal hw hf
      (hasIsolatedCriticalPoint_of_isIsolatedSingularity hw hf hiso hJ) j

end Yau
