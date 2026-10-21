import RequestProject.Yau.Sec4_Proof.Core

/-!
# Transfer through graded isomorphisms of Milnor algebras

A weight-preserving homomorphism that is surjective on homogeneous components
and identifies the Jacobian ideals induces a graded isomorphism of Milnor algebras.
Such an isomorphism transports homogeneous derivations and finite dimensionality.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {m n : ℕ}

/-- The Milnor algebra has no nonzero negative-degree derivation. -/
def NoNegDer (w : Fin n → ℕ) (f : Poly n) : Prop :=
  ∀ k : ℤ, k < 0 → ∀ δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f),
    IsDerivationOfDegree w f k δ → δ = 0

/-- Conjugate a derivation by an algebra isomorphism. -/
def conjDer {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) (δ : Derivation ℂ A A) : Derivation ℂ B B :=
  Derivation.mk' (e.toLinearMap ∘ₗ δ.toLinearMap ∘ₗ e.symm.toLinearMap) (by
    intro a b
    show e (δ (e.symm (a * b))) = a • e (δ (e.symm b)) + b • e (δ (e.symm a))
    rw [map_mul, δ.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, AlgEquiv.apply_symm_apply])

lemma conjDer_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) (δ : Derivation ℂ A A) (b : B) : conjDer e δ b = e (δ (e.symm b)) := rfl

/-- The conclusion is immediate if the Milnor algebra is the zero ring. -/
lemma noNegDer_of_jac_eq_top {w : Fin n → ℕ} {f : Poly n} (h : jacobianIdeal f = ⊤) :
    NoNegDer w f := by
  intro k _ δ _
  haveI : Subsingleton (MilnorAlgebra f) := Ideal.Quotient.subsingleton_iff.mpr h
  ext a; exact Subsingleton.elim _ _

section transfer

variable {w : Fin m → ℕ} {w' : Fin n → ℕ} {f : Poly m} {g : Poly n}
  (ψ : Poly m →ₐ[ℂ] Poly n)
  (h1 : ∀ p e, p.IsWeightedHomogeneous w e → (ψ p).IsWeightedHomogeneous w' e)
  (h2 : ∀ q e, q.IsWeightedHomogeneous w' e → ∃ p, p.IsWeightedHomogeneous w e ∧ ψ p = q)
  (h3 : ∀ p, ψ p ∈ jacobianIdeal g ↔ p ∈ jacobianIdeal f)

include h2 in
lemma surj_of_homog_surj : Function.Surjective ψ := by
  intro q
  have : q ∈ LinearMap.range ψ.toLinearMap := by
    rw [q.as_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    obtain ⟨p, -, hp⟩ := h2 (monomial μ (coeff μ q)) (Finsupp.weight w' μ)
      (isWeightedHomogeneous_monomial _ _ _ rfl)
    exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := this
  exact ⟨p, hp⟩

include h2 h3 in
/-- The induced isomorphism of Milnor algebras. -/
lemma exists_milnor_equiv : ∃ e : MilnorAlgebra f ≃ₐ[ℂ] MilnorAlgebra g,
    ∀ p, e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (ψ p) := by
  have hs : Function.Surjective ((Ideal.Quotient.mkₐ ℂ (jacobianIdeal g)).comp ψ) :=
    (Ideal.Quotient.mkₐ_surjective ℂ _).comp (surj_of_homog_surj ψ h2)
  have hker : RingHom.ker ((Ideal.Quotient.mkₐ ℂ (jacobianIdeal g)).comp ψ) =
      jacobianIdeal f := by
    ext p
    rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, h3]
  refine ⟨(Ideal.quotientEquivAlgOfEq ℂ hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hs), fun p => ?_⟩
  rfl

include h2 h3 in
lemma isolated_transfer : IsIsolatedSingularity f ↔ IsIsolatedSingularity g := by
  obtain ⟨e, -⟩ := exists_milnor_equiv ψ h2 h3
  constructor
  · intro h; haveI : Module.Finite ℂ (MilnorAlgebra f) := h
    exact Module.Finite.equiv e.toLinearEquiv
  · intro h; haveI : Module.Finite ℂ (MilnorAlgebra g) := h
    exact Module.Finite.equiv e.symm.toLinearEquiv

include h1 h2 h3 in
lemma noNegDer_transfer : NoNegDer w' g → NoNegDer w f := by
  intro H k hk δ hδ
  obtain ⟨e, he⟩ := exists_milnor_equiv ψ h2 h3
  have hdeg : IsDerivationOfDegree w' g k (conjDer e δ) := by
    intro j b hb
    obtain ⟨q, hq, rfl⟩ := mem_gradedPiece_nat hb
    obtain ⟨p, hp, rfl⟩ := h2 q j hq
    rw [conjDer_apply, ← he, AlgEquiv.symm_apply_apply]
    have := hδ j _ (mk_mem_gradedPiece hp)
    by_cases hjk : (j : ℤ) + k < 0
    · rw [mem_gradedPiece_neg hjk this, map_zero]; exact Submodule.zero_mem _
    · have hjk' : (j : ℤ) + k = ((j + k).toNat : ℕ) := by omega
      rw [hjk'] at this ⊢
      obtain ⟨p', hp', hp'e⟩ := mem_gradedPiece_nat this
      rw [← hp'e, he]
      exact mk_mem_gradedPiece (h1 _ _ hp')
  have h0 := H k hk _ hdeg
  ext a
  have := congrArg (fun D : Derivation ℂ _ _ => e.symm (D (e a))) h0
  simpa [conjDer_apply] using this

end transfer

end Yau
