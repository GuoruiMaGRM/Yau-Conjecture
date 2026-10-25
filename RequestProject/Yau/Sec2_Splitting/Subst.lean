import RequestProject.Yau.Sec2_Splitting.Transfer

/-! # Weight-preserving substitutions and the chain rule -/

open MvPolynomial

noncomputable section

namespace Yau

variable {m n : ℕ}

/-- The chain rule for polynomial substitution. -/
lemma pderiv_aeval (φ : Fin m → Poly n) (p : Poly m) (i : Fin n) :
    pderiv i (aeval φ p) = ∑ j, aeval φ (pderiv j p) * pderiv i (φ j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    rw [map_mul, aeval_X, Derivation.leibniz, hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Pi.single_apply]
    simp only [apply_ite (aeval φ), map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring

/-- The Jacobian ideal after substitution is contained in the image of the original Jacobian ideal. -/
lemma jac_aeval_le (φ : Fin m → Poly n) (f : Poly m) :
    jacobianIdeal (aeval φ f) ≤ (jacobianIdeal f).map (aeval φ) := by
  rw [jacobianIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe]
  rw [pderiv_aeval]
  refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)

/-- Weight-preserving substitution preserves weighted homogeneity. -/
lemma aeval_isWH {w : Fin m → ℕ} {w' : Fin n → ℕ} {φ : Fin m → Poly n}
    (hφ : ∀ j, (φ j).IsWeightedHomogeneous w' (w j)) {p : Poly m} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) : (aeval φ p).IsWeightedHomogeneous w' e := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp [isWeightedHomogeneous_zero]
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial μ r hr =>
    rw [aeval_monomial, Finsupp.prod]
    have h := IsWeightedHomogeneous.prod μ.support (fun i => φ i ^ μ i) (fun i => μ i * w i)
      (w := w') (fun i _ => by simpa using (hφ i).pow (μ i))
    have hc : (algebraMap ℂ (Poly n) r).IsWeightedHomogeneous w' 0 := by
      rw [MvPolynomial.algebraMap_eq]; exact isWeightedHomogeneous_C _ _
    have := hc.mul h
    convert this using 1
    rw [zero_add, ← hr, Finsupp.weight_apply, Finsupp.sum]
    simp [mul_comm]

lemma algHom_isWH {w : Fin m → ℕ} {w' : Fin n → ℕ} (E : Poly m →ₐ[ℂ] Poly n)
    (hE : ∀ j, (E (X j)).IsWeightedHomogeneous w' (w j)) {p : Poly m} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) : (E p).IsWeightedHomogeneous w' e := by
  rw [aeval_unique E]; exact aeval_isWH hE hp

/-- Transformation of the Jacobian ideal under an algebra automorphism. -/
lemma mem_jac_equiv_iff (E : Poly n ≃ₐ[ℂ] Poly n) (f p : Poly n) :
    E p ∈ jacobianIdeal (E f) ↔ p ∈ jacobianIdeal f := by
  have hE : ∀ (F : Poly n ≃ₐ[ℂ] Poly n) (g : Poly n),
      jacobianIdeal (F g) ≤ (jacobianIdeal g).map (F : Poly n →+* Poly n) := by
    intro F g
    have := jac_aeval_le (⇑(F : Poly n →ₐ[ℂ] Poly n) ∘ X) g
    rw [← aeval_unique] at this
    exact this
  have hinv : ∀ (F : Poly n ≃ₐ[ℂ] Poly n) (I : Ideal (Poly n)),
      I.map (F : Poly n →+* Poly n) ≤ I.comap (F.symm : Poly n →+* Poly n) :=
    fun F I => Ideal.map_le_comap_of_inverse _ _ I (fun x => by simp)
  constructor
  · intro h
    have := hinv E _ (hE E f h)
    simpa using this
  · intro h
    have h' := hE E.symm (E f)
    rw [E.symm_apply_apply] at h'
    have := hinv E.symm _ (h' h)
    simpa using this

section auto

variable {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- Transfer along a weight-preserving automorphism `E`. -/
lemma auto_transfer (E : Poly n ≃ₐ[ℂ] Poly n)
    (hE : ∀ j, (E (X j)).IsWeightedHomogeneous w (w j))
    (hE' : ∀ j, (E.symm (X j)).IsWeightedHomogeneous w (w j)) :
    (IsIsolatedSingularity f ↔ IsIsolatedSingularity (E f)) ∧
      (NoNegDer w (E f) → NoNegDer w f) := by
  have h1 : ∀ p e, p.IsWeightedHomogeneous w e → (E p).IsWeightedHomogeneous w e :=
    fun p e hp => algHom_isWH (E : Poly n →ₐ[ℂ] Poly n) hE hp
  have h2 : ∀ q e, q.IsWeightedHomogeneous w e →
      ∃ p, p.IsWeightedHomogeneous w e ∧ (E : Poly n →ₐ[ℂ] Poly n) p = q :=
    fun q e hq => ⟨E.symm q, algHom_isWH (E.symm : Poly n →ₐ[ℂ] Poly n) hE' hq, by simp⟩
  have h3 : ∀ p, (E : Poly n →ₐ[ℂ] Poly n) p ∈ jacobianIdeal (E f) ↔ p ∈ jacobianIdeal f :=
    fun p => mem_jac_equiv_iff E f p
  exact ⟨isolated_transfer _ h2 h3, noNegDer_transfer _ h1 h2 h3⟩

end auto

end Yau
