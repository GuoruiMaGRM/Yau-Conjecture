import RequestProject.Yau.Appendix.AnalyticYau

/-!
# Euler's identity and the moduli algebra

Euler's identity gives `d f = ∑ w_i x_i ∂_i f`. For positive degree this identifies
the Tjurina algebra, also called the moduli algebra, with the Milnor algebra, both
for polynomials and for convergent power series. Lemma B.2 shows that derivations
of a finite-dimensional local `ℂ`-algebra preserve its maximal ideal.
Positive weights also imply that a weighted homogeneous power series is a polynomial.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ### Euler's identity and the moduli algebra -/

/-- Euler's identity for a weighted homogeneous polynomial of degree `d`. -/
theorem euler_identity {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) :
    (d : ℂ) • f = ∑ i, (w i : ℂ) • (X i * pderiv i f) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
    simp only [smul_add, ihp, ihq, map_add, mul_add, Finset.sum_add_distrib]
  | monomial μ r hr =>
    simp only [X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [← hr, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]

/-- A weighted homogeneous polynomial of positive degree belongs to its Jacobian ideal. -/
theorem mem_jacobianIdeal_self {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) : f ∈ jacobianIdeal f := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have key : (d : ℂ)⁻¹ • ∑ i, (w i : ℂ) • (X i * pderiv i f) ∈ jacobianIdeal f := by
    refine Submodule.smul_of_tower_mem _ _ (Ideal.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_of_tower_mem _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  rwa [← euler_identity hf, smul_smul, inv_mul_cancel₀ hd', one_smul] at key

/-- The ideal `(f,∂₁f,…,∂ₙf)` defining the Tjurina algebra. -/
def moduliIdeal (f : Poly n) : Ideal (Poly n) :=
  Ideal.span {f} ⊔ jacobianIdeal f

/-- The polynomial moduli algebra, or Tjurina algebra, `ℂ[x]/(f,J)`. -/
abbrev ModuliAlgebra (f : Poly n) := Poly n ⧸ moduliIdeal f

theorem moduliIdeal_eq_jacobianIdeal {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) : moduliIdeal f = jacobianIdeal f := by
  refine sup_eq_right.mpr ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact mem_jacobianIdeal_self hf hd

/-- For weighted homogeneous `f` of positive degree, the moduli algebra is the Milnor algebra. -/
def moduliAlgebraEquiv {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) : ModuliAlgebra f ≃ₐ[ℂ] MilnorAlgebra f :=
  Ideal.quotientEquivAlgOfEq ℂ (moduliIdeal_eq_jacobianIdeal hf hd)

/-- The same equality in the analytic local ring: `(f,J)ℂ{x} = Jℂ{x}`. -/
theorem convModuliIdeal_eq {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) :
    convIdeal (moduliIdeal f) = convIdeal (jacobianIdeal f) := by
  rw [moduliIdeal_eq_jacobianIdeal hf hd]

/-! ### Lemma B.2 -/

/-- Lemma B.2: every derivation of a finite-dimensional local `ℂ`-algebra preserves its maximal ideal. -/
theorem derivation_mem_maximalIdeal {B : Type*} [CommRing B] [Algebra ℂ B] [IsLocalRing B]
    [Module.Finite ℂ B] (D : Derivation ℂ B B) {a : B} (ha : a ∈ IsLocalRing.maximalIdeal B) :
    D a ∈ IsLocalRing.maximalIdeal B := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
  have hnil : IsNilpotent a := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    refine ⟨k, ?_⟩
    have : a ∈ (⊥ : Ideal B).jacobson := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have := Ideal.pow_mem_pow this k
    rw [hk] at this
    simpa using this
  classical
  have hex : ∃ N, a ^ N = 0 := hnil
  set N := Nat.find hex
  have hNa : a ^ N = 0 := Nat.find_spec hex
  by_contra hD
  have hu : IsUnit (D a) := by
    by_contra h; exact hD ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hN0 : N ≠ 0 := by
    intro h; rw [h, pow_zero] at hNa; exact one_ne_zero hNa
  have h1 : D (a ^ N) = 0 := by rw [hNa, map_zero]
  rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul] at h1
  have hNu : IsUnit ((N : B)) := by
    have : ((N : B)) = algebraMap ℂ B (N : ℂ) := by simp
    rw [this]; exact (IsUnit.mk0 _ (by exact_mod_cast hN0)).map _
  have : a ^ (N - 1) = 0 :=
    (hNu.mul hu).mul_left_eq_zero.mp (by rw [← h1]; ring)
  exact Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos) this

/-! ### Weighted homogeneous power series are polynomials -/

/-- A formal power series is weighted homogeneous of degree `d` if each monomial with nonzero coefficient has weight `d`. -/
def PowerSeriesIsWeightedHomogeneous (w : Fin n → ℕ) (F : MvPowerSeries (Fin n) ℂ) (d : ℕ) :
    Prop :=
  ∀ μ : Fin n →₀ ℕ, MvPowerSeries.coeff μ F ≠ 0 → Finsupp.weight w μ = d

/-- With positive weights, a weighted homogeneous power series is a weighted homogeneous polynomial. -/
theorem exists_poly_of_isWeightedHomogeneous {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    {F : MvPowerSeries (Fin n) ℂ} {d : ℕ} (hF : PowerSeriesIsWeightedHomogeneous w F d) :
    ∃ p : Poly n, (p : MvPowerSeries (Fin n) ℂ) = F ∧ p.IsWeightedHomogeneous w d := by
  classical
  have hS : {μ : Fin n →₀ ℕ | Finsupp.weight w μ = d}.Finite := by
    refine (Finsupp.finite_of_degree_le d).subset fun μ hμ => ?_
    simp only [Set.mem_setOf_eq] at hμ ⊢
    rw [← hμ, Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_le_sum fun i _ => by have := hw i; simp only [smul_eq_mul]; nlinarith
  refine ⟨∑ μ ∈ hS.toFinset, monomial μ (MvPowerSeries.coeff μ F), ?_, ?_⟩
  · ext ν
    rw [MvPolynomial.coeff_coe, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (by simpa using hF ν (Ne.symm hne))
  · exact IsWeightedHomogeneous.sum _ _ _ fun μ hμ =>
      isWeightedHomogeneous_monomial _ _ _ (by simpa using hμ)

/-! ### The main theorem for the moduli algebra -/

/-- The degree-`m` component of the moduli algebra; it is zero for `m < 0`. -/
def gradedPieceModuli (w : Fin n → ℕ) (f : Poly n) (m : ℤ) :
    Submodule ℂ (ModuliAlgebra f) :=
  if 0 ≤ m then
    (weightedHomogeneousSubmodule ℂ w m.toNat).map
      (Ideal.Quotient.mkₐ ℂ (moduliIdeal f)).toLinearMap
  else ⊥

/-- A derivation has degree `k` when it maps the degree-`j` component into the degree-`j+k` component. -/
def IsDerivationOfDegreeModuli (w : Fin n → ℕ) (f : Poly n) (k : ℤ)
    (δ : Derivation ℂ (ModuliAlgebra f) (ModuliAlgebra f)) : Prop :=
  ∀ j : ℕ, ∀ a ∈ gradedPieceModuli w f j, δ a ∈ gradedPieceModuli w f (j + k)

lemma moduliAlgebraEquiv_mk {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) (p : Poly n) :
    moduliAlgebraEquiv hf hd (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

lemma moduliAlgebraEquiv_symm_mk {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) (p : Poly n) :
    (moduliAlgebraEquiv hf hd).symm (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := by
  rw [AlgEquiv.symm_apply_eq]; rfl

lemma map_gradedPieceModuli {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) (m : ℤ) {a : ModuliAlgebra f}
    (ha : a ∈ gradedPieceModuli w f m) : moduliAlgebraEquiv hf hd a ∈ gradedPiece w f m := by
  unfold gradedPieceModuli at ha
  unfold gradedPiece
  split_ifs at ha ⊢ with hm
  · obtain ⟨p, hp, rfl⟩ := ha
    exact ⟨p, hp, rfl⟩
  · rw [Submodule.mem_bot] at ha ⊢
    rw [ha, map_zero]

lemma symm_map_gradedPiece {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d) (m : ℤ) {a : MilnorAlgebra f}
    (ha : a ∈ gradedPiece w f m) :
    (moduliAlgebraEquiv hf hd).symm a ∈ gradedPieceModuli w f m := by
  unfold gradedPieceModuli
  unfold gradedPiece at ha
  split_ifs at ha ⊢ with hm
  · obtain ⟨p, hp, rfl⟩ := ha
    exact ⟨p, hp, (moduliAlgebraEquiv_symm_mk hf hd p).symm⟩
  · rw [Submodule.mem_bot] at ha ⊢
    rw [ha, map_zero]

/-- The main theorem for the moduli algebra `ℂ[x]/(f,J)`, under the square-deformation input `VarchenkoHypothesis`. -/
theorem yau_conjecture_moduli (hV : VarchenkoHypothesis) {n : ℕ} (w : Fin n → ℕ)
    (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d) (hd : 0 < d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (ModuliAlgebra f) (ModuliAlgebra f))
    (hδ : IsDerivationOfDegreeModuli w f k δ) : δ = 0 := by
  set e := moduliAlgebraEquiv hf hd
  have h0 : conjDer e δ = 0 := by
    refine yau_conjecture_of_critical hV w d f hw hf hcrit k hk _ fun j a ha => ?_
    rw [conjDer_apply]
    exact map_gradedPieceModuli hf hd _ (hδ j _ (symm_map_gradedPiece hf hd _ ha))
  ext x
  have := congrArg (fun D => D (e x)) h0
  simp only [conjDer_apply, AlgEquiv.symm_apply_apply, Derivation.zero_apply] at this
  simpa using this

end Yau
