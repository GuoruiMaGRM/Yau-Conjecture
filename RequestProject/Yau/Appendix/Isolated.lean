import RequestProject.Yau.Sec4_Proof.MainTheorem

/-!
# Isolated critical points and finite-dimensional Milnor algebras

For a weighted homogeneous polynomial with positive weights, an isolated critical
point at the origin implies that the origin is the only critical point: weighted
scaling would bring any other critical point arbitrarily close to it.
The Nullstellensatz then gives `√J = (x₁,…,xₙ)` and a finite-dimensional quotient.
This proves the first part of Lemma A.1 and relates the analytic hypothesis of the
paper to the algebraic condition `IsIsolatedSingularity`.
-/

open MvPolynomial Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-- All first partial derivatives vanish at the origin and have no other common zero in a neighborhood of it. -/
def HasIsolatedCriticalPoint (f : Poly n) : Prop :=
  (∀ i, eval 0 (pderiv i f) = 0) ∧
    ∃ U ∈ 𝓝 (0 : Fin n → ℂ), ∀ x ∈ U, (∀ i, eval x (pderiv i f) = 0) → x = 0

variable {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- Weighted scaling brings any nonzero critical point arbitrarily close to the origin. Thus an isolated critical point at the origin is the only critical point. -/
lemma critical_eq_zero_of_isolated (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hU : ∃ U ∈ 𝓝 (0 : Fin n → ℂ), ∀ x ∈ U, (∀ i, eval x (pderiv i f) = 0) → x = 0)
    (x : Fin n → ℂ) (hx : ∀ i, eval x (pderiv i f) = 0) : x = 0 := by
  obtain ⟨U, hU0, hUc⟩ := hU
  by_contra hx0
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h; push_neg at h; exact hx0 (funext h)
  set φ : ℂ → (Fin n → ℂ) := fun t l => t ^ w l * x l
  have hφc : Continuous φ := by
    apply continuous_pi; intro l; fun_prop
  have hφ0 : φ 0 = 0 := by
    funext l; simp [φ, zero_pow (hw l).ne']
  have hpre : φ ⁻¹' U ∈ 𝓝 (0 : ℂ) := hφc.continuousAt.preimage_mem_nhds (by rwa [hφ0])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set t : ℂ := ((ε / 2 : ℝ) : ℂ)
  have ht0 : t ≠ 0 := by
    simp only [t, ne_eq, Complex.ofReal_eq_zero]; linarith
  have htU : φ t ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right]
    simp only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith)
  have hcrit : ∀ i, eval (φ t) (pderiv i f) = 0 := by
    intro i; rw [eval_scale (pderiv_isWH hf i).1, hx i, mul_zero]
  have := congrFun (hUc _ htU hcrit) j
  simp only [φ, Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', ne_eq] at this
  rcases this with ⟨h, _⟩ | h
  · exact ht0 h
  · exact hj h

/-- By the Nullstellensatz, if the origin is the only common zero of the partial derivatives, a power of every variable lies in the Jacobian ideal. -/
lemma exists_pow_X_mem_jac (hz : ∀ x : Fin n → ℂ, (∀ i, eval x (pderiv i f) = 0) → x = 0)
    (j : Fin n) : ∃ N : ℕ, X j ^ N ∈ jacobianIdeal f := by
  have hmem : (X j : Poly n) ∈ vanishingIdeal ℂ (zeroLocus ℂ (jacobianIdeal f)) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    have hx0 : x = 0 := hz x fun i => by
      have := hx (pderiv i f) (Ideal.subset_span ⟨i, rfl⟩)
      simpa using this
    subst hx0
    simp
  rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
  exact hmem

/-- If `I` contains a power of every variable, then `ℂ[x]/I` is finite dimensional. -/
lemma finite_quotient_of_pow_X_mem (I : Ideal (Poly n))
    (hI : ∀ j : Fin n, ∃ N : ℕ, X j ^ N ∈ I) : Module.Finite ℂ (Poly n ⧸ I) := by
  rw [Algebra.finite_iff_isIntegral_and_finiteType]
  refine ⟨?_, inferInstance⟩
  have hint : ∀ y ∈ Set.range (fun j => Ideal.Quotient.mkₐ ℂ I (X j)), IsIntegral ℂ y := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨N, hN⟩ := hI j
    refine ⟨Polynomial.X ^ N, Polynomial.monic_X_pow N, ?_⟩
    rw [Polynomial.eval₂_X_pow, ← map_pow, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hN
  have hadj : Algebra.adjoin ℂ (Set.range (fun j => Ideal.Quotient.mkₐ ℂ I (X j))) = ⊤ := by
    rw [show (fun j => Ideal.Quotient.mkₐ ℂ I (X j)) = (Ideal.Quotient.mkₐ ℂ I) ∘ X from rfl,
      Set.range_comp, ← AlgHom.map_adjoin, adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ I
  have hle : Algebra.adjoin ℂ (Set.range (fun j => Ideal.Quotient.mkₐ ℂ I (X j))) ≤
      integralClosure ℂ _ := Algebra.adjoin_le hint
  rw [hadj] at hle
  exact ⟨fun x => hle Algebra.mem_top⟩

/-- Lemma A.1: an isolated critical point gives a finite-dimensional Milnor algebra for positive weighted homogeneous polynomials. -/
theorem isIsolatedSingularity_of_hasIsolatedCriticalPoint (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (h : HasIsolatedCriticalPoint f) :
    IsIsolatedSingularity f :=
  finite_quotient_of_pow_X_mem _
    (exists_pow_X_mem_jac (critical_eq_zero_of_isolated hw hf h.2))

/-- Lemma A.1: the radical of the Jacobian ideal is the maximal ideal at the origin. -/
theorem radical_jacobianIdeal_eq_idealOfVars (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (h : HasIsolatedCriticalPoint f) :
    (jacobianIdeal f).radical = idealOfVars (Fin n) ℂ := by
  apply le_antisymm
  · intro p ⟨N, hN⟩
    have h0 : eval 0 (p ^ N) = 0 := mem_jac_eval_zero h.1 hN
    rw [map_pow] at h0
    replace h0 := eq_zero_of_pow_eq_zero h0
    rw [← pow_one (idealOfVars (Fin n) ℂ), mem_pow_idealOfVars_iff]
    intro x hx
    rw [Nat.one_le_iff_ne_zero]
    intro hdeg
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    subst hdeg
    rw [mem_support_iff, ← constantCoeff_eq, ← MvPolynomial.eval_zero] at hx
    exact hx h0
  · rw [idealOfVars, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact exists_pow_X_mem_jac (critical_eq_zero_of_isolated hw hf h.2) j

/-- Conversely, a finite-dimensional Milnor algebra and a proper Jacobian ideal imply an isolated critical point at the origin. -/
theorem hasIsolatedCriticalPoint_of_isIsolatedSingularity (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (hiso : IsIsolatedSingularity f)
    (hJ : jacobianIdeal f ≠ ⊤) : HasIsolatedCriticalPoint f := by
  refine ⟨fun i => ?_, Set.univ, Filter.univ_mem, fun x _ hx => common_zero_eq_zero hw hf hiso x hx⟩
  obtain ⟨hwh, hlt⟩ := pderiv_isWH hf i
  by_cases hdi : d < w i
  · rw [hlt hdi, map_zero]
  by_cases hpos : 0 < d - w i
  · exact eval_zero_of_isWH_pos hwh hpos
  · rw [show d - w i = 0 by omega] at hwh
    by_contra hc
    apply hJ
    rw [Ideal.eq_top_iff_one]
    have hmem : pderiv i f ∈ jacobianIdeal f := Ideal.subset_span ⟨i, rfl⟩
    rw [eq_C_of_isWH_zero hw hwh] at hmem
    have := Ideal.mul_mem_left _ (C (eval 0 (pderiv i f))⁻¹) hmem
    rwa [← map_mul, inv_mul_cancel₀ hc, map_one] at this

/-- For positive weighted homogeneous polynomials with proper Jacobian ideal, isolatedness at the origin is equivalent to finite dimensionality of the Milnor algebra. -/
theorem isIsolatedSingularity_iff_hasIsolatedCriticalPoint (hw : ∀ i, 0 < w i)
    (hf : f.IsWeightedHomogeneous w d) (hJ : jacobianIdeal f ≠ ⊤) :
    IsIsolatedSingularity f ↔ HasIsolatedCriticalPoint f :=
  ⟨fun h => hasIsolatedCriticalPoint_of_isIsolatedSingularity hw hf h hJ,
    isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf⟩

/-- The main theorem stated with the paper's isolated-critical-point hypothesis. -/
theorem yau_conjecture_of_critical (hV : VarchenkoHypothesis) {n : ℕ} (w : Fin n → ℕ)
    (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture hV w d f hw hf (isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit)
    k hk δ hδ

end Yau
