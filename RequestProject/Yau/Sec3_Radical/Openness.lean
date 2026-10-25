import RequestProject.Yau.Sec3_Radical.HilbertFunction

/-!
# Isolatedness under small homogeneous perturbations

Surjectivity between finite-dimensional vector spaces is open, by continuity
of determinants. Apply this to the maps `(b_j) ↦ ∑ b_j ∂_j g_s` on a sufficiently
large homogeneous component. Their surjectivity forces powers of all variables
into `J_{g_s}`, proving isolatedness for small `s`.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ}

/-- A surjective linear map remains surjective under a sufficiently small affine perturbation. -/
theorem eventually_surjective_affine {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [Module.Finite ℂ F] {μ : ℕ}
    (A : E →ₗ[ℂ] F) (hA : Function.Surjective A) (B : Fin μ → E →ₗ[ℂ] F) :
    ∃ ε > 0, ∀ s : Fin μ → ℂ, ‖s‖ < ε → Function.Surjective (A + ∑ k, s k • B k) := by
  classical
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective A (LinearMap.range_eq_top.2 hA)
  set b := Module.finBasis ℂ F
  set M : Fin μ → Matrix (Fin (Module.finrank ℂ F)) (Fin (Module.finrank ℂ F)) ℂ :=
    fun k => LinearMap.toMatrix b b (B k ∘ₗ R)
  have hcont : Continuous fun s : Fin μ → ℂ => (1 + ∑ k, s k • M k).det :=
    (continuous_const.add (continuous_finset_sum _ fun k _ =>
      (continuous_apply k).smul continuous_const)).matrix_det
  have h0 : (1 + ∑ k, (0 : Fin μ → ℂ) k • M k).det ≠ 0 := by simp
  have hev := hcont.continuousAt.eventually_ne h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hdet := hball (by simpa [dist_zero_right] using hs)
  set T := (A + ∑ k, s k • B k) ∘ₗ R
  have hT : T = LinearMap.id + ∑ k, s k • (B k ∘ₗ R) := by
    apply LinearMap.ext; intro x
    simp only [T, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [← LinearMap.comp_apply A R, hR, LinearMap.id_apply]
  have hTdet : LinearMap.det T ≠ 0 := by
    rw [← LinearMap.det_toMatrix b, hT, map_add, map_sum, LinearMap.toMatrix_id]
    simpa [map_smul, M] using hdet
  have hunit : IsUnit T := (LinearMap.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hTdet)
  intro y
  obtain ⟨x, hx⟩ := (Module.End.isUnit_iff T).1 hunit |>.2 y
  exact ⟨R x, hx⟩

/-- The map `∏_j S_{L-a_j} → S_L`, sending `(b_j)` to `∑ b_j ∂_j q`, for homogeneous `q`. -/
def jacMap (w : Fin n → ℕ) (d L : ℕ) (hdL : d ≤ L) (q : Poly n) (hq : q.IsWeightedHomogeneous w d) :
    ((j : Fin n) → gradedS w (L - (d - w j))) →ₗ[ℂ] gradedS w L where
  toFun b := ⟨∑ j, (b j : Poly n) * pderiv j q, Submodule.sum_mem _ fun j _ => by
    have := ((b j).2 : (b j : Poly n).IsWeightedHomogeneous w (L - (d - w j))).mul
      (pderiv_isWH hq j).1
    rwa [show L - (d - w j) + (d - w j) = L by omega] at this⟩
  map_add' b b' := by
    apply Subtype.ext; simp only [Pi.add_apply, Submodule.coe_add, add_mul, Finset.sum_add_distrib]
  map_smul' c b := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_mul_assoc, Finset.smul_sum]

lemma jacMap_apply (d L : ℕ) (hdL : d ≤ L) (q : Poly n) (hq : q.IsWeightedHomogeneous w d)
    (b : (j : Fin n) → gradedS w (L - (d - w j))) :
    (jacMap w d L hdL q hq b : Poly n) = ∑ j, (b j : Poly n) * pderiv j q := rfl

/-- Small degree-`d` homogeneous perturbations of `f` retain an isolated critical point: their Jacobian ideals contain all sufficiently high-weight monomials. -/
theorem eventually_highIdeal_le_jacobian (hw : ∀ i, 0 < w i) {d : ℕ} {f : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hwd : ∀ i, w i < d) {T₀ : ℕ}
    (hT₀ : highIdeal w T₀ ≤ jacobianIdeal f) {μ : ℕ} (φ : Fin μ → Poly n)
    (hφ : ∀ k, (φ k).IsWeightedHomogeneous w d) :
    ∃ ε > 0, ∀ s : Fin μ → ℂ, ‖s‖ < ε →
      ∃ T, highIdeal w T ≤ jacobianIdeal (f + ∑ k, C (s k) * φ k) := by
  classical
  set L := (T₀ + d) * ∏ i, w i with hL
  have hprod : 1 ≤ ∏ i, w i := Finset.one_le_prod' fun i _ => hw i
  have hLge : T₀ + d ≤ L := by rw [hL]; exact Nat.le_mul_of_pos_right _ hprod
  have hdL : d ≤ L := by omega
  have hdvd : ∀ i, w i ∣ L := fun i =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  haveI : ∀ j : Fin n, Module.Finite ℂ (gradedS w (L - (d - w j))) := fun j => finite_gradedS hw _
  haveI : Module.Finite ℂ (gradedS w L) := finite_gradedS hw L
  -- The map is surjective at `s=0`.
  have hsurj : Function.Surjective (jacMap w d L hdL f hf) := by
    intro y
    have hyJ : (y : Poly n) ∈ jacobianIdeal f := hT₀ (isWH_mem_highIdeal y.2 (by omega))
    obtain ⟨h, hh, -, hsum⟩ := jacobian_homog_decomp hf hyJ y.2 (fun i => (hwd i).le)
    refine ⟨fun j => ⟨h j, ?_⟩, Subtype.ext ?_⟩
    · have := hh j
      rwa [show L + w j - d = L - (d - w j) by have := hwd j; omega] at this
    · rw [jacMap_apply]; exact hsum.symm
  obtain ⟨ε, hε, H⟩ := eventually_surjective_affine (jacMap w d L hdL f hf) hsurj
    (fun k => jacMap w d L hdL (φ k) (hφ k))
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hgs : (f + ∑ k, C (s k) * φ k).IsWeightedHomogeneous w d := by
    refine hf.add (IsWeightedHomogeneous.sum _ _ _ fun k _ => ?_)
    exact (hφ k).C_mul (s k)
  have heq : jacMap w d L hdL f hf + ∑ k, s k • jacMap w d L hdL (φ k) (hφ k) =
      jacMap w d L hdL _ hgs := by
    apply LinearMap.ext; intro b; apply Subtype.ext
    simp only [LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, jacMap_apply, map_add, map_sum,
      mul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, MvPolynomial.smul_eq_C_mul, smul_eq_mul]
    ring
  have hS : ∀ y ∈ gradedS w L, y ∈ jacobianIdeal (f + ∑ k, C (s k) * φ k) := by
    intro y hy
    obtain ⟨b, hb⟩ := (heq ▸ H s hs) ⟨y, hy⟩
    have h2 : ∑ j, (b j : Poly n) * pderiv j (f + ∑ k, C (s k) * φ k) = y :=
      congrArg Subtype.val hb
    rw [← h2]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  refine exists_highIdeal_le_of_pow_X_mem fun i => ⟨L / w i, hS _ ?_⟩
  have := (isWeightedHomogeneous_X ℂ w i).pow (L / w i)
  rwa [smul_eq_mul, Nat.div_mul_cancel (hdvd i)] at this

end Yau
