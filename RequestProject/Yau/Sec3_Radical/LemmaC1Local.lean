import RequestProject.Yau.Sec3_Radical.LemmaC1
import RequestProject.Yau.Versality.FixedPoint

/-!
# Local Milnor numbers for higher-weight perturbations

For isolated weighted homogeneous `g` and a polynomial `R` of strictly higher
weight, suitable powers of the coordinates belong locally to `J_{g+R}`.
Thus the origin remains an isolated critical point and the local Milnor number
equals `dim ℂ[x]/J_g`.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {g R : Poly n}

/-- A polynomial with nonzero constant term is a unit in `ℂ{x}`. -/
lemma isUnit_polyToConv {u : Poly n} (hu : eval 0 u ≠ 0) : IsUnit (polyToConv u) := by
  have hA : AnalyticAt ℂ (fun x => eval x u) 0 := analyticAt_eval u 0
  have hI : AnalyticAt ℂ (fun x => (eval x u)⁻¹) 0 := hA.inv hu
  rw [← taylorAt_eval_zero]
  refine IsUnit.of_mul_eq_one (b := taylorAt (fun x => (eval x u)⁻¹) 0) ?_
  rw [← taylorAt_mul hA hI]
  have hne : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), eval x u ≠ 0 := hA.continuousAt.eventually_ne hu
  rw [taylorAt_congr (h' := fun _ => (1 : ℂ)) (by
    filter_upwards [hne] with x hx; exact mul_inv_cancel₀ hx), taylorAt_const, map_one]

lemma eval_zero_of_mem_highIdeal {T : ℕ} (hT : 0 < T) {p : Poly n} (hp : p ∈ highIdeal w T) :
    eval 0 p = 0 := by
  rw [show eval 0 p = coeff 0 p by rw [← constantCoeff_eq, MvPolynomial.eval_zero]]
  by_contra h
  have := hp 0 (mem_support_iff.2 h)
  simp at this; omega

lemma X_pow_mem_highIdeal (hw : ∀ i, 0 < w i) (i : Fin n) (N : ℕ) :
    (X i : Poly n) ^ N ∈ highIdeal w N := by
  have h : ((X i : Poly n) ^ N).IsWeightedHomogeneous w (N * w i) := by
    simpa [smul_eq_mul] using (isWeightedHomogeneous_X ℂ w i).pow N
  exact isWH_mem_highIdeal h (Nat.le_mul_of_pos_right N (hw i))

/-- There is a polynomial `u` with `u(0)=1` such that `u x_l^N ∈ J_{g+R}` for every `l`. -/
theorem exists_unit_mul_pow_mem (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1)) {T₀ : ℕ}
    (hT₀ : highIdeal w T₀ ≤ jacobianIdeal g) :
    ∃ (u : Poly n) (N : ℕ), 0 < N ∧ eval 0 u = 1 ∧ ∀ l, u * X l ^ N ∈ jacobianIdeal (g + R) := by
  classical
  set N := T₀ + 1
  set K := (N + 1) * ∑ i, w i + 1
  have hq : ∀ l : Fin n, ∃ q ∈ jacobianIdeal (g + R), (X l : Poly n) ^ N - q ∈ highIdeal w K := by
    intro l
    obtain ⟨q, hq, hpq⟩ := approx hg hwd hR hT₀ K T₀ le_rfl _
      (highIdeal_mono (by omega) (X_pow_mem_highIdeal hw l N))
    exact ⟨q, hq, highIdeal_mono (by omega) hpq⟩
  choose q hqJ hqK using hq
  have he : ∀ l, ∃ e : Fin n → Poly n, ∑ i, e i * X i ^ (N + 1) = X l ^ N - q l := fun l =>
    Ideal.mem_span_range_iff_exists_fun.1 (highIdeal_le_span_X_pow (N + 1) (hqK l))
  choose e he using he
  set M : Matrix (Fin n) (Fin n) (Poly n) := 1 - Matrix.of fun l i => e l i * X i with hM
  set x : Fin n → Poly n := fun i => X i ^ N with hx
  have hMx : M.mulVec x = q := by
    funext l
    rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hx]
    rw [show ∑ i, e l i * X i * X i ^ N = ∑ i, e l i * X i ^ (N + 1) from
      Finset.sum_congr rfl fun i _ => by ring, he l]
    ring
  refine ⟨M.det, N, by omega, ?_, fun l => ?_⟩
  · rw [RingHom.map_det]
    have : (eval (0 : Fin n → ℂ)).mapMatrix M = 1 := by
      ext i j
      simp [hM, Matrix.one_apply]
    rw [this, Matrix.det_one]
  · have key : (M.adjugate.mulVec (M.mulVec x)) l = M.det * x l := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [show M.det * X l ^ N = M.det * x l from rfl, ← key, hMx]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hqJ i)

/-- The origin is an isolated critical point of `g+R`. -/
theorem hasIsolatedCriticalPoint_add_high (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1)) {T₀ : ℕ}
    (hT₀ : highIdeal w T₀ ≤ jacobianIdeal g) : HasIsolatedCriticalPoint (g + R) := by
  obtain ⟨u, N, hN, hu0, hu⟩ := exists_unit_mul_pow_mem hw hg hwd hR hT₀
  refine ⟨fun i => ?_, {x | eval x u ≠ 0}, ?_, fun x hx hcrit => funext fun l => ?_⟩
  · rw [map_add, map_add, eval_zero_of_isWH_pos (pderiv_f_isWH hg i) (by have := hwd i; omega),
      eval_zero_of_mem_highIdeal (by omega) (pderiv_R_mem hwd hR i), add_zero]
  · exact (continuous_eval u).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds (by rw [hu0]; exact one_ne_zero))
  · have := mem_jac_eval_zero hcrit (hu l)
    rw [map_mul, map_pow, eval_X] at this
    exact pow_eq_zero_iff hN.ne' |>.1 ((mul_eq_zero.1 this).resolve_left hx)

set_option synthInstance.maxHeartbeats 200000 in
/-- The local Milnor number `dim ℂ{x}/J_{g+R}` equals `dim ℂ[x]/J_g`. -/
theorem localMilnorNumber_add_high (hw : ∀ i, 0 < w i) (hg : g.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity g) (hwd : ∀ i, w i < d) (hR : R ∈ highIdeal w (d + 1))
    {T₀ : ℕ} (hT₀ : highIdeal w T₀ ≤ jacobianIdeal g) :
    localMilnorNumber (fun x => eval x (g + R)) 0 = Module.finrank ℂ (MilnorAlgebra g) := by
  obtain ⟨u, N, -, hu0, hu⟩ := exists_unit_mul_pow_mem hw hg hwd hR hT₀
  set T := T₀ + (N * ∑ i, w i + 1)
  set I := jacobianIdeal (g + R) ⊔ highIdeal w T
  have hunit := isUnit_polyToConv (u := u) (by rw [hu0]; exact one_ne_zero)
  have hconv : convIdeal I = convIdeal (jacobianIdeal (g + R)) := by
    refine le_antisymm ?_ (Ideal.map_mono le_sup_left)
    rw [convIdeal, Ideal.map_sup, sup_le_iff]
    refine ⟨le_rfl, ?_⟩
    refine (Ideal.map_mono ((highIdeal_mono (by omega)).trans (highIdeal_le_span_X_pow N))).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    obtain ⟨v, hv⟩ := hunit.exists_left_inv
    have h1 : polyToConv (u * X l ^ N) ∈ convIdeal (jacobianIdeal (g + R)) :=
      Ideal.mem_map_of_mem _ (hu l)
    rw [map_mul] at h1
    have := Ideal.mul_mem_left _ v h1
    rwa [← mul_assoc, hv, one_mul] at this
  have hI : ∀ i, ∃ N : ℕ, (X i : Poly n) ^ N ∈ I := fun i =>
    ⟨T, Ideal.mem_sup_right (X_pow_mem_highIdeal hw i T)⟩
  rw [localMilnorNumber, localJacobianIdeal_eval_zero, ← hconv,
    ← (quotientEquivConv hI).toLinearEquiv.finrank_eq]
  exact (finrank_quot_high hw hg hiso hwd hR hT₀ (by omega)).2

end Yau
