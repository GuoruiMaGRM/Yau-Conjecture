import RequestProject.Yau.Versality.Tools

/-!
# Finite determinacy by a Tougeron argument

If the origin is critical for `h` and `g-h∈𝔪 J_h²`, there is an analytic
coordinate change `Φ`, tangent to the identity at zero, with `g=h∘Φ` nearby.
Write the coordinate correction as a combination of the partial derivatives.
The algebraic Taylor formula reduces the required identity to an equation
whose linearization is the identity, solved by the analytic inverse function theorem.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The algebraic Taylor formula with a quadratic remainder: `h(x+w)=h(x)+∑ ∂_a h(x)w_a+∑ w_a w_b H_{ab}(x,w)`. -/
theorem exists_taylor_remainder (h : Poly n) :
    ∃ H : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ, ∀ x w : Fin n → ℂ,
      eval (x + w) h = eval x h + ∑ a, eval x (pderiv a h) * w a +
        ∑ a, ∑ b, w a * w b * eval (Sum.elim x w) (H a b) := by
  classical
  let Y : Fin n ⊕ Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ :=
    Sum.elim (fun i => X (Sum.inr i)) (fun _ => 0)
  have hm := bind₁_X_add_sub_mem Y (rename Sum.inl h)
  obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.1 hm
  refine ⟨fun a b => r (Sum.inl a, Sum.inl b), fun x w => ?_⟩
  have := congrArg (eval (Sum.elim x w)) hr
  have hb : bind₁ (fun i => X i + Y i) (rename Sum.inl h) =
      bind₁ (fun i => X (Sum.inl i) + X (Sum.inr i)) h := by
    rw [bind₁_rename]; rfl
  have he : ∀ P : Poly n, eval (Sum.elim x w) (bind₁ (fun i => X (Sum.inl i) + X (Sum.inr i)) P)
      = eval (x + w) P := by
    intro P
    show eval₂Hom (RingHom.id ℂ) _ _ = _
    rw [eval₂Hom_bind₁]
    show eval₂Hom (RingHom.id ℂ) _ P = eval₂Hom (RingHom.id ℂ) _ P
    congr 2
    funext i
    simp
  simp only [map_sub, map_sum, map_mul, hb, he, eval_rename, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Y, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Function.comp_def, eval_X,
    pderiv_rename Sum.inl_injective] at this
  have key : ∑ a, ∑ b, w a * w b * eval (Sum.elim x w) (r (Sum.inl a, Sum.inl b)) =
      ∑ a, ∑ b, eval (Sum.elim x w) (r (Sum.inl a, Sum.inl b)) * (w a * w b) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key]
  linear_combination (-1 : ℂ) * this
/-- Reorder a quadruple sum. -/
lemma sum4_perm (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ i, ∑ k, F a b i k = ∑ i, ∑ k, ∑ a, ∑ b, F a b i k := by
  calc ∑ a, ∑ b, ∑ i, ∑ k, F a b i k = ∑ a, ∑ i, ∑ b, ∑ k, F a b i k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ k, F a b i k := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ k, ∑ b, F a b i k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ a, ∑ b, F a b i k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- The ideal `𝔪 J_h²`. -/
def tougIdeal (h : Poly n) : Ideal (Poly n) :=
  Ideal.span (Set.range fun lik : Fin n × Fin n × Fin n =>
    X lik.1 * (pderiv lik.2.1 h * pderiv lik.2.2 h))

/-- If `x_j^N∈J_h`, then `x_j^{2N+1}∈𝔪 J_h²`. -/
lemma pow_mem_tougIdeal {h : Poly n} {j : Fin n} {N : ℕ} (hN : X j ^ N ∈ jacobianIdeal h) :
    X j ^ (2 * N + 1) ∈ tougIdeal h := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hN
  have : (X j : Poly n) ^ (2 * N + 1) =
      ∑ i, ∑ k, (a i * a k) * (X j * (pderiv i h * pderiv k h)) := by
    rw [show 2 * N + 1 = N + N + 1 by ring, pow_succ, pow_add, ← ha, Finset.sum_mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  exact Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun k _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(j, i, k), rfl⟩)

lemma exists_coeff_of_mem_tougIdeal {h P : Poly n} (hP : P ∈ tougIdeal h) :
    ∃ c : Fin n → Fin n → Poly n, (∀ i k, eval 0 (c i k) = 0) ∧
      P = ∑ i, ∑ k, pderiv i h * pderiv k h * c i k := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.1 hP
  refine ⟨fun i k => ∑ l, r (l, i, k) * X l, fun i k => by simp, ?_⟩
  rw [← hr, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Tougeron finite determinacy: if zero is critical for `h` and `g-h∈𝔪 J_h²`, there is a local analytic coordinate change `Φ` with `Φ(0)=0`, differential the identity, and `g=h∘Φ`. -/
theorem exists_rightEquiv_of_mem_tougIdeal {h g : Poly n}
    (hcrit : ∀ i, eval 0 (pderiv i h) = 0) (hmem : g - h ∈ tougIdeal h) :
    ∃ Φ : (Fin n → ℂ) → (Fin n → ℂ), AnalyticAt ℂ Φ 0 ∧ Φ 0 = 0 ∧
      HasFDerivAt Φ (ContinuousLinearMap.id ℂ (Fin n → ℂ)) 0 ∧
      ∀ᶠ x in 𝓝 0, eval x g = eval (Φ x) h := by
  obtain ⟨c, hc0, hc⟩ := exists_coeff_of_mem_tougIdeal hmem
  obtain ⟨H, hH⟩ := exists_taylor_remainder h
  let D : Fin n → (Fin n → ℂ) → ℂ := fun l x => eval x (pderiv l h)
  let U : (Fin n → ℂ) × (Fin n → Fin n → ℂ) → Fin n → Fin n → ℂ :=
    fun z a l => z.2 a l + eval z.1 (c a l)
  let W : (Fin n → ℂ) × (Fin n → Fin n → ℂ) → Fin n → ℂ := fun z a => ∑ l, D l z.1 * U z a l
  let HH : (Fin n → ℂ) × (Fin n → Fin n → ℂ) → Fin n → Fin n → ℂ :=
    fun z a b => eval (Sum.elim z.1 (W z)) (H a b)
  let Q : (Fin n → ℂ) × (Fin n → Fin n → ℂ) → Fin n → Fin n → ℂ :=
    fun z i k => ∑ a, ∑ b, U z a i * U z b k * HH z a b
  let Θ : (Fin n → ℂ) × (Fin n → Fin n → ℂ) → (Fin n → ℂ) × (Fin n → Fin n → ℂ) :=
    fun z => (z.1, z.2 + Q z)
  -- The algebraic identity.
  have hkey : ∀ z, eval (z.1 + W z) h =
      eval z.1 h + ∑ i, ∑ k, D i z.1 * D k z.1 * (U z i k + Q z i k) := by
    intro z
    rw [hH]
    have h1 : ∑ a, eval z.1 (pderiv a h) * W z a = ∑ i, ∑ k, D i z.1 * D k z.1 * U z i k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [W, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∑ a, ∑ b, W z a * W z b * eval (Sum.elim z.1 (W z)) (H a b) =
        ∑ i, ∑ k, D i z.1 * D k z.1 * Q z i k := by
      have e1 : ∀ a b, W z a * W z b * eval (Sum.elim z.1 (W z)) (H a b) =
          ∑ i, ∑ k, D i z.1 * D k z.1 * (U z a i * U z b k * HH z a b) := by
        intro a b
        show (∑ i, D i z.1 * U z a i) * (∑ k, D k z.1 * U z b k) * HH z a b = _
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [e1]
      rw [sum4_perm]
      simp only [Q, Finset.mul_sum]
    rw [h1, h2, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- Analyticity.
  have hAx : ∀ (P : Poly n) z, AnalyticAt ℂ (fun z : (Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
      eval z.1 P) z := fun P z => (analyticAt_eval P z.1).comp analyticAt_fst
  have hAu : ∀ a l z, AnalyticAt ℂ (fun z : (Fin n → ℂ) × (Fin n → Fin n → ℂ) => z.2 a l) z :=
    fun a l z => (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) l).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) a)).comp
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → Fin n → ℂ))).analyticAt z
  have hU : ∀ a l z, AnalyticAt ℂ (fun z => U z a l) z := fun a l z => (hAu a l z).add (hAx _ z)
  have hW : ∀ a z, AnalyticAt ℂ (fun z => W z a) z := fun a z => by
    have := Finset.univ.analyticAt_sum (fun l _ => (hAx (pderiv l h) z).mul (hU a l z))
    convert this using 1
    funext z; simp [W, D]
  have hHH : ∀ a b z, AnalyticAt ℂ (fun z => HH z a b) z := fun a b z => by
    have hco : ∀ c, AnalyticAt ℂ (fun z : (Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
        Sum.elim z.1 (W z) c) z := by
      rintro (i | i)
      · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _).comp
          analyticAt_fst
      · exact hW i z
    have := AnalyticAt.aeval_mvPolynomial hco (H a b)
    simpa [HH, MvPolynomial.coe_aeval_eq_eval] using this
  have hQ : ∀ i k z, AnalyticAt ℂ (fun z => Q z i k) z := fun i k z => by
    have := Finset.univ.analyticAt_sum (fun a _ => Finset.univ.analyticAt_sum
      (fun b _ => ((hU a i z).mul (hU b k z)).mul (hHH a b z)))
    convert this using 1
    funext z; simp [Q]
  have hΘan : AnalyticAt ℂ Θ 0 := by
    refine analyticAt_fst.prod (analyticAt_snd.add ?_)
    exact analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun k => hQ i k 0
  -- The derivative.
  have hU0 : ∀ a l, U 0 a l = 0 := fun a l => by
    show (0 : Fin n → Fin n → ℂ) a l + eval (0 : Fin n → ℂ) (c a l) = 0
    rw [hc0]; simp
  have hQd : HasFDerivAt Q (0 : (Fin n → ℂ) × (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → Fin n → ℂ)) 0 := by
    rw [hasFDerivAt_pi']
    intro i
    rw [ContinuousLinearMap.comp_zero, hasFDerivAt_pi']
    intro k
    rw [ContinuousLinearMap.comp_zero]
    have hterm : ∀ a b, HasFDerivAt (fun z => U z a i * U z b k * HH z a b)
        (0 : (Fin n → ℂ) × (Fin n → Fin n → ℂ) →L[ℂ] ℂ) 0 := by
      intro a b
      have h1 := hasFDerivAt_mul_of_eq_zero (hU a i 0).differentiableAt
        (hU b k 0).differentiableAt (hU0 a i) (hU0 b k)
      refine (h1.mul (hHH a b 0).differentiableAt.hasFDerivAt).congr_fderiv ?_
      exact ContinuousLinearMap.ext fun v => by simp [hU0]
    have := HasFDerivAt.fun_sum (u := Finset.univ) fun a _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun b _ => hterm a b
    simpa [Q] using this
  have hΘd : HasFDerivAt Θ (ContinuousLinearMap.id ℂ _) 0 := by
    refine (hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add hQd)).congr_fderiv ?_
    ext v <;> simp
  have hQ0 : Q 0 = 0 := by
    funext i k
    simp [Q, hU0]
  have hΘ0 : Θ 0 = 0 := by
    show ((0 : Fin n → ℂ), (0 : Fin n → Fin n → ℂ) + Q 0) = 0
    rw [hQ0, add_zero]; rfl
  obtain ⟨Ψ, hΨan, hΨ0, -, hright, -⟩ := exists_analytic_localInverse_id hΘan hΘd.fderiv
  rw [hΘ0] at hΨan hΨ0 hright
  let ι : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → Fin n → ℂ) := fun x => (x, 0)
  have hιan : AnalyticAt ℂ ι 0 := analyticAt_id.prod analyticAt_const
  have hι0 : ι 0 = 0 := rfl
  have hι : Tendsto ι (𝓝 0) (𝓝 0) := by
    have := hιan.continuousAt.tendsto; rwa [hι0] at this
  let zz : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → Fin n → ℂ) := fun x => Ψ (ι x)
  have hzan : AnalyticAt ℂ zz 0 := AnalyticAt.comp_of_eq hΨan hιan hι0
  have hz0 : zz 0 = 0 := hΨ0
  have hev : ∀ᶠ x in 𝓝 0, Θ (zz x) = ι x := hι.eventually hright
  have hWz : ∀ a, AnalyticAt ℂ (fun x => W (zz x) a) 0 := fun a =>
    AnalyticAt.comp_of_eq (g := fun y => W y a) (f := zz) (hW a (zz 0)) hzan rfl
  refine ⟨fun x => x + W (zz x), ?_, ?_, ?_, ?_⟩
  · exact analyticAt_id.add (analyticAt_pi_iff.2 hWz)
  · show 0 + W (zz 0) = 0
    rw [hz0]
    funext a
    simp [W, hU0]
  · have hWd : HasFDerivAt (fun x => W (zz x)) (0 : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) 0 := by
      rw [hasFDerivAt_pi']
      intro a
      rw [ContinuousLinearMap.comp_zero]
      have hterm : ∀ l, HasFDerivAt (fun x => D l (zz x).1 * U (zz x) a l)
          (0 : (Fin n → ℂ) →L[ℂ] ℂ) 0 := by
        intro l
        refine hasFDerivAt_mul_of_eq_zero ?_ ?_ ?_ ?_
        · exact (AnalyticAt.comp_of_eq (g := fun y => eval y.1 (pderiv l h)) (f := zz)
            (hAx (pderiv l h) (zz 0)) hzan rfl).differentiableAt
        · exact (AnalyticAt.comp_of_eq (g := fun y => U y a l) (f := zz)
            (hU a l (zz 0)) hzan rfl).differentiableAt
        · simp [D, hz0, hcrit]
        · simp only [hz0]; exact hU0 a l
      have := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => hterm l
      simpa [W] using this
    have := (hasFDerivAt_id (0 : Fin n → ℂ)).add hWd
    simpa using this
  · filter_upwards [hev] with x hx
    have h1 : (zz x).1 = x := congrArg Prod.fst hx
    have h2 : (zz x).2 + Q (zz x) = 0 := congrArg Prod.snd hx
    have h3 : x + W (zz x) = (zz x).1 + W (zz x) := by rw [h1]
    show eval x g = eval (x + W (zz x)) h
    rw [h3, hkey (zz x)]
    have h4 : ∀ i k, U (zz x) i k + Q (zz x) i k = eval x (c i k) := by
      intro i k
      have := congrFun (congrFun h2 i) k
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [U, h1]
      linear_combination this
    simp only [h4, h1, D]
    have := congrArg (eval x) hc
    simp only [map_sub, map_sum, map_mul] at this
    linear_combination this
end Yau
