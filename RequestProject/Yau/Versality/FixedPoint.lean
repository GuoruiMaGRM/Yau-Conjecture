import RequestProject.Yau.Versality.Jet

/-!
# Versality for fixed-origin linear families

For `f+tq` with the origin as its only critical point and with constant Milnor
number, construct an analytic parameter curve `γ(t)` and local right
equivalences to the monomial-basis miniversal deformation. The construction also
gives `q ≡ ∑ γ'_j(0)x^{β_j}` modulo `J_f`.
At the jet level the analytic inverse function theorem supplies a solution;
finite determinacy turns equality of sufficiently large jets into right equivalence.
Combining this result with the stratum theorem gives the first-order conclusion
used in Lemma 3.4. No separate general-versality hypothesis is required.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ## Preliminaries -/

/-- For polynomials, the local Milnor number at the origin is `milnorNumber`. -/
lemma localMilnorNumber_eval_zero (P : Poly n) :
    localMilnorNumber (fun x => eval x P) 0 = milnorNumber P := by
  rw [localMilnorNumber, localJacobianIdeal_eval_zero]
  rfl

/-- A polynomial isolated critical point is also isolated in the analytic function formulation. -/
lemma isIsolatedCriticalPointAt_of_hasIsolatedCriticalPoint {P : Poly n}
    (h : HasIsolatedCriticalPoint P) :
    IsIsolatedCriticalPointAt (fun x => eval x P) 0 := by
  have key : ∀ x, fderiv ℂ (fun x => eval x P) x = 0 ↔ ∀ i, eval x (pderiv i P) = 0 := by
    intro x
    rw [(hasFDerivAt_eval P x).fderiv]
    constructor
    · intro h0 i
      have := congrArg (fun L => L (Pi.single i 1)) h0
      simpa [evalDeriv_apply, Pi.single_apply] using this
    · intro h0
      ext v
      simp [evalDeriv_apply, h0]
  refine ⟨(key 0).2 h.1, ?_⟩
  obtain ⟨U, hU, hUc⟩ := h.2
  filter_upwards [diff_mem_nhdsWithin_compl hU {0}] with x hx
  intro h0
  exact hx.2 (hUc x hx.1 ((key x).1 h0))

lemma eval_bind₁_eq (x : Fin n → ℂ) (φ : Fin n → Poly n) (P : Poly n) :
    eval x (bind₁ φ P) = eval (fun i => eval x (φ i)) P := by
  show eval₂Hom (RingHom.id ℂ) _ _ = _
  rw [eval₂Hom_bind₁]
  rfl

/-- A monomial basis supplies the finite-jet data: each monomial in a sufficiently large box is a combination of the partial derivatives and basis monomials. -/
lemma exists_jet_data {f : Poly n} {μ : ℕ} {β : Fin μ → (Fin n →₀ ℕ)} (hβ : IsMonomialBasis f β)
    (b : Fin n →₀ ℕ) :
    ∃ (m : ℕ) (mono : Fin m → (Fin n →₀ ℕ)) (A : Fin m → Fin n → Poly n)
      (σc : Fin m → Fin μ → ℂ), Function.Injective mono ∧ (∀ α, α ≤ b → ∃ a, mono a = α) ∧
      ∀ a, monomial (mono a) 1 = ∑ i, pderiv i f * A a i + ∑ j, monomial (β j) (σc a j) := by
  classical
  have hrep : ∀ α : Fin n →₀ ℕ, ∃ (A : Fin n → Poly n) (σ : Fin μ → ℂ),
      monomial α 1 = ∑ i, pderiv i f * A i + ∑ j, monomial (β j) (σ j) := by
    intro α
    have hmem : Ideal.Quotient.mk (jacobianIdeal f) (monomial α (1 : ℂ)) ∈
        Submodule.span ℂ (Set.range fun j =>
          Ideal.Quotient.mk (jacobianIdeal f) (monomial (β j) (1 : ℂ))) := by
      rw [hβ.2]; trivial
    obtain ⟨σ, hσ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    have hJ : monomial α 1 - ∑ j, monomial (β j) (σ j) ∈ jacobianIdeal f := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hσ, map_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (monomial (β j) (σ j) : Poly n) = σ j • monomial (β j) 1 := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact (map_smul (Ideal.Quotient.mkₐ ℂ (jacobianIdeal f)) (σ j) _).symm
    obtain ⟨A, hA⟩ := Ideal.mem_span_range_iff_exists_fun.1 hJ
    refine ⟨A, σ, ?_⟩
    rw [← sub_eq_iff_eq_add]
    rw [← hA]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  choose A σ hAσ using hrep
  set S := Finset.Iic b
  refine ⟨S.card, fun a => (S.equivFin.symm a : Fin n →₀ ℕ), fun a => A _, fun a => σ _,
    ?_, ?_, fun a => hAσ _⟩
  · exact Subtype.val_injective.comp S.equivFin.symm.injective
  · intro α hα
    exact ⟨S.equivFin ⟨α, Finset.mem_Iic.2 hα⟩, by simp⟩

/-- If the origin is the only critical point of `h`, then `x_j^{μ(h)}∈J_h`. -/
lemma pow_milnorNumber_mem {h : Poly n}
    (hz : ∀ x : Fin n → ℂ, (∀ i, eval x (pderiv i h) = 0) → x = 0) (j : Fin n) :
    X j ^ milnorNumber h ∈ jacobianIdeal h := by
  have hpow := exists_pow_X_mem_jac hz
  haveI : Module.Finite ℂ (Poly n ⧸ jacobianIdeal h) := finite_quotient_of_pow_X_mem _ hpow
  have hrank : Module.finrank ℂ (Poly n ⧸ jacobianIdeal h) = milnorNumber h := by
    rw [milnorNumber]
    exact (quotientEquivConv hpow).toLinearEquiv.finrank_eq
  obtain ⟨N, hN⟩ := hpow j
  rw [← hrank]
  exact pow_finrank_mem _ _ hN

/-! ## Versality with the critical point fixed at the origin -/

/-- Versality for fixed-origin one-parameter families: constant Milnor number gives an analytic `γ(t)` with `γ(0)=0`, the first-order congruence modulo `J_f`, and analytic right equivalences `f+tq=F_{γ(t)}∘Θ_t` whose centers tend to the origin. -/
theorem versality_fixed_origin {f : Poly n} {μ : ℕ} {β : Fin μ → (Fin n →₀ ℕ)}
    (hβ : IsMonomialBasis f β) (q : Poly n)
    (hq : ∀ᶠ t in 𝓝 (0 : ℂ),
      (∀ x : Fin n → ℂ, (∀ i, eval x (pderiv i (f + C t * q)) = 0) ↔ x = 0) ∧
        milnorNumber (f + C t * q) = milnorNumber f) :
    ∃ γ : ℂ → (Fin μ → ℂ), AnalyticAt ℂ γ 0 ∧ γ 0 = 0 ∧
      q - ∑ j, monomial (β j) (deriv γ 0 j) ∈ jacobianIdeal f ∧
      ∃ c : ℂ → (Fin n → ℂ), Tendsto c (𝓝 0) (𝓝 0) ∧
        ∀ᶠ t in 𝓝 (0 : ℂ), ∃ Θ : (Fin n → ℂ) → (Fin n → ℂ), AnalyticAt ℂ Θ 0 ∧ Θ 0 = c t ∧
          (∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), fderiv ℂ Θ 0 = e) ∧
          ∀ᶠ y in 𝓝 0, eval y (f + C t * q) = miniversalDeformation f β (γ t) (Θ y) := by
  classical
  set μf := milnorNumber f
  set K := 2 * μf + q.totalDegree
  set b : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => K)
  have hb : ∀ i, b i = K := fun i => by simp [b]
  obtain ⟨m, mono, A, σc, hinj, hbox, hA⟩ := exists_jet_data hβ b
  obtain ⟨v, hvan, hv0, hvd, hjet⟩ := exists_jet_solution hinj hA q
  -- The support of `q` lies in the box.
  have hqsupp : ∀ α, coeff α q ≠ 0 → α ≤ b := by
    intro α hα i
    rw [hb]
    have h1 : α i ≤ α.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : α.degree ≤ q.totalDegree := by
      have := le_totalDegree (mem_support_iff.2 hα)
      rwa [Finsupp.degree_eq_sum, ← Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)]
    omega
  have hqsum : q = ∑ a, monomial (mono a) (coeff (mono a) q) := by
    ext α
    rw [coeff_sum]
    simp only [coeff_monomial]
    by_cases hα : ∃ a, mono a = α
    · obtain ⟨a, rfl⟩ := hα
      rw [Finset.sum_eq_single a]
      · simp
      · intro b' _ hb'; rw [if_neg (fun h => hb' (hinj h))]
      · simp
    · push_neg at hα
      rw [Finset.sum_eq_zero fun a _ => if_neg (hα a)]
      by_contra hne
      obtain ⟨a, ha⟩ := hbox α (hqsupp α hne)
      exact hα a ha
  -- The parameter curve `γ(t)=s(v(t))`.
  set γ : ℂ → (Fin μ → ℂ) := fun t => jetParam σc (v t)
  have hvc : ∀ a, AnalyticAt ℂ (fun t => v t a) 0 := analyticAt_pi_iff.1 hvan
  have hγan : AnalyticAt ℂ γ 0 := analyticAt_pi_iff.2 fun j =>
    Finset.univ.analyticAt_fun_sum fun a _ => (hvc a).mul analyticAt_const
  have hγ0 : γ 0 = 0 := by funext j; simp [γ, jetParam, hv0]
  have hγd : deriv γ 0 = fun j => ∑ a, coeff (mono a) q * σc a j := by
    have : HasDerivAt γ (fun j => ∑ a, coeff (mono a) q * σc a j) 0 := by
      rw [hasDerivAt_pi]
      intro j
      exact HasDerivAt.fun_sum fun a _ => (hasDerivAt_pi.1 hvd a).mul_const (σc a j)
    exact this.deriv
  refine ⟨γ, hγan, hγ0, ?_, ?_⟩
  · -- The first-order relation.
    rw [hγd]
    have key : ∀ cq : Fin m → ℂ, (∑ a, monomial (mono a) (cq a)) -
        ∑ j, monomial (β j) (∑ a, cq a * σc a j) = ∑ a, C (cq a) * ∑ i, pderiv i f * A a i := by
      intro cq
      have hm : ∀ a, monomial (mono a) (cq a) = C (cq a) * monomial (mono a) 1 := fun a => by
        rw [C_mul_monomial, mul_one]
      simp only [hm, hA, mul_add, Finset.sum_add_distrib, Finset.mul_sum, C_mul_monomial]
      rw [Finset.sum_comm (f := fun a j => monomial (β j) (cq a * σc a j))]
      simp only [← map_sum (monomial _)]
      abel
    have := key (fun a => coeff (mono a) q)
    rw [← hqsum] at this
    rw [this]
    exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _
      (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))
  -- The coordinate change `ψ_t(x)=x+ξ_{v(t)}(x)`.
  set Φ : ℂ → (Fin n → ℂ) → (Fin n → ℂ) := fun t x i => eval x (jetMap A (v t) i)
  have hΦform : ∀ t x i, Φ t x i = x i + ∑ a, v t a * eval x (A a i) := fun t x i => by
    simp [Φ, jetMap]
  have hΦan : AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2) (0, 0) := by
    rw [analyticAt_pi_iff]
    intro i
    have e : (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2 i) =
        fun z => z.2 i + ∑ a, v z.1 a * eval z.2 (A a i) := funext fun z => hΦform _ _ _
    rw [e]
    refine AnalyticAt.add ?_ ?_
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _).comp
        analyticAt_snd
    exact Finset.univ.analyticAt_fun_sum fun a _ =>
      (AnalyticAt.comp_of_eq (hvc a) analyticAt_fst rfl).mul
        ((analyticAt_eval (A a i) _).comp analyticAt_snd)
  have hΦ0 : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), Φ 0 x = x :=
    Eventually.of_forall fun x => by funext i; simp [hΦform, hv0]
  have hΦan_t : ∀ t x, AnalyticAt ℂ (Φ t) x := by
    intro t x
    rw [analyticAt_pi_iff]
    intro i
    exact analyticAt_eval _ x
  refine ⟨fun t => Φ t 0, ?_, ?_⟩
  · have := hΦan.continuousAt.tendsto.comp (tendsto_graph (n := n) tendsto_const_nhds)
    simpa [Function.comp_def, show Φ 0 0 = 0 from hΦ0.self_of_nhds] using this
  filter_upwards [hq, hjet, eventually_fderiv_slice_equiv hΦan hΦ0
    (p := fun _ => (0 : Fin n → ℂ)) tendsto_const_nhds] with t ⟨hz, hμ⟩ hjt ⟨e, he⟩
  set h := f + C t * q
  set g := jetPoly f β A σc (v t)
  have hcrit0 : ∀ i, eval 0 (pderiv i h) = 0 := ((hz 0).2 rfl)
  -- `x_j^{K+1} ∈ 𝔪 J_h²`
  have hpow : ∀ j, (X j : Poly n) ^ (b j + 1) ∈ tougIdeal h := by
    intro j
    have h1 := pow_mem_tougIdeal (pow_milnorNumber_mem (fun x hx => (hz x).1 hx) j)
    rw [hμ] at h1
    rw [hb, show K + 1 = (2 * μf + 1) + q.totalDegree by omega, pow_add]
    exact Ideal.mul_mem_right _ _ h1
  have hgh : g - h ∈ tougIdeal h := by
    apply mem_of_coeff_box _ b hpow
    intro α hα
    obtain ⟨a, rfl⟩ := hbox α hα
    rw [coeff_sub, hjt a, sub_self]
  obtain ⟨Φ', hΦ'an, hΦ'0, hΦ'd, hΦ'eq⟩ := exists_rightEquiv_of_mem_tougIdeal hcrit0 hgh
  obtain ⟨Ψ', hΨ'an, hΨ'0, -, hright, hΨ'd⟩ := exists_analytic_localInverse_id hΦ'an hΦ'd.fderiv
  rw [hΦ'0] at hΨ'an hΨ'0 hright hΨ'd
  have hΨ't : Tendsto Ψ' (𝓝 0) (𝓝 0) := by
    have := hΨ'an.continuousAt.tendsto; rwa [hΨ'0] at this
  refine ⟨fun y => Φ t (Ψ' y), AnalyticAt.comp_of_eq (hΦan_t t 0) hΨ'an hΨ'0, by simp [hΨ'0],
    ⟨e, ?_⟩, ?_⟩
  · have hd := ((hΦan_t t (Ψ' 0)).differentiableAt.hasFDerivAt).comp (0 : Fin n → ℂ) hΨ'd
    rw [hΨ'0, he] at hd
    rw [show (fun y => Φ t (Ψ' y)) = Φ t ∘ Ψ' from rfl, hd.fderiv]
    rfl
  · filter_upwards [hright, hΨ't.eventually hΦ'eq] with y hy1 hy2
    calc eval y h = eval (Φ' (Ψ' y)) h := by rw [hy1]
      _ = eval (Ψ' y) g := hy2.symm
      _ = _ := by
        show eval (Ψ' y) (jetPoly f β A σc (v t)) = _
        rw [jetPoly, eval_bind₁_eq]; rfl

/-! ## The fixed-origin first-order consequence -/

/-- For homogeneous `q` of degree less than `d`, the fixed-origin isolatedness, zero-critical-value, and constant-Milnor-number hypotheses imply `q∈J_f` from the stratum theorem and the versality construction proved above. -/
theorem corollary35_fixed_origin (hV : VarchenkoTheorem) {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d) (hcrit : HasIsolatedCriticalPoint f)
    (hf0 : eval 0 f = 0) {q : Poly n} {e : ℕ} (hq : q.IsWeightedHomogeneous w e) (he : e < d)
    (hfam : ∀ᶠ t in 𝓝 (0 : ℂ),
      (∀ x : Fin n → ℂ, (∀ i, eval x (pderiv i (f + C t * q)) = 0) ↔ x = 0) ∧
        eval 0 (f + C t * q) = 0 ∧ milnorNumber (f + C t * q) = milnorNumber f) :
    q ∈ jacobianIdeal f := by
  have hiso := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit
  obtain ⟨μ, β, hβ⟩ := exists_monomialBasis hiso
  obtain ⟨γ, hγan, hγ0, hfirst, c, hc, hev⟩ := versality_fixed_origin hβ q
    (hfam.mono fun t ht => ⟨ht.1, ht.2.2⟩)
  obtain ⟨ε, hε0, hε⟩ := hV n w d f hw hf hcrit hf0 μ β hβ
  have hγε : ∀ᶠ t in 𝓝 (0 : ℂ), ‖γ t‖ < ε :=
    hγan.continuousAt.norm.eventually (gt_mem_nhds (by simpa [hγ0] using hε0))
  have hcε : ∀ᶠ t in 𝓝 (0 : ℂ), ‖c t‖ < ε :=
    hc.norm.eventually (gt_mem_nhds (by simpa using hε0))
  have hvan : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j, Finsupp.weight w (β j) < d → γ t j = 0 := by
    filter_upwards [hev, hfam, hγε, hcε] with t ⟨Θ, hΘan, hΘ0, ⟨e', he'⟩, hΘeq⟩ ⟨hz, hval, hμ⟩
      h1 h2
    have hg := analyticAt_miniversalDeformation f β (γ t) (Θ 0)
    have hisoh : IsIsolatedCriticalPointAt (fun y => eval y (f + C t * q)) 0 :=
      isIsolatedCriticalPointAt_of_hasIsolatedCriticalPoint
        ⟨(hz 0).2 rfl, Set.univ, univ_mem, fun x _ hx => (hz x).1 hx⟩
    apply hε (γ t) (Θ 0) h1 (by rw [hΘ0]; exact h2)
    · exact isIsolatedCriticalPointAt_of_comp hg hΘan he'
        ((isIsolatedCriticalPointAt_congr hΘeq).1 hisoh)
    · rw [← hΘeq.self_of_nhds]; exact hval
    · rw [← localMilnorNumber_comp hg hΘan he', ← localMilnorNumber_congr hΘeq,
        localMilnorNumber_eval_zero, localMilnorNumber_eval_zero, hμ]
  have hd0 : ∀ j, Finsupp.weight w (β j) < d → deriv γ 0 j = 0 := by
    intro j hj
    have h1 : (fun t => γ t j) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hvan] with t ht using ht j hj
    rw [← (hasDerivAt_pi.1 hγan.differentiableAt.hasDerivAt j).deriv, h1.deriv_eq, deriv_const]
  exact mem_jacobianIdeal_of_sub_mem hf hq he
    (weightedHomogeneousComponent_sum_monomial_eq_zero hd0) hfirst

/-- For the square deformation in Lemma 3.3, the origin is the only critical point. -/
lemma squareDeformation_critical_iff {w : Fin n → ℕ} {d : ℕ} {g : Poly n} (H : Setup w d g)
    {r : ℕ} {a : Poly n} (ha : a.IsWeightedHomogeneous w r) (hr : 3 * r < d)
    (haI : a ∈ (partialIdeal w g r).radical) (t : ℂ) (x : Fin n → ℂ) :
    (∀ i, eval x (pderiv i (g + C t * a ^ 2)) = 0) ↔ x = 0 := by
  constructor
  · intro hx
    have haY : ∀ i ∈ {i | r < w i}, pderiv i a = 0 := fun i hi => pderiv_eq_zero_of_lt ha i hi
    have hrad := radical_jacobianIdeal_add_sq g a {i | r < w i} haY haI t
    refine H.common_zero x fun i => ?_
    have hmem : pderiv i g ∈ (jacobianIdeal (g + C t * a ^ 2)).radical := by
      rw [hrad]; exact Ideal.le_radical (Ideal.subset_span ⟨i, rfl⟩)
    obtain ⟨N, hN⟩ := hmem
    have := mem_jac_eval_zero hx hN
    rw [map_pow] at this
    exact (pow_eq_zero_iff'.1 this).1
  · rintro rfl
    exact (squareDeformation_hyp H ha hr haI t).1.1

end Yau
