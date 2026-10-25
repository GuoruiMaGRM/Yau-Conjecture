import RequestProject.Yau.Basic.Convergent
import RequestProject.Yau.Basic.Basic

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The diagonal `x ↦ P_m(x, …, x)` of the degree-`m` term of a formal multilinear series, as a homogeneous polynomial. -/
def homogPoly (P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ) (m : ℕ) : Poly n :=
  ∑ s : Fin m → Fin n, C (P m (fun k => Pi.single (s k) 1)) * ∏ k, X (s k)

lemma eval_homogPoly (P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ) (m : ℕ) (x : Fin n → ℂ) :
    eval x (homogPoly P m) = P m (fun _ => x) := by
  conv_rhs => rw [show (fun _ : Fin m => x) = fun _ : Fin m => ∑ i, x i • (Pi.single i 1 : Fin n → ℂ)
    by funext _ j; simp [Pi.single_apply]]
  rw [ContinuousMultilinearMap.map_sum, homogPoly, map_sum]
  refine Finset.sum_congr ?_ fun s _ => ?_
  · simp
  · rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, map_mul, eval_C, map_prod]
    simp [mul_comm]

lemma isHomogeneous_homogPoly (P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ) (m : ℕ) :
    (homogPoly P m).IsHomogeneous m := by
  apply MvPolynomial.IsHomogeneous.sum
  intro s _
  have := (isHomogeneous_C (Fin n) (P m (fun k => Pi.single (s k) 1))).mul
    (MvPolynomial.IsHomogeneous.prod Finset.univ (fun k => X (s k)) (fun _ => 1)
      (fun k _ => isHomogeneous_X ℂ (s k)))
  simpa using this

/-- Uniqueness of a one-variable power series: if its sum vanishes for every `|s| < ε`, all coefficients vanish. -/
lemma coeff_eq_zero_of_hasSum_zero {c : ℕ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ s : ℂ, ‖s‖ < ε → HasSum (fun m => c m * s ^ m) 0) : c = 0 := by
  set r : NNReal := ⟨ε / 2, by positivity⟩
  have hr : (r : ℝ) = ε / 2 := rfl
  have hrε : (r : ℝ) < ε := by rw [hr]; linarith
  have hrad : (r : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    have h1 := (hs (r : ℂ) (by simpa [Complex.norm_real, abs_of_nonneg r.2] using hrε)).tendsto_sum_nat
    have h2 := (hs (r : ℂ) (by simpa [Complex.norm_real, abs_of_nonneg r.2] using hrε)).summable.tendsto_atTop_zero
    have h3 := h2.norm
    simp only [norm_zero] at h3
    refine h3.congr fun m => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      NNReal.norm_eq]
  have hP : HasFPowerSeriesOnBall (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ c) 0 r := by
    refine ⟨hrad, ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos, hr]; positivity), fun {y} hy => ?_⟩
    simp only [Pi.zero_apply, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    apply hs
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hy
    linarith
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 hP.hasFPowerSeriesAt.eq_zero

/-- Scaling a homogeneous polynomial: `Q(s x) = s^m Q(x)`. -/
lemma eval_smul_of_isHomogeneous {Q : Poly n} {m : ℕ} (hQ : Q.IsHomogeneous m) (s : ℂ)
    (x : Fin n → ℂ) : eval (s • x) Q = s ^ m * eval x Q := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hdeg : ∑ i ∈ β.support, β i = m := by
    have := hQ (mem_support_iff.mp hβ)
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-! ## Homogeneous expansions -/

/-- An absolutely convergent homogeneous expansion `h(x) = ∑_m G_m(x)` near the origin, with `G_m` homogeneous of degree `m`. -/
structure IsHomogExpansion (h : (Fin n → ℂ) → ℂ) (G : ℕ → Poly n) : Prop where
  homog : ∀ m, (G m).IsHomogeneous m
  sum : ∃ r > 0, ∀ x : Fin n → ℂ, ‖x‖ < r →
    Summable (fun m => ‖eval x (G m)‖) ∧ HasSum (fun m => eval x (G m)) (h x)

/-- Uniqueness of homogeneous expansions for functions equal near the origin. -/
theorem IsHomogExpansion.eq_of_eventuallyEq {h h' : (Fin n → ℂ) → ℂ} {G G' : ℕ → Poly n}
    (hG : IsHomogExpansion h G) (hG' : IsHomogExpansion h' G') (hh : h =ᶠ[𝓝 0] h') :
    G = G' := by
  obtain ⟨r, hr, hsum⟩ := hG.sum
  obtain ⟨r', hr', hsum'⟩ := hG'.sum
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hh
  funext m
  apply MvPolynomial.funext
  intro y
  set M := min (min r r') ρ with hM
  have hMpos : 0 < M := lt_min (lt_min hr hr') hρ
  have hy1 : 0 < ‖y‖ + 1 := by positivity
  have hc := coeff_eq_zero_of_hasSum_zero (c := fun k => eval y (G k) - eval y (G' k))
    (ε := M / (‖y‖ + 1)) (by positivity) (fun s hs => by
      have hsy : ‖s • y‖ < M := by
        rw [norm_smul]
        calc ‖s‖ * ‖y‖ ≤ M / (‖y‖ + 1) * ‖y‖ := by gcongr
          _ < M := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hy1]; nlinarith
      have h1 := (hsum (s • y) (lt_of_lt_of_le hsy ((min_le_left _ _).trans (min_le_left _ _)))).2
      have h2 := (hsum' (s • y) (lt_of_lt_of_le hsy ((min_le_left _ _).trans (min_le_right _ _)))).2
      rw [hball (by simpa using lt_of_lt_of_le hsy (min_le_right _ _))] at h1
      have h3 := h1.sub h2
      rw [sub_self] at h3
      convert h3 using 1
      funext k
      rw [eval_smul_of_isHomogeneous (hG.homog k), eval_smul_of_isHomogeneous (hG'.homog k)]
      ring)
  have := congrFun hc m
  simpa [sub_eq_zero] using this

lemma IsHomogExpansion.congr {h h' : (Fin n → ℂ) → ℂ} {G : ℕ → Poly n}
    (hG : IsHomogExpansion h G) (hh : h =ᶠ[𝓝 0] h') : IsHomogExpansion h' G := by
  refine ⟨hG.homog, ?_⟩
  obtain ⟨r, hr, hsum⟩ := hG.sum
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hh
  refine ⟨min r ρ, lt_min hr hρ, fun x hx => ?_⟩
  have h1 := hsum x (lt_of_lt_of_le hx (min_le_left _ _))
  rw [← hball (by simpa using lt_of_lt_of_le hx (min_le_right _ _))]
  exact h1

/-- A power series expansion gives homogeneous terms `G_m = P_m(x, …, x)`. -/
theorem isHomogExpansion_of_hasFPowerSeriesAt {h : (Fin n → ℂ) → ℂ}
    {P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ} (hP : HasFPowerSeriesAt h P 0) :
    IsHomogExpansion h (homogPoly P) := by
  refine ⟨isHomogeneous_homogPoly P, ?_⟩
  obtain ⟨R, hR⟩ := hP
  obtain ⟨r', hr'0, hr'R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos
  refine ⟨r', by exact_mod_cast hr'0, fun x hx => ⟨?_, ?_⟩⟩
  · have hsm := P.summable_norm_mul_pow (lt_of_lt_of_le hr'R hR.r_le)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hsm
    rw [eval_homogPoly]
    calc ‖P m (fun _ => x)‖ ≤ ‖P m‖ * ∏ _k : Fin m, ‖x‖ := (P m).le_opNorm _
      _ = ‖P m‖ * ‖x‖ ^ m := by simp
      _ ≤ ‖P m‖ * (r' : ℝ) ^ m := by gcongr
  · have hxR : x ∈ Metric.eball (0 : Fin n → ℂ) R := by
      rw [Metric.mem_eball]
      refine lt_trans ?_ hr'R
      rw [edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, dist_zero_right]
      exact hx
    have := hR.hasSum hxR
    simp only [zero_add] at this
    simpa [eval_homogPoly] using this

/-! ## Taylor series -/

open Classical in
/-- The homogeneous expansion of `h` at the origin, chosen from `AnalyticAt`; it is zero when `h` is not analytic. -/
def expansion (h : (Fin n → ℂ) → ℂ) : ℕ → Poly n :=
  if H : AnalyticAt ℂ h 0 then homogPoly H.choose else 0

lemma isHomogExpansion_expansion {h : (Fin n → ℂ) → ℂ} (H : AnalyticAt ℂ h 0) :
    IsHomogExpansion h (expansion h) := by
  rw [expansion, dif_pos H]
  exact isHomogExpansion_of_hasFPowerSeriesAt H.choose_spec

lemma expansion_eq {h : (Fin n → ℂ) → ℂ} {G : ℕ → Poly n} (H : AnalyticAt ℂ h 0)
    (hG : IsHomogExpansion h G) : expansion h = G :=
  (isHomogExpansion_expansion H).eq_of_eventuallyEq hG EventuallyEq.rfl

/-- The formal Taylor series of `h` at the origin: the coefficient of `x^α` is taken from the homogeneous part of degree `|α|`. -/
def taylorSeries0 (h : (Fin n → ℂ) → ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun α => coeff α (expansion h α.degree)

lemma coeff_taylorSeries0 (h : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (taylorSeries0 h) = coeff α (expansion h α.degree) := rfl

lemma taylorSeries0_eq {h : (Fin n → ℂ) → ℂ} {G : ℕ → Poly n} (H : AnalyticAt ℂ h 0)
    (hG : IsHomogExpansion h G) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (taylorSeries0 h) = coeff α (G α.degree) := by
  rw [coeff_taylorSeries0, expansion_eq H hG]

lemma norm_coeff_prod_X_le (m : ℕ) (s : Fin m → Fin n) (α : Fin n →₀ ℕ) :
    ‖coeff α (∏ k, (X (s k) : Poly n))‖ ≤ 1 := by
  classical
  have : (∏ k, (X (s k) : Poly n)) = monomial (∑ k, Finsupp.single (s k) 1) 1 := by
    rw [monomial_sum_one]; rfl
  rw [this, coeff_monomial]
  split_ifs <;> simp

lemma norm_coeff_homogPoly_le (P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ) (m : ℕ)
    (α : Fin n →₀ ℕ) : ‖coeff α (homogPoly P m)‖ ≤ (n : ℝ) ^ m * ‖P m‖ := by
  rw [homogPoly, coeff_sum]
  calc ‖∑ s : Fin m → Fin n, coeff α (C (P m (fun k => Pi.single (s k) 1)) * ∏ k, X (s k))‖
      ≤ ∑ s : Fin m → Fin n, ‖coeff α (C (P m (fun k => Pi.single (s k) 1)) * ∏ k, X (s k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _s : Fin m → Fin n, ‖P m‖ := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [coeff_C_mul, norm_mul]
        calc ‖P m (fun k => Pi.single (s k) 1)‖ * ‖coeff α (∏ k, (X (s k) : Poly n))‖
            ≤ ‖P m (fun k => Pi.single (s k) 1)‖ * 1 := by
              gcongr; exact norm_coeff_prod_X_le m s α
          _ ≤ ‖P m‖ * ∏ k, ‖(Pi.single (s k) (1 : ℂ) : Fin n → ℂ)‖ := by
              rw [mul_one]; exact (P m).le_opNorm _
          _ ≤ ‖P m‖ * 1 := by
              gcongr
              apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
              intro k _
              rw [pi_norm_le_iff_of_nonneg zero_le_one]
              intro j
              by_cases hj : j = s k
              · subst hj; simp
              · simp [hj]
          _ = ‖P m‖ := mul_one _
    _ = (n : ℝ) ^ m * ‖P m‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- The Taylor series converges. -/
lemma isConvergent_taylor0 (h : (Fin n → ℂ) → ℂ) : IsConvergent (taylorSeries0 h) := by
  by_cases H : AnalyticAt ℂ h 0
  · obtain ⟨R, hR⟩ := H.choose_spec
    obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hR.r_pos
    obtain ⟨K, hK, hPK⟩ := H.choose.norm_le_div_pow_of_pos_of_lt_radius (by exact_mod_cast hr0)
      (lt_of_lt_of_le hrR hR.r_le)
    refine ⟨K, n / r, by positivity, fun α => ?_⟩
    rw [coeff_taylorSeries0, expansion, dif_pos H]
    refine (norm_coeff_homogPoly_le _ _ α).trans ?_
    have hr : (0 : ℝ) < r := by exact_mod_cast hr0
    calc (n : ℝ) ^ α.degree * ‖H.choose α.degree‖ ≤ (n : ℝ) ^ α.degree * (K / r ^ α.degree) := by
          gcongr; exact hPK _
      _ = K * (n / r) ^ α.degree := by rw [div_pow]; ring
  · refine ⟨0, 0, le_rfl, fun α => ?_⟩
    simp [coeff_taylorSeries0, expansion, dif_neg H]

/-- The Taylor series of `h` at the origin, as an element of `ℂ{x}`. -/
def taylorConv0 (h : (Fin n → ℂ) → ℂ) : ConvSeries n := ⟨taylorSeries0 h, isConvergent_taylor0 h⟩

@[simp] lemma taylorConv0_coe (h : (Fin n → ℂ) → ℂ) :
    ((taylorConv0 h : ConvSeries n) : MvPowerSeries (Fin n) ℂ) = taylorSeries0 h := rfl

/-- The Taylor series depends only on the germ at the origin. -/
lemma taylorSeries0_congr {h h' : (Fin n → ℂ) → ℂ} (hh : h =ᶠ[𝓝 0] h') : taylorSeries0 h = taylorSeries0 h' := by
  by_cases H : AnalyticAt ℂ h 0
  · have H' : AnalyticAt ℂ h' 0 := H.congr hh
    ext α
    rw [taylorSeries0_eq H' ((isHomogExpansion_expansion H).congr hh)]
    rfl
  · have H' : ¬ AnalyticAt ℂ h' 0 := fun H' => H (H'.congr hh.symm)
    ext α
    simp [coeff_taylorSeries0, expansion, dif_neg H, dif_neg H']

/-! ## Operations on homogeneous expansions -/

theorem IsHomogExpansion.add {h₁ h₂ : (Fin n → ℂ) → ℂ} {G₁ G₂ : ℕ → Poly n}
    (hG₁ : IsHomogExpansion h₁ G₁) (hG₂ : IsHomogExpansion h₂ G₂) :
    IsHomogExpansion (fun x => h₁ x + h₂ x) (fun m => G₁ m + G₂ m) := by
  refine ⟨fun m => (hG₁.homog m).add (hG₂.homog m), ?_⟩
  obtain ⟨r₁, hr₁, hs₁⟩ := hG₁.sum
  obtain ⟨r₂, hr₂, hs₂⟩ := hG₂.sum
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun x hx => ?_⟩
  obtain ⟨a₁, b₁⟩ := hs₁ x (lt_of_lt_of_le hx (min_le_left _ _))
  obtain ⟨a₂, b₂⟩ := hs₂ x (lt_of_lt_of_le hx (min_le_right _ _))
  simp only [map_add]
  exact ⟨(a₁.add a₂).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _),
    b₁.add b₂⟩

theorem IsHomogExpansion.mul {h₁ h₂ : (Fin n → ℂ) → ℂ} {G₁ G₂ : ℕ → Poly n}
    (hG₁ : IsHomogExpansion h₁ G₁) (hG₂ : IsHomogExpansion h₂ G₂) :
    IsHomogExpansion (fun x => h₁ x * h₂ x)
      (fun m => ∑ p ∈ Finset.antidiagonal m, G₁ p.1 * G₂ p.2) := by
  refine ⟨fun m => ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp]
    exact (hG₁.homog _).mul (hG₂.homog _)
  obtain ⟨r₁, hr₁, hs₁⟩ := hG₁.sum
  obtain ⟨r₂, hr₂, hs₂⟩ := hG₂.sum
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun x hx => ?_⟩
  obtain ⟨a₁, b₁⟩ := hs₁ x (lt_of_lt_of_le hx (min_le_left _ _))
  obtain ⟨a₂, b₂⟩ := hs₂ x (lt_of_lt_of_le hx (min_le_right _ _))
  have heval : ∀ m, eval x (∑ p ∈ Finset.antidiagonal m, G₁ p.1 * G₂ p.2) =
      ∑ p ∈ Finset.antidiagonal m, eval x (G₁ p.1) * eval x (G₂ p.2) := by
    intro m; simp only [map_sum, map_mul]
  simp only [heval]
  have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (f := fun m => eval x (G₁ m)) (g := fun m => eval x (G₂ m)) a₁ a₂
  refine ⟨hn, ?_⟩
  have hsum := hn.of_norm
  have e : h₁ x * h₂ x =
      ∑' m, ∑ p ∈ Finset.antidiagonal m, eval x (G₁ p.1) * eval x (G₂ p.2) := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (f := fun m => eval x (G₁ m)) (g := fun m => eval x (G₂ m)) a₁ a₂, b₁.tsum_eq, b₂.tsum_eq]
  rw [e]
  exact hsum.hasSum

/-- For a polynomial function, the homogeneous expansion consists of its homogeneous components. -/
theorem isHomogExpansion_eval (Q : Poly n) :
    IsHomogExpansion (fun x => eval x Q) (fun m => homogeneousComponent m Q) := by
  refine ⟨fun m => homogeneousComponent_isHomogeneous m Q, 1, one_pos, fun x _ => ⟨?_, ?_⟩⟩
  · apply summable_of_ne_finset_zero (s := Finset.range (Q.totalDegree + 1))
    intro m hm
    rw [Finset.mem_range, not_lt] at hm
    rw [homogeneousComponent_eq_zero m Q (by omega), map_zero, norm_zero]
  · have : HasSum (fun m => eval x (homogeneousComponent m Q))
        (∑ m ∈ Finset.range (Q.totalDegree + 1), eval x (homogeneousComponent m Q)) :=
      hasSum_sum_of_ne_finset_zero (fun m hm => by
        rw [Finset.mem_range, not_lt] at hm
        show eval x (homogeneousComponent m Q) = 0
        rw [homogeneousComponent_eq_zero m Q (by omega), map_zero])
    rwa [← map_sum, sum_homogeneousComponent] at this

/-! ## Operations on Taylor series -/

lemma analyticAt_eval (Q : Poly n) (p : Fin n → ℂ) : AnalyticAt ℂ (fun x => eval x Q) p :=
  AnalyticOnNhd.eval_mvPolynomial Q p (Set.mem_univ p)

theorem taylorSeries0_add {h₁ h₂ : (Fin n → ℂ) → ℂ} (H₁ : AnalyticAt ℂ h₁ 0) (H₂ : AnalyticAt ℂ h₂ 0) :
    taylorSeries0 (fun x => h₁ x + h₂ x) = taylorSeries0 h₁ + taylorSeries0 h₂ := by
  ext α
  rw [taylorSeries0_eq (h := fun x => h₁ x + h₂ x) (H₁.add H₂) ((isHomogExpansion_expansion H₁).add (isHomogExpansion_expansion H₂)),
    map_add, coeff_add, coeff_taylorSeries0, coeff_taylorSeries0]

theorem taylorSeries0_mul {h₁ h₂ : (Fin n → ℂ) → ℂ} (H₁ : AnalyticAt ℂ h₁ 0) (H₂ : AnalyticAt ℂ h₂ 0) :
    taylorSeries0 (fun x => h₁ x * h₂ x) = taylorSeries0 h₁ * taylorSeries0 h₂ := by
  classical
  set G₁ := expansion h₁
  set G₂ := expansion h₂
  have hG₁ := isHomogExpansion_expansion H₁
  have hG₂ := isHomogExpansion_expansion H₂
  ext α
  rw [taylorSeries0_eq (h := fun x => h₁ x * h₂ x) (H₁.mul H₂) (hG₁.mul hG₂), MvPowerSeries.coeff_mul, coeff_sum]
  simp_rw [MvPolynomial.coeff_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  rw [coeff_taylorSeries0, coeff_taylorSeries0]
  rw [Finset.sum_eq_single (q.1.degree, q.2.degree)]
  · intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    have hdeg : p.1 + p.2 = q.1.degree + q.2.degree := by rw [hp, ← hq, map_add]
    by_cases h1 : q.1.degree = p.1
    · have h2 : q.2.degree ≠ p.2 := by
        intro h2; exact hne (Prod.ext h1.symm h2.symm)
      rw [(hG₂.homog p.2).coeff_eq_zero h2, mul_zero]
    · rw [(hG₁.homog p.1).coeff_eq_zero h1, zero_mul]
  · intro hn
    exfalso; apply hn
    rw [Finset.mem_antidiagonal, ← map_add, hq]

theorem taylorSeries0_eval (Q : Poly n) : taylorSeries0 (fun x => eval x Q) = (Q : MvPowerSeries (Fin n) ℂ) := by
  ext α
  rw [taylorSeries0_eq (analyticAt_eval Q 0) (isHomogExpansion_eval Q), coeff_homogeneousComponent,
    if_pos rfl, MvPolynomial.coeff_coe]

/-- An analytic function with zero Taylor series vanishes near the origin. -/
theorem eventuallyEq_zero_of_taylor0_eq_zero {h : (Fin n → ℂ) → ℂ} (H : AnalyticAt ℂ h 0)
    (h0 : taylorSeries0 h = 0) : h =ᶠ[𝓝 0] 0 := by
  have hG := isHomogExpansion_expansion H
  have hz : ∀ m, expansion h m = 0 := by
    intro m
    ext β
    by_cases hβ : β.degree = m
    · subst hβ
      have := congrArg (MvPowerSeries.coeff β) h0
      rwa [coeff_taylorSeries0, map_zero] at this
    · rw [(hG.homog m).coeff_eq_zero hβ, coeff_zero]
  obtain ⟨r, hr, hs⟩ := hG.sum
  rw [Filter.EventuallyEq, Metric.eventually_nhds_iff]
  refine ⟨r, hr, fun {x} hx => ?_⟩
  have := (hs x (by simpa using hx)).2
  simp only [hz, map_zero] at this
  exact this.unique hasSum_zero

/-! ## Sum functions of convergent power series -/

lemma card_monoIdx (α : Fin n →₀ ℕ) : Fintype.card (Σ i : Fin n, Fin (α i)) = α.degree := by
  simp [Fintype.card_sigma, Finsupp.degree_eq_sum]

/-- An `m`-linear map whose diagonal is `x^α` when `|α| = m`, and zero otherwise. -/
def monoML (α : Fin n →₀ ℕ) (m : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) ℂ :=
  if h : α.degree = m then
    ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Σ i : Fin n, Fin (α i)) ℂ).compContinuousLinearMap
      (fun ij => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ij.1)).domDomCongr
      (Fintype.equivFinOfCardEq ((card_monoIdx α).trans h))
  else 0

lemma monoML_apply (α : Fin n →₀ ℕ) (m : ℕ) (v : Fin m → Fin n → ℂ) :
    monoML α m v = if h : α.degree = m then
      ∏ ij : (Σ i : Fin n, Fin (α i)),
        v (Fintype.equivFinOfCardEq ((card_monoIdx α).trans h) ij) ij.1 else 0 := by
  unfold monoML
  split_ifs with h
  · simp [ContinuousMultilinearMap.domDomCongr_apply]
  · rfl

lemma monoML_diag {α : Fin n →₀ ℕ} {m : ℕ} (h : α.degree = m) (x : Fin n → ℂ) :
    monoML α m (fun _ => x) = ∏ i, x i ^ α i := by
  rw [monoML_apply, dif_pos h, Fintype.prod_sigma]
  simp

lemma norm_monoML_le (α : Fin n →₀ ℕ) (m : ℕ) : ‖monoML α m‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [monoML_apply, one_mul]
  split_ifs with h
  · set e := Fintype.equivFinOfCardEq ((card_monoIdx α).trans h)
    rw [norm_prod]
    calc ∏ ij : (Σ i : Fin n, Fin (α i)), ‖v (e ij) ij.1‖
        ≤ ∏ ij : (Σ i : Fin n, Fin (α i)), ‖v (e ij)‖ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun ij _ => norm_le_pi_norm _ _)
      _ = ∏ k, ‖v k‖ := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · rw [norm_zero]; exact Finset.prod_nonneg fun _ _ => norm_nonneg _

lemma card_finsuppAntidiag_le (m : ℕ) :
    ((Finset.univ : Finset (Fin n)).finsuppAntidiag m).card ≤ (2 ^ n) ^ m := by
  classical
  calc ((Finset.univ : Finset (Fin n)).finsuppAntidiag m).card
      ≤ (Finset.univ : Finset (Fin n → Fin (m + 1))).card := by
        refine Finset.card_le_card_of_injOn (fun α i => ⟨min (α i) m, by omega⟩)
          (fun _ _ => Finset.mem_univ _) ?_
        intro α hα β hβ hab
        have hle : ∀ γ ∈ ((Finset.univ : Finset (Fin n)).finsuppAntidiag m : Set (Fin n →₀ ℕ)),
            ∀ i, γ i ≤ m := by
          intro γ hγ i
          rw [Finset.mem_coe, Finset.mem_finsuppAntidiag] at hγ
          rw [← hγ.1]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        ext i
        have := congrArg Fin.val (congrFun hab i)
        simp only at this
        have h1 := hle α hα i
        have h2 := hle β hβ i
        omega
    _ = (m + 1) ^ n := by simp
    _ ≤ (2 ^ m) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self) n
    _ = (2 ^ n) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]

/-- The formal multilinear series associated with a convergent power series: `P_m = ∑_{|α| = m} c_α x^α`. -/
def convFML (F : MvPowerSeries (Fin n) ℂ) : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ :=
  fun m => ∑ α ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag m,
    MvPowerSeries.coeff α F • monoML α m

lemma radius_convFML_pos {F : MvPowerSeries (Fin n) ℂ} (hF : IsConvergent F) :
    0 < (convFML F).radius := by
  obtain ⟨K, R, hR, hK⟩ := hF
  have hK0 := IsConvergent.nonneg_const hK
  set q : ℝ := 2 ^ n * R + 1
  have hq : 0 < q := by positivity
  set r : NNReal := ⟨1 / q, by positivity⟩
  have hr : (0 : ENNReal) < r := ENNReal.coe_pos.2 (by
    rw [← NNReal.coe_pos]; show (0 : ℝ) < 1 / q; positivity)
  refine lt_of_lt_of_le hr (FormalMultilinearSeries.le_radius_of_bound _ K fun m => ?_)
  have hbound : ‖convFML F m‖ ≤ K * (2 ^ n * R) ^ m := by
    calc ‖convFML F m‖
        ≤ ∑ α ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag m,
            ‖MvPowerSeries.coeff α F • monoML α m‖ := norm_sum_le _ _
      _ ≤ ∑ _α ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag m, K * R ^ m := by
          refine Finset.sum_le_sum fun α hα => ?_
          rw [Finset.mem_finsuppAntidiag] at hα
          have hdeg : α.degree = m := by rw [Finsupp.degree_eq_sum]; exact hα.1
          rw [norm_smul]
          calc ‖MvPowerSeries.coeff α F‖ * ‖monoML α m‖ ≤ (K * R ^ α.degree) * 1 :=
                mul_le_mul (hK α) (norm_monoML_le α m) (norm_nonneg _) (by positivity)
            _ = K * R ^ m := by rw [hdeg, mul_one]
      _ = ((Finset.univ : Finset (Fin n)).finsuppAntidiag m).card * (K * R ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 ^ n) ^ m : ℕ) * (K * R ^ m) := by
          gcongr; exact_mod_cast card_finsuppAntidiag_le m
      _ = K * (2 ^ n * R) ^ m := by push_cast; ring
  calc ‖convFML F m‖ * (r : ℝ) ^ m ≤ K * (2 ^ n * R) ^ m * (1 / q) ^ m := by
        gcongr; exact le_of_eq rfl
    _ = K * (2 ^ n * R / q) ^ m := by rw [mul_assoc, ← mul_pow]; ring
    _ ≤ K * 1 := by
        gcongr
        apply pow_le_one₀ (by positivity)
        rw [div_le_one hq]; linarith
    _ = K := mul_one K

/-- The sum function `x ↦ ∑_α c_α x^α` of a convergent power series. -/
def sumFun (F : ConvSeries n) : (Fin n → ℂ) → ℂ := (convFML (F : MvPowerSeries (Fin n) ℂ)).sum

lemma hasFPowerSeriesAt_sumFun (F : ConvSeries n) :
    HasFPowerSeriesAt (sumFun F) (convFML (F : MvPowerSeries (Fin n) ℂ)) 0 :=
  ((convFML (F : MvPowerSeries (Fin n) ℂ)).hasFPowerSeriesOnBall
    (radius_convFML_pos (show IsConvergent (F : MvPowerSeries (Fin n) ℂ) from F.2))).hasFPowerSeriesAt

lemma analyticAt_sumFun (F : ConvSeries n) : AnalyticAt ℂ (sumFun F) 0 :=
  (hasFPowerSeriesAt_sumFun F).analyticAt

lemma homogPoly_convFML (F : MvPowerSeries (Fin n) ℂ) (m : ℕ) :
    homogPoly (convFML F) m = ∑ α ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag m,
      monomial α (MvPowerSeries.coeff α F) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_homogPoly, convFML, ContinuousMultilinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_finsuppAntidiag] at hα
  have hdeg : α.degree = m := by rw [Finsupp.degree_eq_sum]; exact hα.1
  rw [ContinuousMultilinearMap.smul_apply, monoML_diag hdeg, eval_monomial, smul_eq_mul,
    Finsupp.prod_fintype]
  · simp

/-- The Taylor series of the sum function is the original power series. -/
theorem taylorSeries0_sumFun (F : ConvSeries n) : taylorSeries0 (sumFun F) = F := by
  classical
  ext α
  rw [taylorSeries0_eq (analyticAt_sumFun F) (isHomogExpansion_of_hasFPowerSeriesAt
    (hasFPowerSeriesAt_sumFun F)), homogPoly_convFML, coeff_sum]
  rw [Finset.sum_eq_single α]
  · rw [coeff_monomial, if_pos rfl]
  · intro β _ hβ; rw [coeff_monomial, if_neg hβ]
  · intro hα; exfalso; apply hα
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [Finsupp.degree_eq_sum], by simp⟩

end Yau
