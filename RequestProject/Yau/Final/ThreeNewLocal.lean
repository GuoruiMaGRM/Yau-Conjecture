import RequestProject.Yau.Final.AGV148

/-!
# From AGV, Theorem 14.8 to Lemma 3.4 and the main theorem

Lemma 3.4 assumes local conditions at the origin for `f_t = f+tq`:
isolatedness, critical value zero, and constant local Milnor number.
The formalization first relates these conditions to the global formulation.
For a lower-degree perturbation, the polynomial Jacobian quotient retains its
dimension. If the entire dimension is already realized by the local Milnor
algebra at zero, another critical point would force a strict dimension drop.

The proved versality construction and AGV, Theorem 14.8 then give `q ∈ J_f`.
This connects Lemma 3.4 to Corollary 3.5, Theorem 3.6, and Section 4.
The file also proves equivalence with a polynomial-only formulation of Lemma 3.4.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ## 1. Powers of coordinates in `ℂ{x}` -/

/-- Suppose `ψ : ℂ[x] → R` sends polynomials with nonzero constant term to units and `R/I` is finite dimensional. Then `ψ(x_i)^{dim R/I} ∈ I`. Factor the minimal polynomial as `X^k Q` with `Q(0) ≠ 0`, deduce nilpotence, and apply Cayley–Hamilton. -/
theorem X_pow_finrank_mem_of_unit {R : Type*} [CommRing R] [Algebra ℂ R]
    (ψ : Poly n →ₐ[ℂ] R) (hψ : ∀ u, eval 0 u ≠ 0 → IsUnit (ψ u))
    (I : Ideal R) [Module.Finite ℂ (R ⧸ I)] (i : Fin n) :
    ψ (X i) ^ Module.finrank ℂ (R ⧸ I) ∈ I := by
  obtain ⟨a, ha⟩ : ∃ a : R ⧸ I, a = Ideal.Quotient.mk I (ψ (X i)) := ⟨_, rfl⟩
  have hint : IsIntegral ℂ a := IsIntegral.of_finite ℂ a
  have hP0 : minpoly ℂ a ≠ 0 := minpoly.ne_zero hint
  obtain ⟨Q, hPQ, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly ℂ a) hP0 0
  generalize (minpoly ℂ a).rootMultiplicity 0 = k at hPQ
  have hQ0 : Q.eval 0 ≠ 0 := by
    intro h
    apply hndvd
    rw [map_zero, sub_zero, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact h
  have hunit : IsUnit (ψ (Polynomial.aeval (X i : Poly n) Q)) := by
    apply hψ
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
    simpa [Polynomial.eval₂_eq_eval_map] using hQ0
  have hQa : IsUnit (Polynomial.aeval a Q) := by
    have : Polynomial.aeval a Q =
        (Ideal.Quotient.mkₐ ℂ I) (ψ (Polynomial.aeval (X i : Poly n) Q)) := by
      rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, ha]
      rfl
    rw [this]
    exact hunit.map _
  have hak : a ^ k = 0 := by
    have h := minpoly.aeval ℂ a
    rw [hPQ] at h
    simp only [map_mul, map_pow, Polynomial.aeval_X, map_zero, sub_zero] at h
    exact (hQa.mul_left_eq_zero).1 h
  have hnil : IsNilpotent (LinearMap.mulLeft ℂ a) := by
    refine ⟨k, ?_⟩
    rw [LinearMap.pow_mulLeft, hak, LinearMap.mulLeft_zero_eq_zero]
  have hCH := LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℂ a)
  rw [hnil.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X, LinearMap.pow_mulLeft] at hCH
  have hfin : a ^ Module.finrank ℂ (R ⧸ I) = 0 := by
    have := congrArg (fun L : (R ⧸ I) →ₗ[ℂ] (R ⧸ I) => L 1) hCH
    simpa using this
  rw [ha, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hfin
  exact hfin

set_option synthInstance.maxHeartbeats 200000 in
/-- If `ℂ{x}/I` is finite dimensional, each coordinate to the power `dim ℂ{x}/I` belongs to `I`. -/
lemma X_pow_finrank_mem_conv (I : Ideal (ConvSeries n)) [Module.Finite ℂ (ConvSeries n ⧸ I)]
    (i : Fin n) : polyToConv (X i) ^ Module.finrank ℂ (ConvSeries n ⧸ I) ∈ I :=
  X_pow_finrank_mem_of_unit polyToConv (fun _ hu => isUnit_polyToConv hu) I i

/-! ## 2. Constant local Milnor number excludes other critical points -/

set_option synthInstance.maxHeartbeats 200000 in
/-- For homogeneous `q` of degree `e < d`, equality `μ(f+q,0) = μ(f,0)` implies that every critical point of `f+q` is the origin. -/
theorem eq_zero_of_crit_of_milnorNumber_eq {w : Fin n → ℕ} {d e : ℕ} {f q : Poly n}
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d) (hcrit : HasIsolatedCriticalPoint f)
    (hq : q.IsWeightedHomogeneous w e) (he : e < d)
    (hμ : milnorNumber (f + q) = milnorNumber f)
    (x : Fin n → ℂ) (hx : ∀ i, eval x (pderiv i (f + q)) = 0) : x = 0 := by
  classical
  by_contra hx0
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h; push_neg at h; exact hx0 (funext h)
  have hz : ∀ y : Fin n → ℂ, (∀ i, eval y (pderiv i f) = 0) → y = 0 :=
    critical_eq_zero_of_isolated hw hf hcrit.2
  have hpowf := exists_pow_X_mem_jac hz
  have hiso : IsIsolatedSingularity f := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit
  have hwd := w_lt_of_hasIsolatedCriticalPoint hw hf hcrit
  obtain ⟨hiso', hrank⟩ := finrank_milnorAlgebra_add hw hf hiso hwd hq he
  haveI : Module.Finite ℂ (Poly n ⧸ jacobianIdeal f) := finite_quotient_of_pow_X_mem _ hpowf
  haveI : Module.Finite ℂ (Poly n ⧸ jacobianIdeal (f + q)) := hiso'
  have hMf : Module.finrank ℂ (Poly n ⧸ jacobianIdeal f) = milnorNumber f :=
    (quotientEquivConv hpowf).toLinearEquiv.finrank_eq
  -- The Milnor number of `f` is positive: the partial derivatives vanish at the origin, so `J_f` is proper.
  have hJne : jacobianIdeal f ≠ ⊤ := by
    intro htop
    have h1 : (1 : Poly n) ∈ jacobianIdeal f := htop ▸ Submodule.mem_top
    have := mem_jac_eval_zero hcrit.1 h1
    simp at this
  have hpos : 0 < milnorNumber f := by
    rw [← hMf]
    haveI : Nontrivial (Poly n ⧸ jacobianIdeal f) := Ideal.Quotient.nontrivial_iff.mpr hJne
    exact Module.finrank_pos
  set g := f + q with hg
  haveI : Module.Free ℂ (ConvSeries n ⧸ convIdeal (jacobianIdeal g)) :=
    Module.Free.of_divisionRing ℂ _
  haveI : Module.Finite ℂ (ConvSeries n ⧸ convIdeal (jacobianIdeal g)) :=
    Module.finite_of_finrank_pos (show 0 < milnorNumber g by rw [hμ]; exact hpos)
  set N := milnorNumber g with hN
  have hXN : ∀ i, polyToConv (X i) ^ N ∈ convIdeal (jacobianIdeal g) :=
    fun i => X_pow_finrank_mem_conv _ i
  set I' : Ideal (Poly n) := jacobianIdeal g ⊔ Ideal.span (Set.range fun i => (X i : Poly n) ^ N)
    with hI'
  have hI'X : ∀ i, ∃ M : ℕ, (X i : Poly n) ^ M ∈ I' :=
    fun i => ⟨N, Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hconv : convIdeal I' = convIdeal (jacobianIdeal g) := by
    rw [convIdeal, hI', Ideal.map_sup, Ideal.map_span]
    refine le_antisymm (sup_le le_rfl ?_) le_sup_left
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa using hXN i
  have hrank' : Module.finrank ℂ (Poly n ⧸ I') = N :=
    ((quotientEquivConv hI'X).toLinearEquiv.trans
      (Ideal.quotientEquivAlgOfEq ℂ hconv).toLinearEquiv).finrank_eq
  -- `J_g ⊊ I'`
  have hle : jacobianIdeal g ≤ I' := le_sup_left
  have hnot : (X j : Poly n) ^ N ∉ jacobianIdeal g := by
    intro hmem
    have := mem_jac_eval_zero hx hmem
    simp only [map_pow, eval_X] at this
    exact hj (pow_eq_zero_iff'.1 this).1
  -- The quotient dimension strictly decreases.
  set ψ := (Ideal.Quotient.factorₐ ℂ hle).toLinearMap with hψ
  have hsurj : Function.Surjective ψ := Ideal.Quotient.factor_surjective hle
  have hker : LinearMap.ker ψ ≠ ⊥ := by
    intro hbot
    have hmk : Ideal.Quotient.mk (jacobianIdeal g) ((X j : Poly n) ^ N) ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, hψ, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply,
        Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
    rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmk
    exact hnot hmk
  have hdim := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hrank'] at hdim
  have hkpos : 0 < Module.finrank ℂ (LinearMap.ker ψ) :=
    Nat.pos_of_ne_zero fun h => hker (Submodule.finrank_eq_zero.1 h)
  rw [hrank, hMf, ← hμ] at hdim
  omega

/-- The differential of a polynomial function vanishes if and only if all its partial derivatives vanish there. -/
lemma fderiv_eval_eq_zero_iff (P : Poly n) (x : Fin n → ℂ) :
    fderiv ℂ (fun x => eval x P) x = 0 ↔ ∀ i, eval x (pderiv i P) = 0 := by
  rw [(hasFDerivAt_eval P x).fderiv]
  constructor
  · intro h0 i
    have := congrArg (fun L => L (Pi.single i 1)) h0
    simpa [evalDeriv_apply, Pi.single_apply] using this
  · intro h0
    ext v
    simp [evalDeriv_apply, h0]

/-! ## 3. Local and global formulations of Lemma 3.4 -/

/-- The global formulation implies the local formulation stated in the paper. -/
theorem lemma34For_of_globalLemma34For {n : ℕ} (h : GlobalLemma34For n) : Lemma34For n := by
  intro w d f hw hf hcrit hf0 q e hq he hfam
  apply h w d f hw hf hcrit hf0 q e hq he
  filter_upwards [hfam] with t ⟨hiso, hval, hμ⟩
  have hμ' : milnorNumber (f + C t * q) = milnorNumber f := by
    rwa [localMilnorNumber_eval_zero, localMilnorNumber_eval_zero] at hμ
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, hval, hμ'⟩
  · exact eq_zero_of_crit_of_milnorNumber_eq hw hf hcrit (hq.C_mul t) he hμ' x hx
  · rintro rfl
    exact (fderiv_eval_eq_zero_iff _ 0).1 hiso.1

/-- The local and global formulations of Lemma 3.4 are equivalent for a fixed number of variables. -/
theorem lemma34For_iff_globalLemma34For (n : ℕ) : Lemma34For n ↔ GlobalLemma34For n :=
  ⟨globalLemma34For_of_lemma34For, lemma34For_of_globalLemma34For⟩

/-! ## 4. Deriving Lemma 3.4 from AGV, Theorem 14.8 -/

/-- The fixed-origin first-order Jacobian-ideal conclusion, using the stratum theorem only in `n` variables. -/
theorem corollary35_fixed_origin_of_varchenkoTheoremFor (hV : VarchenkoTheoremFor n) {w : Fin n → ℕ} {d : ℕ} {f : Poly n}
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
  obtain ⟨ε, hε0, hε⟩ := hV w d f hw hf hcrit hf0 μ β hβ
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

/-- The `n`-variable stratum hypothesis implies the local formulation of Lemma 3.4 in `n` variables. -/
theorem lemma34For_of_varchenkoTheoremFor (hV : VarchenkoTheoremFor n) : Lemma34For n :=
  lemma34For_of_globalLemma34For fun _ _ _ hw hf hcrit hf0 _ _ hq he hfam =>
    corollary35_fixed_origin_of_varchenkoTheoremFor hV hw hf hcrit hf0 hq he hfam

/-- AGV, Theorem 14.8 implies Lemma 3.4. Proved versality writes `f+tq = F_{γ(t)} ∘ Φ_t`; the stratum theorem forces the low-degree parameters to vanish. Differentiate and take the degree-`e` component to obtain `q ∈ J`. The local-to-global lemma supplies the hypotheses of the fixed-origin construction. -/
theorem lemma34For_of_agv148 (hA : AGVTheorem148For n) : Lemma34For n :=
  lemma34For_of_varchenkoTheoremFor (varchenkoTheoremFor_of_AGV hA)

/-- Lemma 3.4 for every number of variables, assuming AGV, Theorem 14.8 for `n ≥ 2` and using the direct proofs for `n ≤ 1`. -/
theorem lemma34_of_agv148 (hA : ∀ m, 2 ≤ m → AGVTheorem148For m) (n : ℕ) : Lemma34For n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact lemma34_zero_variables
    · exact lemma34_one_variable
  · exact lemma34For_of_agv148 (hA n hn)

/-- The main theorem of the accompanying paper, following Lemma 3.4, Corollary 3.5, Theorem 3.6, and Section 4, with AGV, Theorem 14.8 for `n ≥ 2` as the explicit hypothesis. -/
theorem yau_conjecture_of_agv148 (hA : ∀ m, 2 ≤ m → AGVTheorem148For m) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture_of_lemma34 (fun m _ => lemma34_of_agv148 hA m) w d f hw hf hcrit k hk δ hδ

/-! ## 5. A polynomial-only formulation of Lemma 3.4 -/

/-- Scaling identity: if `λ^{d-e} = t`, then `∂_i(f+tq)(λ^w · x) = λ^{d-w_i} ∂_i(f+q)(x)`. -/
lemma eval_scale_pderiv_add {w : Fin n → ℕ} {d e : ℕ} {f q : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hq : q.IsWeightedHomogeneous w e) (he : e ≤ d)
    {l t : ℂ} (hl : l ^ (d - e) = t) (x : Fin n → ℂ) (i : Fin n) :
    eval (fun j => l ^ w j * x j) (pderiv i (f + C t * q)) =
      l ^ (d - w i) * eval x (pderiv i (f + q)) := by
  have hCq : pderiv i (C t * q) = C t * pderiv i q := by
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
  rw [map_add, hCq, map_add, map_add, map_mul, eval_C, eval_scale (pderiv_isWH hf i).1, map_add,
    mul_add]
  congr 1
  rcases lt_or_ge e (w i) with h | h
  · rw [pderiv_eq_zero_of_lt hq i h]; simp
  · rw [eval_scale (pderiv_isWH hq i).1, ← hl, ← mul_assoc, ← pow_add]
    congr 2
    omega

/-- The algebraic formulation of Lemma 3.4: for homogeneous `q` of degree less than `d` with `q(0)=0`, if `f+q` has no critical point other than the origin, then `q ∈ J_f`. -/
def AlgebraicLemma34For (n : ℕ) : Prop :=
  ∀ (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (q : Poly n) (e : ℕ), q.IsWeightedHomogeneous w e → e < d → eval 0 q = 0 →
    (∀ x : Fin n → ℂ, (∀ i, eval x (pderiv i (f + q)) = 0) → x = 0) →
    q ∈ jacobianIdeal f

/-- The algebraic formulation implies the global formulation by scaling a critical point of `f+q` to one of `f+tq`, with nonzero `t`. -/
theorem globalLemma34For_of_algebraicLemma34For {n : ℕ} (h : AlgebraicLemma34For n) :
    GlobalLemma34For n := by
  intro w d f hw hf hcrit hf0 q e hq he hfam
  obtain ⟨t, ⟨hz, hval, -⟩, ht0⟩ := exists_ne_zero_of_eventually_nhds hfam
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq t (by omega : 0 < d - e)
  have hl0 : l ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega)] at hl; exact ht0 hl.symm
  have hq0 : eval 0 q = 0 := by
    rw [map_add, map_mul, eval_C, hf0, zero_add] at hval
    exact (mul_eq_zero.1 hval).resolve_left ht0
  refine h w d f hw hf hcrit hf0 q e hq he hq0 fun x hx => ?_
  have hy := (hz fun j => l ^ w j * x j).1 fun i => by
    rw [eval_scale_pderiv_add hf hq he.le hl, hx i, mul_zero]
  funext j
  have := congrFun hy j
  simpa [hl0] using this

set_option synthInstance.maxHeartbeats 200000 in
/-- The global formulation implies the algebraic formulation: scaling excludes other critical points for `f+tq`, the global dimension count and Nullstellensatz give criticality at zero, and the Milnor numbers agree. -/
theorem algebraicLemma34For_of_globalLemma34For {n : ℕ} (h : GlobalLemma34For n) :
    AlgebraicLemma34For n := by
  intro w d f hw hf hcrit hf0 q e hq he hq0 hcritq
  apply h w d f hw hf hcrit hf0 q e hq he
  refine Eventually.of_forall fun t => ?_
  have hz : ∀ y : Fin n → ℂ, (∀ i, eval y (pderiv i (f + C t * q)) = 0) → y = 0 := by
    intro y hy
    rcases eq_or_ne t 0 with rfl | ht0
    · simp only [map_zero, zero_mul, add_zero] at hy
      exact critical_eq_zero_of_isolated hw hf hcrit.2 y hy
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq t (by omega : 0 < d - e)
    have hl0 : l ≠ 0 := by
      rintro rfl; rw [zero_pow (by omega)] at hl; exact ht0 hl.symm
    set x : Fin n → ℂ := fun j => (l ^ w j)⁻¹ * y j with hx
    have hyx : (fun j => l ^ w j * x j) = y := by
      funext j; simp [hx, hl0]
    have hx0 : x = 0 := hcritq x fun i => by
      have h1 := eval_scale_pderiv_add hf hq he.le hl x i
      rw [hyx, hy i] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ hl0)
    rw [← hyx, hx0]; funext j; simp
  -- Dimension count: `dim ℂ[x]/J_{f+tq} = dim ℂ[x]/J_f`.
  have hiso : IsIsolatedSingularity f := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit
  have hwd := w_lt_of_hasIsolatedCriticalPoint hw hf hcrit
  obtain ⟨hiso', hrank⟩ := finrank_milnorAlgebra_add hw hf hiso hwd (hq.C_mul t) he
  have hpowf := exists_pow_X_mem_jac (critical_eq_zero_of_isolated hw hf hcrit.2)
  have hpowg := exists_pow_X_mem_jac hz
  haveI : Module.Finite ℂ (Poly n ⧸ jacobianIdeal f) := finite_quotient_of_pow_X_mem _ hpowf
  have hJne : jacobianIdeal f ≠ ⊤ := by
    intro htop
    have h1 : (1 : Poly n) ∈ jacobianIdeal f := htop ▸ Submodule.mem_top
    have := mem_jac_eval_zero hcrit.1 h1
    simp at this
  have hpos : 0 < Module.finrank ℂ (Poly n ⧸ jacobianIdeal f) := by
    haveI : Nontrivial (Poly n ⧸ jacobianIdeal f) := Ideal.Quotient.nontrivial_iff.mpr hJne
    exact Module.finrank_pos
  -- The origin is a critical point of `f+tq`, by the Nullstellensatz.
  have hrank' : Module.finrank ℂ (Poly n ⧸ jacobianIdeal (f + C t * q)) =
      Module.finrank ℂ (Poly n ⧸ jacobianIdeal f) := hrank
  have hJgne : jacobianIdeal (f + C t * q) ≠ ⊤ := by
    intro htop
    have : Module.finrank ℂ (Poly n ⧸ jacobianIdeal (f + C t * q)) = 0 := by
      rw [htop]
      haveI : Subsingleton (Poly n ⧸ (⊤ : Ideal (Poly n))) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    omega
  have hcrit0 : ∀ i, eval 0 (pderiv i (f + C t * q)) = 0 := by
    obtain ⟨y, hy⟩ : ∃ y : Fin n → ℂ, y ∈ zeroLocus ℂ (jacobianIdeal (f + C t * q)) := by
      by_contra hne
      push_neg at hne
      apply hJgne
      have hmem : (1 : Poly n) ∈ vanishingIdeal ℂ (zeroLocus ℂ (jacobianIdeal (f + C t * q))) := by
        rw [mem_vanishingIdeal_iff]
        intro x hx
        exact absurd hx (hne x)
      rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
      obtain ⟨N, hN⟩ := hmem
      rw [one_pow] at hN
      exact (Ideal.eq_top_iff_one _).2 hN
    have hyc : ∀ i, eval y (pderiv i (f + C t * q)) = 0 := fun i => by
      rw [mem_zeroLocus_iff] at hy
      exact hy _ (Ideal.subset_span ⟨i, rfl⟩)
    have := hz y hyc
    subst this
    exact hyc
  refine ⟨fun y => ⟨hz y, fun hy => hy ▸ hcrit0⟩, ?_, ?_⟩
  · rw [map_add, map_mul, eval_C, hf0, hq0, mul_zero, add_zero]
  · have h1 : Module.finrank ℂ (Poly n ⧸ jacobianIdeal (f + C t * q)) =
        milnorNumber (f + C t * q) := (quotientEquivConv hpowg).toLinearEquiv.finrank_eq
    have h2 : Module.finrank ℂ (Poly n ⧸ jacobianIdeal f) = milnorNumber f :=
      (quotientEquivConv hpowf).toLinearEquiv.finrank_eq
    rw [← h1, ← h2, hrank']

/-- The local, global, and polynomial-only formulations of Lemma 3.4 are equivalent for a fixed number of variables. -/
theorem lemma34For_iff_algebraicLemma34For (n : ℕ) : Lemma34For n ↔ AlgebraicLemma34For n :=
  ⟨fun h => algebraicLemma34For_of_globalLemma34For (globalLemma34For_of_lemma34For h),
    fun h => lemma34For_of_globalLemma34For (globalLemma34For_of_algebraicLemma34For h)⟩

/-- The main theorem under the polynomial-only formulation of Lemma 3.4 for `n ≥ 2`. -/
theorem yau_conjecture_of_algebraic_lemma34 (hP : ∀ m, 2 ≤ m → AlgebraicLemma34For m) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture_of_lemma34 (fun m hm => (lemma34For_iff_algebraicLemma34For m).2 (hP m hm)) w d f hw hf hcrit k hk δ hδ

end Yau
