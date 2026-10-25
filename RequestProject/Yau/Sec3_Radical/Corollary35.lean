import RequestProject.Yau.Analytic.LocalMilnor
import RequestProject.Yau.Sec3_Radical.MilnorConstancy

/-!
# Monomial-basis deformations and the first-order Jacobian-ideal conclusion

Choose homogeneous monomials whose classes form a basis of the Milnor algebra
and define `F_s = f + ∑ s_j φ_j`. The stratum hypothesis forces the parameters
of degree less than `d` to vanish along a `μ`-constant zero-critical-value family.
Differentiate the right-equivalence identity, pass to Taylor series, and take
the appropriate weighted homogeneous component to obtain `q ∈ J_f`.
This is the analytic argument of Lemma 3.4. Corollary 3.5 applies it to `q=a²`.

This file also formulates a general moving-critical-point consequence using
`VersalityTheorem` as a hypothesis. The main theorem uses the proved construction
for fixed-origin linear families in `Versality/FixedPoint.lean` instead.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ## 1. Monomial-basis miniversal deformations -/

/-- The classes of the monomials `x^{β_j}` form a basis of `ℂ[x]/J_f`. Lemma A.1 identifies this with a basis of the analytic Milnor algebra in the isolated weighted homogeneous case. -/
def IsMonomialBasis (f : Poly n) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ)) : Prop :=
  LinearIndependent ℂ (fun j => Ideal.Quotient.mk (jacobianIdeal f) (monomial (β j) (1 : ℂ))) ∧
    Submodule.span ℂ (Set.range fun j =>
      Ideal.Quotient.mk (jacobianIdeal f) (monomial (β j) (1 : ℂ))) = ⊤

/-- The polynomial `f + ∑_j s_j x^{β_j}` defining the miniversal deformation. -/
def miniversalPoly (f : Poly n) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ)) (s : Fin μ → ℂ) : Poly n :=
  f + ∑ j, monomial (β j) (s j)

/-- The miniversal deformation regarded as a function of `x`. -/
def miniversalDeformation (f : Poly n) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ)) (s : Fin μ → ℂ) :
    (Fin n → ℂ) → ℂ :=
  fun x => eval x (miniversalPoly f β s)

/-- A finite-dimensional Milnor algebra has a basis consisting of monomial classes, since monomials span the quotient. -/
theorem exists_monomialBasis {f : Poly n} (hfin : IsIsolatedSingularity f) :
    ∃ (μ : ℕ) (β : Fin μ → (Fin n →₀ ℕ)), IsMonomialBasis f β := by
  haveI : Module.Finite ℂ (MilnorAlgebra f) := hfin
  set m : (Fin n →₀ ℕ) → MilnorAlgebra f :=
    fun a => Ideal.Quotient.mk (jacobianIdeal f) (monomial a (1 : ℂ)) with hm
  -- Monomial classes span the Milnor algebra.
  have hspan : Submodule.span ℂ (Set.range m) = ⊤ := by
    have : Submodule.span ℂ (Set.range m) =
        (Submodule.span ℂ (Set.range (basisMonomials (Fin n) ℂ))).map
          (Ideal.Quotient.mkₐ ℂ (jacobianIdeal f)).toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp, coe_basisMonomials]; rfl
    rw [this, (basisMonomials (Fin n) ℂ).span_eq, Submodule.map_top, LinearMap.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  -- Extract a finite basis from the spanning family.
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range m)
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨_⟩ := hbfin.nonempty_fintype
  let e := Fintype.equivFin b
  have hpre : ∀ x : b, ∃ a, m a = x := fun x => hbS x.2
  choose g hg using hpre
  refine ⟨Fintype.card b, fun j => g (e.symm j), ?_, ?_⟩
  · have : (fun j => m (g (e.symm j))) = (Subtype.val : b → _) ∘ e.symm := by
      funext j; simp [hg]
    show LinearIndependent ℂ (fun j => m (g (e.symm j)))
    rw [this]; exact hbli.comp _ e.symm.injective
  · have : (Set.range fun j => m (g (e.symm j))) = b := by
      ext x; constructor
      · rintro ⟨j, rfl⟩; show m (g _) ∈ b; rw [hg]; exact (e.symm j).2
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp [hg]⟩
    show Submodule.span ℂ (Set.range fun j => m (g (e.symm j))) = ⊤
    rw [this, hbspan, hspan]

/-! ## 2. Versality and the stratum hypothesis -/

/-- General analytic versality: any analytic deformation `F(t,x)` of `f` is locally `F_{γ(t)}(Φ_t(x))`, for analytic `γ` with `γ(0)=0` and analytic coordinate changes with `Φ_0=id`. -/
def VersalityTheorem : Prop :=
  ∀ (n : ℕ) (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (μ : ℕ) (β : Fin μ → (Fin n →₀ ℕ)), IsMonomialBasis f β →
    ∀ (F : ℂ → (Fin n → ℂ) → ℂ),
      AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => F z.1 z.2) (0, 0) →
      (∀ᶠ x in 𝓝 (0 : Fin n → ℂ), F 0 x = eval x f) →
      ∃ (γ : ℂ → (Fin μ → ℂ)) (Φ : ℂ → (Fin n → ℂ) → (Fin n → ℂ)),
        AnalyticAt ℂ γ 0 ∧ γ 0 = 0 ∧
        AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2) (0, 0) ∧
        (∀ᶠ x in 𝓝 (0 : Fin n → ℂ), Φ 0 x = x) ∧
        ∀ᶠ z in 𝓝 ((0 : ℂ), (0 : Fin n → ℂ)),
          F z.1 z.2 = miniversalDeformation f β (γ z.1) (Φ z.1 z.2)

/-- The inclusion of the zero-critical-value `μ`-constant stratum in the coordinate subspace `s_j=0` for `e_j<d`. It is expressed on neighborhoods of the parameter origin, and the nearby critical point may move. -/
def VarchenkoTheorem : Prop :=
  ∀ (n : ℕ) (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (μ : ℕ) (β : Fin μ → (Fin n →₀ ℕ)), IsMonomialBasis f β →
    ∃ ε > 0, ∀ (s : Fin μ → ℂ) (p : Fin n → ℂ), ‖s‖ < ε → ‖p‖ < ε →
      IsIsolatedCriticalPointAt (miniversalDeformation f β s) p →
      miniversalDeformation f β s p = 0 →
      localMilnorNumber (miniversalDeformation f β s) p =
        localMilnorNumber (fun x => eval x f) 0 →
      ∀ j, Finsupp.weight w (β j) < d → s j = 0

/-! ## 3. A general first-order consequence -/

/-- For an analytic deformation with a nearby moving isolated critical point, critical value zero, and constant local Milnor number, a homogeneous polynomial initial derivative of degree less than `d` belongs to `J_f`, provided the analytic inputs below hold. -/
def FirstOrderCorollary35 : Prop :=
  ∀ (n : ℕ) (w : Fin n → ℕ) (d : ℕ) (f : Poly n), (∀ i, 0 < w i) →
    f.IsWeightedHomogeneous w d → HasIsolatedCriticalPoint f → eval 0 f = 0 →
    ∀ (F : ℂ → (Fin n → ℂ) → ℂ),
      AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => F z.1 z.2) (0, 0) →
      (∀ᶠ x in 𝓝 (0 : Fin n → ℂ), F 0 x = eval x f) →
      (∃ p : ℂ → (Fin n → ℂ), Tendsto p (𝓝 0) (𝓝 0) ∧ ∀ᶠ t in 𝓝 (0 : ℂ),
          IsIsolatedCriticalPointAt (F t) (p t) ∧ F t (p t) = 0 ∧
          localMilnorNumber (F t) (p t) = localMilnorNumber (fun x => eval x f) 0) →
      ∀ (Q : Poly n) (e : ℕ), Q.IsWeightedHomogeneous w e → e < d →
        (∀ᶠ x in 𝓝 (0 : Fin n → ℂ), deriv (fun t => F t x) 0 = eval x Q) →
        Q ∈ jacobianIdeal f

/-! ## 4. Versality and the stratum theorem imply the first-order consequence -/

/-! ### Slices of analytic families -/

lemma tendsto_graph {p : ℂ → (Fin n → ℂ)} (hp : Tendsto p (𝓝 0) (𝓝 0)) :
    Tendsto (fun t => (t, p t)) (𝓝 (0:ℂ)) (𝓝 ((0:ℂ), (0 : Fin n → ℂ))) :=
  tendsto_id.prodMk_nhds hp

/-- Joint analyticity at `(0,0)` gives analyticity of the slices at nearby points `p(t)` for small `t`. -/
lemma eventually_analyticAt_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {G : ℂ → (Fin n → ℂ) → E}
    (hG : AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => G z.1 z.2) (0, 0))
    {p : ℂ → (Fin n → ℂ)} (hp : Tendsto p (𝓝 0) (𝓝 0)) :
    ∀ᶠ t in 𝓝 (0:ℂ), AnalyticAt ℂ (G t) (p t) := by
  filter_upwards [(tendsto_graph hp).eventually hG.eventually_analyticAt] with t ht
  have hi : AnalyticAt ℂ (fun x : Fin n → ℂ => (t, x)) (p t) :=
    analyticAt_const.prod analyticAt_id
  exact ht.comp hi

/-- An identity near `(0,0)` restricts, for small `t`, to an identity near `p(t)` as a function of `x`. -/
lemma eventually_eventuallyEq_slice {E : Type*} {A B : ℂ → (Fin n → ℂ) → E}
    (h : ∀ᶠ z in 𝓝 ((0:ℂ), (0 : Fin n → ℂ)), A z.1 z.2 = B z.1 z.2)
    {p : ℂ → (Fin n → ℂ)} (hp : Tendsto p (𝓝 0) (𝓝 0)) :
    ∀ᶠ t in 𝓝 (0:ℂ), A t =ᶠ[𝓝 (p t)] B t := by
  filter_upwards [(tendsto_graph hp).eventually (eventually_eventually_nhds.2 h)] with t ht
  have hc : Tendsto (fun x : Fin n → ℂ => (t, x)) (𝓝 (p t)) (𝓝 (t, p t)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  exact hc.eventually ht

/-- If `Φ_0=id`, the differential of `Φ_t` at `p(t)` is invertible for small `t`. -/
lemma eventually_fderiv_slice_equiv {Φ : ℂ → (Fin n → ℂ) → (Fin n → ℂ)}
    (hΦ : AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2) (0, 0))
    (hΦ0 : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), Φ 0 x = x)
    {p : ℂ → (Fin n → ℂ)} (hp : Tendsto p (𝓝 0) (𝓝 0)) :
    ∀ᶠ t in 𝓝 (0:ℂ), ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), fderiv ℂ (Φ t) (p t) = e := by
  set G := fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2
  let D : ℂ × (Fin n → ℂ) → ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    fun z => (fderiv ℂ G z).comp (ContinuousLinearMap.inr ℂ ℂ (Fin n → ℂ))
  have hslice : ∀ᶠ z in 𝓝 ((0:ℂ), (0 : Fin n → ℂ)), fderiv ℂ (Φ z.1) z.2 = D z := by
    filter_upwards [hΦ.eventually_analyticAt] with z hz
    have hi : HasFDerivAt (fun x : Fin n → ℂ => (z.1, x))
        (ContinuousLinearMap.inr ℂ ℂ (Fin n → ℂ)) z.2 :=
      (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
    have := hz.differentiableAt.hasFDerivAt.comp z.2 hi
    exact this.fderiv
  have hDc : ContinuousAt D (0, 0) :=
    (hΦ.fderiv.continuousAt).clm_comp continuousAt_const
  have hD0 : D (0, 0) = ContinuousLinearMap.id ℂ _ := by
    rw [← hslice.self_of_nhds]
    have h' : Φ 0 =ᶠ[𝓝 0] id := hΦ0
    show fderiv ℂ (Φ 0) 0 = _
    rw [h'.fderiv_eq, fderiv_id]
  have hopen := ContinuousLinearEquiv.isOpen (𝕜 := ℂ) (E := Fin n → ℂ) (F := Fin n → ℂ)
  have hmem : ∀ᶠ z in 𝓝 ((0:ℂ), (0 : Fin n → ℂ)),
      D z ∈ Set.range ((↑) : ((Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) → _) := by
    apply hDc.eventually (hopen.mem_nhds _)
    rw [hD0]; exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩
  filter_upwards [(tendsto_graph hp).eventually (hslice.and hmem)] with t ⟨h1, e, he⟩
  exact ⟨e, h1.trans he.symm⟩

lemma isIsolatedCriticalPointAt_congr {g g' : (Fin n → ℂ) → ℂ} {p : Fin n → ℂ}
    (h : g =ᶠ[𝓝 p] g') : IsIsolatedCriticalPointAt g p ↔ IsIsolatedCriticalPointAt g' p := by
  have hd : ∀ᶠ x in 𝓝 p, fderiv ℂ g x = fderiv ℂ g' x := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    exact hx.fderiv_eq
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hd.self_of_nhds ▸ h1, ?_⟩
    filter_upwards [h2, nhdsWithin_le_nhds hd] with x hx hx'
    rwa [← hx']
  · rintro ⟨h1, h2⟩
    refine ⟨hd.self_of_nhds ▸ h1, ?_⟩
    filter_upwards [h2, nhdsWithin_le_nhds hd] with x hx hx'
    rwa [hx']

lemma analyticAt_miniversalDeformation (f : Poly n) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ))
    (s : Fin μ → ℂ) (y : Fin n → ℂ) : AnalyticAt ℂ (miniversalDeformation f β s) y :=
  analyticAt_eval _ y


/-- Invariance of local Milnor numbers, criticality, and critical values under coordinate changes places `γ(t)` in the stratum; hence its low-degree coordinates vanish. -/
lemma eventually_gamma_eq_zero {w : Fin n → ℕ} {d : ℕ} {f : Poly n} {μ : ℕ}
    {β : Fin μ → (Fin n →₀ ℕ)} {ε : ℝ}
    (hε : ∀ (s : Fin μ → ℂ) (p : Fin n → ℂ), ‖s‖ < ε → ‖p‖ < ε →
      IsIsolatedCriticalPointAt (miniversalDeformation f β s) p →
      miniversalDeformation f β s p = 0 →
      localMilnorNumber (miniversalDeformation f β s) p =
        localMilnorNumber (fun x => eval x f) 0 →
      ∀ j, Finsupp.weight w (β j) < d → s j = 0) (hε0 : 0 < ε)
    {F : ℂ → (Fin n → ℂ) → ℂ} {γ : ℂ → (Fin μ → ℂ)} {Φ : ℂ → (Fin n → ℂ) → (Fin n → ℂ)}
    (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = 0)
    (hΦ : AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2) (0, 0))
    (hΦ0 : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), Φ 0 x = x)
    (hFΦ : ∀ᶠ z in 𝓝 ((0 : ℂ), (0 : Fin n → ℂ)),
          F z.1 z.2 = miniversalDeformation f β (γ z.1) (Φ z.1 z.2))
    {p : ℂ → (Fin n → ℂ)} (hp : Tendsto p (𝓝 0) (𝓝 0))
    (hev : ∀ᶠ t in 𝓝 (0 : ℂ),
          IsIsolatedCriticalPointAt (F t) (p t) ∧ F t (p t) = 0 ∧
          localMilnorNumber (F t) (p t) = localMilnorNumber (fun x => eval x f) 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j, Finsupp.weight w (β j) < d → γ t j = 0 := by
  have hγε : ∀ᶠ t in 𝓝 (0 : ℂ), ‖γ t‖ < ε :=
    hγ.norm.eventually (gt_mem_nhds (by simpa [hγ0] using hε0))
  have hΦt : Tendsto (fun t => Φ t (p t)) (𝓝 0) (𝓝 (Φ 0 0)) :=
    hΦ.continuousAt.tendsto.comp (tendsto_graph hp)
  rw [hΦ0.self_of_nhds] at hΦt
  have hΦε : ∀ᶠ t in 𝓝 (0 : ℂ), ‖Φ t (p t)‖ < ε :=
    hΦt.norm.eventually (gt_mem_nhds (by simpa using hε0))
  filter_upwards [hγε, hΦε, hev, eventually_analyticAt_slice hΦ hp,
    eventually_fderiv_slice_equiv hΦ hΦ0 hp, eventually_eventuallyEq_slice (A := F)
      (B := fun t x => miniversalDeformation f β (γ t) (Φ t x)) hFΦ hp]
    with t h1 h2 hcv han he heq
  obtain ⟨hc, hv, hm⟩ := hcv
  obtain ⟨e, he⟩ := he
  have hg := analyticAt_miniversalDeformation f β (γ t) (Φ t (p t))
  apply hε (γ t) (Φ t (p t)) h1 h2
  · exact isIsolatedCriticalPointAt_of_comp hg han he ((isIsolatedCriticalPointAt_congr heq).1 hc)
  · exact (heq.self_of_nhds).symm.trans hv
  · rw [← localMilnorNumber_comp hg han he, ← localMilnorNumber_congr heq, hm]

lemma miniversalDeformation_apply (f : Poly n) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ))
    (s : Fin μ → ℂ) (y : Fin n → ℂ) :
    miniversalDeformation f β s y = eval y f + ∑ j, s j * eval y (monomial (β j) 1) := by
  simp [miniversalDeformation, miniversalPoly, eval_monomial]

lemma eventually_deriv_formula {f : Poly n} {μ : ℕ} {β : Fin μ → (Fin n →₀ ℕ)}
    {F : ℂ → (Fin n → ℂ) → ℂ} {γ : ℂ → (Fin μ → ℂ)} {Φ : ℂ → (Fin n → ℂ) → (Fin n → ℂ)}
    (hγ : DifferentiableAt ℂ γ 0) (hγ0 : γ 0 = 0)
    (hΦ : AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2) (0, 0))
    (hΦ0 : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), Φ 0 x = x)
    (hFΦ : ∀ᶠ z in 𝓝 ((0 : ℂ), (0 : Fin n → ℂ)),
          F z.1 z.2 = miniversalDeformation f β (γ z.1) (Φ z.1 z.2)) :
    ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), deriv (fun t => F t x) 0 =
      ∑ i, eval x (pderiv i f) * fderiv ℂ (fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2) (0, x) (1, 0) i +
        ∑ j, deriv γ 0 j * eval x (monomial (β j) 1) := by
  set G := fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2
  rw [nhds_prod_eq, eventually_prod_iff] at hFΦ
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hFΦ
  have hsl : Tendsto (fun x : Fin n → ℂ => ((0 : ℂ), x)) (𝓝 0) (𝓝 ((0:ℂ), (0 : Fin n → ℂ))) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [hpb, hΦ0, hsl.eventually hΦ.eventually_analyticAt] with x hx hx0 hxa
  have heq : (fun t => F t x) =ᶠ[𝓝 0] fun t => miniversalDeformation f β (γ t) (Φ t x) := by
    filter_upwards [hpa] with t ht using hab ht hx
  rw [heq.deriv_eq]
  -- The derivative `∂_t Φ(0,x)`.
  have hΦd : HasDerivAt (fun t => Φ t x) (fderiv ℂ G (0, x) (1, 0)) 0 := by
    have hi : HasDerivAt (fun t : ℂ => (t, x)) ((1 : ℂ), (0 : Fin n → ℂ)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
    exact hxa.differentiableAt.hasFDerivAt.comp_hasDerivAt (x := (0:ℂ)) hi
  have hγd : HasDerivAt γ (deriv γ 0) 0 := hγ.hasDerivAt
  have hfd : HasDerivAt (fun t => eval (Φ t x) f)
      (∑ i, eval x (pderiv i f) * fderiv ℂ G (0, x) (1, 0) i) 0 := by
    have := (hasFDerivAt_eval f (Φ 0 x)).comp_hasDerivAt (x := (0:ℂ)) hΦd
    rw [evalDeriv_apply, hx0] at this
    exact this
  have hmd : ∀ j, HasDerivAt (fun t => γ t j * eval (Φ t x) (monomial (β j) 1))
      (deriv γ 0 j * eval x (monomial (β j) 1)) 0 := by
    intro j
    have h1 : HasDerivAt (fun t => γ t j) (deriv γ 0 j) 0 := hasDerivAt_pi.1 hγd j
    have h2 := (hasFDerivAt_eval (monomial (β j) 1) (Φ 0 x)).comp_hasDerivAt (x := (0:ℂ)) hΦd
    have := h1.mul h2
    simpa [hγ0, hx0] using this
  have hall := hfd.add (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hmd j)
  convert hall.deriv using 2
  funext t
  rw [miniversalDeformation_apply]
  rfl

lemma weightedHomogeneousComponent_sum_monomial_eq_zero {w : Fin n → ℕ} {d : ℕ} {μ : ℕ}
    {β : Fin μ → (Fin n →₀ ℕ)} {c : Fin μ → ℂ} (hc : ∀ j, Finsupp.weight w (β j) < d → c j = 0)
    (m : ℕ) (hm : m < d) :
    weightedHomogeneousComponent w m (∑ j, monomial (β j) (c j)) = 0 := by
  classical
  ext a
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with ha
  · rw [coeff_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_monomial]
    split_ifs with hj
    · exact hc j (by rw [hj, ha]; exact hm)
    · rfl
  · rfl

/-- Derive the general first-order Jacobian-ideal conclusion from versality and the stratum theorem. -/
theorem corollary35_of_varchenko_and_versality (hV : VarchenkoTheorem) (hU : VersalityTheorem) :
    FirstOrderCorollary35 := by
  intro n w d f hw hf hcrit hf0 F hFan hF0 hpex Q e hQ he hderiv
  obtain ⟨p, hp, hev⟩ := hpex
  have hiso := isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit
  obtain ⟨μ, β, hβ⟩ := exists_monomialBasis hiso
  obtain ⟨γ, Φ, hγ, hγ0, hΦ, hΦ0, hFΦ⟩ := hU n w d f hw hf hcrit hf0 μ β hβ F hFan hF0
  obtain ⟨ε, hε0, hε⟩ := hV n w d f hw hf hcrit hf0 μ β hβ
  -- Step 1: the low-degree coordinates `γ_j(t)` and their derivatives at zero vanish.
  have hvan := eventually_gamma_eq_zero hε hε0 hγ.continuousAt hγ0 hΦ hΦ0 hFΦ hp hev
  have hd0 : ∀ j, Finsupp.weight w (β j) < d → deriv γ 0 j = 0 := by
    intro j hj
    have h1 : (fun t => γ t j) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hvan] with t ht using ht j hj
    rw [← (hasDerivAt_pi.1 hγ.differentiableAt.hasDerivAt j).deriv, h1.deriv_eq, deriv_const]
  -- Step 2: differentiate with respect to `t`.
  set G := fun z : ℂ × (Fin n → ℂ) => Φ z.1 z.2 with hG
  set v : Fin n → (Fin n → ℂ) → ℂ := fun i x => fderiv ℂ G (0, x) (1, 0) i with hv
  set r : Poly n := ∑ j, monomial (β j) (deriv γ 0 j) with hr
  have hform := eventually_deriv_formula hγ.differentiableAt hγ0 hΦ hΦ0 hFΦ
  have hQeq : (fun x => eval x Q) =ᶠ[𝓝 0]
      fun x => ∑ i, eval x (pderiv i f) * v i x + eval x r := by
    filter_upwards [hform, hderiv] with x h1 h2
    rw [← h2, h1, hr, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [eval_monomial]
  -- Step 3: take Taylor series.
  have hva : ∀ i, AnalyticAt ℂ (v i) 0 := by
    intro i
    have h1 : AnalyticAt ℂ (fun x : Fin n → ℂ => fderiv ℂ G (0, x)) 0 :=
      hΦ.fderiv.comp (analyticAt_const.prod analyticAt_id)
    have h2 := analyticAt_clm_apply h1 ((1 : ℂ), (0 : Fin n → ℂ))
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _).comp h2
  have htay := taylorAt_congr hQeq
  have hA : AnalyticAt ℂ (fun x => ∑ i, eval x (pderiv i f) * v i x) 0 := by
    have := Finset.univ.analyticAt_sum (fun i _ => (analyticAt_eval (pderiv i f) 0).mul (hva i))
    convert this using 1
    funext x; simp
  rw [taylorAt_eval_zero, taylorAt_add hA (analyticAt_eval _ 0),
    taylorAt_sum (h := fun i x => eval x (pderiv i f) * v i x) _
      (fun i _ => (analyticAt_eval _ 0).mul (hva i)), taylorAt_eval_zero] at htay
  have hmem : polyToConv (Q - r) ∈ convIdeal (jacobianIdeal f) := by
    rw [map_sub, htay, add_sub_cancel_right]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [taylorAt_mul (analyticAt_eval _ 0) (hva i), taylorAt_eval_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
  have hsub := mem_of_polyToConv_mem_convIdeal (exists_pow_X_mem_jacobianIdeal hw hf hcrit) hmem
  -- Step 4: use the grading.
  exact mem_jacobianIdeal_of_sub_mem hf hQ he
    (weightedHomogeneousComponent_sum_monomial_eq_zero hd0) hsub

end Yau
