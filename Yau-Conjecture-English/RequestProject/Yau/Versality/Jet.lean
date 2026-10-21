import RequestProject.Yau.Versality.Determinacy

/-!
# Versality at the level of finite jets

Write finitely many monomials in terms of the gradient and the chosen Milnor
basis. Their coefficients define a polynomial coordinate correction `ξ_v`
and deformation parameters `s(v)`. The map taking `v` to the selected
coefficients of `F_{s(v)}(x+ξ_v(x))` has derivative the identity at zero.
Its analytic local inverse produces a parameter curve matching the chosen
coefficients of `f+tq`, together with their required first-order relation.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

section Jet

variable (f : Poly n) {μ : ℕ} (β : Fin μ → (Fin n →₀ ℕ)) {m : ℕ}
  (mono : Fin m → (Fin n →₀ ℕ)) (A : Fin m → Fin n → Poly n) (σc : Fin m → Fin μ → ℂ)

/-- The polynomial coordinate change `x↦x+∑_a v_a A_a(x)`. -/
def jetMap (v : Fin m → ℂ) : Fin n → Poly n := fun i => X i + ∑ a, C (v a) * A a i

/-- The deformation parameter `s(v)=∑_a v_a σ_a`. -/
def jetParam (v : Fin m → ℂ) : Fin μ → ℂ := fun j => ∑ a, v a * σc a j

/-- `G_v(x) = 𝓕(x + ξ_v(x), s(v))`。 -/
def jetPoly (v : Fin m → ℂ) : Poly n :=
  bind₁ (jetMap A v) (miniversalPoly f β (jetParam σc v))

/-- The universal coordinate change over the parameter polynomial ring `ℂ[v]`. -/
def uMap : Fin n → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ) :=
  fun i => X i + ∑ a, C (X a) * MvPolynomial.map C (A a i)

/-- The universal deformation parameters. -/
def uParam : Fin μ → MvPolynomial (Fin m) ℂ := fun j => ∑ a, X a * C (σc a j)

/-- The universal polynomial `G` over `ℂ[v]`. -/
def uPoly : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ) :=
  bind₁ (uMap A) (MvPolynomial.map C f + ∑ j, monomial (β j) (uParam σc j))

lemma map_eval_map_C (v : Fin m → ℂ) (p : Poly n) :
    MvPolynomial.map (eval v) (MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin m) ℂ) p) = p := by
  rw [MvPolynomial.map_map]
  have : (eval v).comp (C : ℂ →+* MvPolynomial (Fin m) ℂ) = RingHom.id ℂ := by
    ext; simp
  rw [this, MvPolynomial.map_id]

lemma map_eval_uPoly (v : Fin m → ℂ) :
    MvPolynomial.map (eval v) (uPoly f β A σc) = jetPoly f β A σc v := by
  rw [uPoly, MvPolynomial.map_bind₁, jetPoly]
  have hmap : (fun i => MvPolynomial.map (eval v) (uMap A i)) = jetMap A v := by
    funext i
    simp [uMap, jetMap, map_eval_map_C]
  rw [hmap]
  congr 1
  simp [miniversalPoly, map_eval_map_C, map_monomial, uParam, jetParam]

/-- The selected coefficient of `G_v`, as a polynomial in `v`. -/
def jetCoeff (v : Fin m → ℂ) : Fin m → ℂ :=
  fun a => eval v (coeff (mono a) (uPoly f β A σc))

lemma jetCoeff_eq (v : Fin m → ℂ) (a : Fin m) :
    jetCoeff f β mono A σc v a = coeff (mono a) (jetPoly f β A σc v) := by
  rw [jetCoeff, ← map_eval_uPoly, coeff_map]

lemma jetPoly_zero : jetPoly f β A σc 0 = f := by
  have h1 : jetMap A (0 : Fin m → ℂ) = X := by funext i; simp [jetMap]
  have h2 : jetParam σc (0 : Fin m → ℂ) = 0 := by funext j; simp [jetParam]
  rw [jetPoly, h1, h2, bind₁_X_left]
  simp [miniversalPoly]

/-- The maximal ideal `(v₁,…,v_m)` of the parameter polynomial ring. -/
abbrev paramIdeal (m : ℕ) : Ideal (MvPolynomial (Fin m) ℂ) := Ideal.span (Set.range X)

lemma eval_zero_of_mem_paramIdeal {r : MvPolynomial (Fin m) ℂ} (hr : r ∈ paramIdeal m) :
    eval 0 r = 0 := by
  have : paramIdeal m ≤ RingHom.ker (eval (0 : Fin m → ℂ)) := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simp
  exact this hr

lemma eval_zero_pderiv_of_mem_sq {r : MvPolynomial (Fin m) ℂ} (hr : r ∈ paramIdeal m ^ 2)
    (b : Fin m) : eval 0 (pderiv b r) = 0 := by
  rw [pow_two] at hr
  refine Submodule.mul_induction_on hr ?_ ?_
  · intro x hx y hy
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      eval_zero_of_mem_paramIdeal hx, eval_zero_of_mem_paramIdeal hy]
    ring
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

variable {f β mono A σc}

/-- `G = f + ∑_a v_a x^{mono a} + O(v²)`。 -/
lemma uPoly_sub_mem
    (hA : ∀ a, monomial (mono a) 1 =
      ∑ i, pderiv i f * A a i + ∑ j, monomial (β j) (σc a j)) :
    uPoly f β A σc - MvPolynomial.map C f - ∑ a, C (X a) * MvPolynomial.map C (monomial (mono a) (1 : ℂ)) ∈
      (Ideal.map (C : MvPolynomial (Fin m) ℂ →+* _) (paramIdeal m)) ^ 2 := by
  classical
  set 𝔐 := Ideal.map (C : MvPolynomial (Fin m) ℂ →+* MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ))
    (paramIdeal m)
  set Y : Fin n → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ) :=
    fun i => ∑ a, C (X a) * MvPolynomial.map C (A a i)
  have hCX : ∀ a, (C (X a) : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ)) ∈ 𝔐 := fun a =>
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, rfl⟩)
  have hY : ∀ i, Y i ∈ 𝔐 := fun i => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (hCX a)
  set N : Fin m → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ) :=
    fun a => ∑ j, monomial (β j) (C (σc a j))
  set P : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ) :=
    MvPolynomial.map C f + ∑ j, monomial (β j) (uParam σc j)
  have hM : ∑ j, monomial (β j) (uParam σc j) =
      ∑ a, (C (X a) : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ)) * N a := by
    simp only [N, uParam, Finset.mul_sum, C_mul_monomial]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_sum]
  have hT := bind₁_X_add_sub_mem Y P
  have hTle : Ideal.span (Set.range fun ij : Fin n × Fin n => Y ij.1 * Y ij.2) ≤ 𝔐 ^ 2 := by
    rw [Ideal.span_le]
    rintro _ ⟨ij, rfl⟩
    rw [pow_two]
    exact Ideal.mul_mem_mul (hY _) (hY _)
  have hP : uPoly f β A σc = bind₁ (fun i => X i + Y i) P := rfl
  have hdP : ∀ i, pderiv i P = MvPolynomial.map C (pderiv i f) +
      ∑ a, (C (X a) : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ)) * pderiv i (N a) := by
    intro i
    simp only [P, hM, map_add, map_sum, pderiv_C_mul, pderiv_map]
  have hlin : ∑ j, monomial (β j) (uParam σc j) + ∑ i, MvPolynomial.map C (pderiv i f) * Y i =
      ∑ a, C (X a) * MvPolynomial.map C (monomial (mono a) (1 : ℂ)) := by
    rw [hM]
    simp only [Y, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i a => MvPolynomial.map C (pderiv i f) * (C (X a) * MvPolynomial.map C (A a i))), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hA a, map_add, map_sum, map_sum, mul_add, Finset.mul_sum, Finset.mul_sum, add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [MvPolynomial.map_monomial]
  have hdecomp : uPoly f β A σc - MvPolynomial.map C f - ∑ a, C (X a) * MvPolynomial.map C (monomial (mono a) (1 : ℂ)) =
      (bind₁ (fun i => X i + Y i) P - P - ∑ i, pderiv i P * Y i) +
        ∑ i, (∑ a, (C (X a) : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ)) *
          pderiv i (N a)) * Y i := by
    rw [hP, ← hlin]
    simp only [hdP, add_mul, Finset.sum_add_distrib, P]
    ring
  rw [hdecomp]
  refine Ideal.add_mem _ (hTle hT) (Ideal.sum_mem _ fun i _ => ?_)
  rw [pow_two]
  exact Ideal.mul_mem_mul (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (hCX a)) (hY i)

/-- The coefficient map has derivative the identity at zero. -/
lemma hasFDerivAt_jetCoeff (hmono : Function.Injective mono)
    (hA : ∀ a, monomial (mono a) 1 =
      ∑ i, pderiv i f * A a i + ∑ j, monomial (β j) (σc a j)) :
    HasFDerivAt (jetCoeff f β mono A σc) (ContinuousLinearMap.id ℂ (Fin m → ℂ)) 0 := by
  classical
  have hmem := uPoly_sub_mem (f := f) (β := β) (mono := mono) (A := A) (σc := σc) hA
  rw [← Ideal.map_pow] at hmem
  rw [hasFDerivAt_pi']
  intro a
  set r := coeff (mono a) (uPoly f β A σc - MvPolynomial.map C f -
    ∑ b, C (X b) * MvPolynomial.map C (monomial (mono b) (1 : ℂ)))
  have hr : r ∈ paramIdeal m ^ 2 := mem_map_C_iff.1 hmem _
  have hcoeff : coeff (mono a) (uPoly f β A σc) = C (coeff (mono a) f) + X a + r := by
    have hL : coeff (mono a) (∑ b, (C (X b) : MvPolynomial (Fin n) (MvPolynomial (Fin m) ℂ)) *
        MvPolynomial.map C (monomial (mono b) (1 : ℂ))) = X a := by
      rw [coeff_sum]
      simp only [coeff_C_mul, coeff_map, coeff_monomial]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (hmono h))]; simp
      · simp
    simp only [r, coeff_sub, coeff_map, hL]
    ring
  have hd := hasFDerivAt_eval (coeff (mono a) (uPoly f β A σc)) (0 : Fin m → ℂ)
  refine hd.congr_fderiv ?_
  ext u
  simp only [evalDeriv_apply, hcoeff, map_add, pderiv_C, pderiv_X, eval_zero_pderiv_of_mem_sq hr,
    add_zero, zero_add]
  simp [Pi.single_apply]

lemma analyticAt_jetCoeff (v : Fin m → ℂ) : AnalyticAt ℂ (jetCoeff f β mono A σc) v :=
  analyticAt_pi_iff.2 fun _ => analyticAt_eval _ v

/-- Finite-jet versality: an analytic curve `v(t)` matches the selected coefficients of `G_{v(t)}` and `f+tq`, with `v(0)=0` and initial derivative given by the corresponding coefficients of `q`. -/
theorem exists_jet_solution (hmono : Function.Injective mono)
    (hA : ∀ a, monomial (mono a) 1 =
      ∑ i, pderiv i f * A a i + ∑ j, monomial (β j) (σc a j)) (q : Poly n) :
    ∃ v : ℂ → (Fin m → ℂ), AnalyticAt ℂ v 0 ∧ v 0 = 0 ∧
      HasDerivAt v (fun a => coeff (mono a) q) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a, coeff (mono a) (jetPoly f β A σc (v t)) =
        coeff (mono a) (f + C t * q) := by
  set Λ := jetCoeff f β mono A σc
  obtain ⟨Ψ, hΨan, hΨ0, -, hright, hΨd⟩ := exists_analytic_localInverse_id
    (analyticAt_jetCoeff (f := f) (β := β) (mono := mono) (A := A) (σc := σc) 0)
    (hasFDerivAt_jetCoeff hmono hA).fderiv
  set τ : ℂ → (Fin m → ℂ) := fun t a => coeff (mono a) f + t * coeff (mono a) q
  have hτ0 : τ 0 = Λ 0 := by
    funext a
    simp only [τ, zero_mul, add_zero, Λ, jetCoeff_eq, jetPoly_zero]
  have hτd : HasDerivAt τ (fun a => coeff (mono a) q) 0 := by
    rw [hasDerivAt_pi]
    intro a
    have := ((hasDerivAt_id (0 : ℂ)).mul_const (coeff (mono a) q)).const_add (coeff (mono a) f)
    show HasDerivAt (fun t : ℂ => coeff (mono a) f + t * coeff (mono a) q) _ 0
    simpa using this
  have hτan : AnalyticAt ℂ τ 0 := analyticAt_pi_iff.2 fun a =>
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hτt : Tendsto τ (𝓝 0) (𝓝 (Λ 0)) := by
    rw [← hτ0]; exact hτan.continuousAt.tendsto
  refine ⟨fun t => Ψ (τ t), AnalyticAt.comp_of_eq hΨan hτan hτ0, ?_, ?_, ?_⟩
  · show Ψ (τ 0) = 0
    rw [hτ0]; exact hΨ0
  · have := hΨd.comp_hasDerivAt_of_eq (x := (0 : ℂ)) hτd hτ0.symm
    simpa using this
  · filter_upwards [hτt.eventually hright] with t ht a
    rw [← jetCoeff_eq, ht]
    simp [τ]

end Jet

end Yau
