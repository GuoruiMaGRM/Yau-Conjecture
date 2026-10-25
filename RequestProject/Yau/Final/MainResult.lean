import RequestProject.Yau.Versality.FixedPoint
import RequestProject.Yau.Final.Rational
import RequestProject.Yau.Appendix.EulerModuli

/-!
# Assembling the main theorem

The `μ`-constant stratum theorem and the proved versality statement for the
fixed-origin families yield the first-order Jacobian-ideal conclusion.
Apply it to the square deformation from Lemma 3.3 to obtain Corollary 3.5,
then Theorem 3.6 and the argument of Section 4.
This file packages the resulting integer-weight, rational-weight, and moduli-algebra
statements. The explicitly AGV-based formulation is in `ThreeNewLocal.lean`.
The general moving-critical-point consequence is also retained as a separate result.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ## 1. Polynomial families -/

/-- The polynomial family `(t,x) ↦ g(x) + t a(x)` is analytic at every point. -/
lemma analyticAt_eval_add_smul (g a : Poly n) (z : ℂ × (Fin n → ℂ)) :
    AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => eval z.2 (g + C z.1 * a)) z := by
  have hcoord : ∀ i, AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => z.2 i) z := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin n → ℂ))).analyticAt z
  have hp : ∀ p : Poly n, AnalyticAt ℂ (fun z : ℂ × (Fin n → ℂ) => eval z.2 p) z := fun p => by
    have := AnalyticAt.aeval_mvPolynomial (f := fun z : ℂ × (Fin n → ℂ) => z.2) hcoord p
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  simp only [map_add, map_mul, eval_C]
  exact (hp g).add (analyticAt_fst.mul (hp a))

/-! ## 2. The square-deformation input for Theorem 3.6 -/

/-- The first-order Jacobian-ideal conclusion applied to `g+t a²` gives `a² ∈ J_g`. Lemma 3.3 supplies isolatedness, critical value zero, and constant Milnor number, and the initial derivative is `a²` of degree `2r < d`. -/
theorem varchenkoHypothesis_of_corollary35 (hC : FirstOrderCorollary35) : VarchenkoHypothesis := by
  intro m w d g H r a ha hr haI
  have h2 : (a ^ 2).IsWeightedHomogeneous w (2 * r) := by
    have h := ha.pow 2
    rwa [smul_eq_mul] at h
  have hsq := squareDeformation_hyp H ha hr haI
  have hcrit0 : HasIsolatedCriticalPoint g := by simpa using (hsq 0).1
  have hg0 : eval 0 g = 0 := by simpa using (hsq 0).2.1
  have hμ : ∀ t : ℂ, localMilnorNumber (fun x => eval x (g + C t * a ^ 2)) 0 =
      localMilnorNumber (fun x => eval x g) 0 := by
    intro t
    rw [localMilnorNumber_eval_zero, localMilnorNumber_eval_zero]
    exact (hsq t).2.2
  refine hC m w d g H.pos H.hom hcrit0 hg0 (fun t x => eval x (g + C t * a ^ 2))
    (analyticAt_eval_add_smul g (a ^ 2) _) (Eventually.of_forall fun x => by simp)
    ⟨fun _ => 0, tendsto_const_nhds, Eventually.of_forall fun t =>
      ⟨isIsolatedCriticalPointAt_of_hasIsolatedCriticalPoint (hsq t).1, (hsq t).2.1, hμ t⟩⟩
    (a ^ 2) (2 * r) h2 (by omega) (Eventually.of_forall fun x => ?_)
  simp only [map_add, map_mul, eval_C]
  rw [deriv_const_add, deriv_mul_const_field, deriv_id'', one_mul]

/-- The stratum theorem and general versality imply the square-deformation input. The main theorem uses the separately proved fixed-origin versality statement. -/
theorem varchenkoHypothesis_of_theorem34 (hV : VarchenkoTheorem) (hU : VersalityTheorem) :
    VarchenkoHypothesis :=
  varchenkoHypothesis_of_corollary35 (corollary35_of_varchenko_and_versality hV hU)

/-- The stratum theorem gives the square-deformation input using the proved fixed-origin versality statement: Lemma 3.3 verifies the hypotheses for `g+t a²`. -/
theorem varchenkoHypothesis_of_varchenko (hV : VarchenkoTheorem) : VarchenkoHypothesis := by
  intro m w d g H r a ha hr haI
  have h2 : (a ^ 2).IsWeightedHomogeneous w (2 * r) := by
    have h := ha.pow 2
    rwa [smul_eq_mul] at h
  have hsq := squareDeformation_hyp H ha hr haI
  have hcrit0 : HasIsolatedCriticalPoint g := by simpa using (hsq 0).1
  have hg0 : eval 0 g = 0 := by simpa using (hsq 0).2.1
  exact corollary35_fixed_origin hV H.pos H.hom hcrit0 hg0 h2 (by omega)
    (Eventually.of_forall fun t =>
      ⟨squareDeformation_critical_iff H ha hr haI t, (hsq t).2.1, (hsq t).2.2⟩)

/-! ## 3. The main theorem -/

/-- Yau's conjecture under the `μ`-constant stratum hypothesis: every negative-degree derivation of the Milnor algebra is zero. -/
theorem yau_conjecture_of_varchenko (hV : VarchenkoTheorem) {n : ℕ} (w : Fin n → ℕ)
    (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  yau_conjecture_of_critical (varchenkoHypothesis_of_varchenko hV) w d f hw hf hcrit k hk δ hδ

/-- The main theorem with rational weights, under the stratum hypothesis. -/
theorem yau_conjecture_rational_weights (hV : VarchenkoTheorem) (w : Fin n → ℚ)
    (d : ℚ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hcrit : HasIsolatedCriticalPoint f) (k : ℚ) (hk : k < 0)
    (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegreeRat w f k δ) : δ = 0 :=
  yau_conjecture_rat (varchenkoHypothesis_of_varchenko hV) w d f hw hf hcrit k hk δ hδ

/-- The main theorem for the moduli algebra `T_f = ℂ[x]/(f,J)`, under the stratum hypothesis. -/
theorem yau_conjecture_moduli_algebra (hV : VarchenkoTheorem) {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (f : Poly n) (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hd : 0 < d) (hcrit : HasIsolatedCriticalPoint f) (k : ℤ) (hk : k < 0)
    (δ : Derivation ℂ (ModuliAlgebra f) (ModuliAlgebra f))
    (hδ : IsDerivationOfDegreeModuli w f k δ) : δ = 0 :=
  yau_conjecture_moduli (varchenkoHypothesis_of_varchenko hV) w d f hw hf hd hcrit k hk δ hδ

end Yau
