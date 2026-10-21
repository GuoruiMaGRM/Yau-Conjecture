import RequestProject.Yau.Basic.Basic

/-!
# Calculus of polynomial functions

The derivative of polynomial evaluation is expressed through formal partial
derivatives. A polynomial that vanishes on a neighborhood is the zero polynomial.
-/

open MvPolynomial Filter Topology

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The candidate derivative of polynomial evaluation at `x`. -/
def evalDeriv (p : Poly n) (x : Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i

lemma evalDeriv_apply (p : Poly n) (x v : Fin n → ℂ) :
    evalDeriv p x v = ∑ i, eval x (pderiv i p) * v i := by
  simp [evalDeriv]

/-- Formal partial derivatives give the derivative of polynomial evaluation. -/
lemma hasFDerivAt_eval (p : Poly n) (x : Fin n → ℂ) :
    HasFDerivAt (fun y => eval y p) (evalDeriv p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact (hasFDerivAt_const a x).congr_fderiv (by ext v; simp [evalDeriv_apply])
  | add p q hp hq =>
    simp only [map_add]
    exact (hp.add hq).congr_fderiv (by
      ext v; simp [evalDeriv_apply, add_mul, Finset.sum_add_distrib])
  | mul_X p j hp =>
    have hX : HasFDerivAt (fun y : Fin n → ℂ => y j)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) x :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).hasFDerivAt
    simp only [map_mul, eval_X]
    refine (hp.mul hX).congr_fderiv ?_
    ext v
    simp only [evalDeriv_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Derivation.leibniz, pderiv_X, map_add,
      map_mul, eval_X]
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Ne.symm hij]
    · simp
    · refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- A polynomial vanishing on a neighborhood is zero. -/
lemma eq_zero_of_eventually_eval_eq_zero {p : Poly n} {z : Fin n → ℂ}
    (h : ∀ᶠ x in 𝓝 z, eval x p = 0) : p = 0 := by
  have ha : AnalyticOnNhd ℂ (fun x : Fin n → ℂ => eval x p) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial p
  have := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) h
  exact MvPolynomial.funext fun x => by simpa using this (Set.mem_univ x)

end Yau
