import RequestProject.Yau.Basic.PolyDeriv

/-! # Standing hypotheses after splitting -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The setup after removal of quadratic variables: positive weights, weighted degree `d > 2 max w_i`, and an isolated singularity. -/
structure Setup (w : Fin n → ℕ) (d : ℕ) (f : Poly n) : Prop where
  pos : ∀ i, 0 < w i
  hom : f.IsWeightedHomogeneous w d
  big : ∀ i, 2 * w i < d
  iso : IsIsolatedSingularity f

/-- The square-deformation consequence used in Corollary 3.5: for homogeneous `a` of degree `r`, with `3r < d` and `a ∈ √I_r`, one has `a² ∈ J`. -/
def SquareDeformationProperty (w : Fin n → ℕ) (d : ℕ) (f : Poly n) : Prop :=
  ∀ (r : ℕ) (a : Poly n), a.IsWeightedHomogeneous w r → 3 * r < d →
    a ∈ (partialIdeal w f r).radical → a ^ 2 ∈ jacobianIdeal f

variable {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

lemma mem_jac_eval_zero {x : Fin n → ℂ} (hx : ∀ i, eval x (pderiv i f) = 0) {p : Poly n}
    (hp : p ∈ jacobianIdeal f) : eval x p = 0 := by
  have : jacobianIdeal f ≤ RingHom.ker (eval x) := by
    rw [jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩; exact hx i
  exact this hp

/-- For an isolated weighted homogeneous singularity, the origin is the only common zero of the partial derivatives. -/
lemma common_zero_eq_zero (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hiso : IsIsolatedSingularity f) (x : Fin n → ℂ)
    (hx : ∀ i, eval x (pderiv i f) = 0) : x = 0 := by
  haveI : Module.Finite ℂ (MilnorAlgebra f) := hiso
  funext j
  by_contra hxj
  obtain ⟨P, hPm, hP⟩ := (Algebra.IsIntegral.isIntegral (R := ℂ)
    (Ideal.Quotient.mk (jacobianIdeal f) (X j)))
  set q : Poly n := P.eval₂ C (X j)
  have hq : q ∈ jacobianIdeal f := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    convert hP
  have hroot : ∀ t : ℂ, P.eval (t ^ w j * x j) = 0 := by
    intro t
    have hxt : ∀ i, eval (fun l => t ^ w l * x l) (pderiv i f) = 0 := by
      intro i; rw [eval_scale (pderiv_isWH hf i).1, hx i, mul_zero]
    have := mem_jac_eval_zero hxt hq
    rw [Polynomial.hom_eval₂] at this
    have hc : (eval fun l => t ^ w l * x l).comp C = RingHom.id ℂ := by ext; simp
    simpa [Polynomial.eval₂_eq_eval_map, hc] using this
  apply hPm.ne_zero
  apply Polynomial.eq_zero_of_infinite_isRoot
  convert Set.infinite_univ (α := ℂ)
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (b / x j) (hw j)
  have := hroot t
  rwa [ht, div_mul_cancel₀ _ (by simpa using hxj)] at this

lemma Setup.common_zero (H : Setup w d f) (x : Fin n → ℂ)
    (hx : ∀ i, eval x (pderiv i f) = 0) : x = 0 :=
  common_zero_eq_zero H.pos H.hom H.iso x hx

lemma Setup.wd (H : Setup w d f) (i : Fin n) : w i ≤ d := by
  have := H.big i; omega

end Yau
