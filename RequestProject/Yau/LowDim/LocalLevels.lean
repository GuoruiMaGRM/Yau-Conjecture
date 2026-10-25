import RequestProject.Yau.LowDim.LocalCriterion
import RequestProject.Yau.LowDim.QuadraticHeavy

/-!
# Combining local criteria degree by degree

`LocalSquareCondition` requires local membership of `a²` in `I_r` at every
nonzero common zero. `OneLightLocalEuler` requires the local Euler relation
for the restriction obtained by setting the unique light variable to zero.
These join the three elementary criteria to give the theorem below.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The local square condition at degree `r`: for `a ∈ S_r ∩ √I_r` and a nonzero common zero `x`, some `s` satisfies `s(x) ≠ 0` and `s a² ∈ I_r`. -/
def LocalSquareCondition (w : Fin n → ℕ) (f : Poly n) (r : ℕ) : Prop :=
  ∀ a : Poly n, a.IsWeightedHomogeneous w r → a ∈ (partialIdeal w f r).radical →
    ∀ x : Fin n → ℂ, x ≠ 0 → (∀ i, r < w i → eval x (pderiv i f) = 0) →
      ∃ s, eval x s ≠ 0 ∧ s * a ^ 2 ∈ partialIdeal w f r

/-- There is one light variable `u`, and `f|_{x_u=0}` satisfies `LocalEulerAt` at every nonzero critical point with `x_u=0`. -/
def OneLightLocalEuler (w : Fin n → ℕ) (f : Poly n) (r : ℕ) : Prop :=
  ∃ u : Fin n, (∀ l, l ≠ u → r < w l) ∧
    ∀ x : Fin n → ℂ, x ≠ 0 → x u = 0 → (∀ k, eval x (pderiv k (killV u f)) = 0) →
      LocalEulerAt (killV u f) x

/-- Any of the five degree-by-degree criteria gives the square-deformation property without the stratum theorem. -/
theorem Setup.squareDeformationProperty_of_local_levels (H : Setup w d f)
    (hlev : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r ∨
        QuadraticIn (Finset.univ.filter fun i => r < w i) f ∨
        OneLightLocalEuler w f r ∨ LocalSquareCondition w f r) :
    SquareDeformationProperty w d f := by
  intro r a ha h3 hrad
  suffices a = 0 by rw [this]; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; exact H.radical_zero a ha hrad
  rcases hlev r hr h3 with hY | hfin | hQ | ⟨u, hheavy, hE⟩ | hL
  · exact H.radical_of_heavy_subsingleton r hY a ha hrad
  · exact H.radical_of_heavyRestrictionIsolated r hfin a ha hrad
  · exact H.radical_of_quadratic r hQ a ha hrad
  · exact H.radical_of_one_light_localEuler hr h3 hheavy hE a ha hrad
  · exact H.radical_of_local_sq hr h3 a ha (hL a ha hrad)

/-- The main theorem when `2w_i < d` and every degree `0 < 3r < d` satisfies one of: at most one heavy variable; isolated restriction to the heavy coordinate subspace; quadratic dependence on heavy variables; one light variable with the local Euler relation; or the local square condition. -/
theorem yau_conjecture_local_levelwise (w : Fin n → ℕ) (d : ℕ) (f : Poly n)
    (hw : ∀ i, 0 < w i) (hf : f.IsWeightedHomogeneous w d)
    (hbig : ∀ i, 2 * w i < d) (hcrit : HasIsolatedCriticalPoint f)
    (hlev : ∀ r, 0 < r → 3 * r < d →
      (∀ i j, r < w i → r < w j → i = j) ∨ HeavyRestrictionIsolated w f r ∨
        QuadraticIn (Finset.univ.filter fun i => r < w i) f ∨
        OneLightLocalEuler w f r ∨ LocalSquareCondition w f r)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 :=
  have H : Setup w d f :=
    ⟨hw, hf, hbig, isIsolatedSingularity_of_hasIsolatedCriticalPoint hw hf hcrit⟩
  H.no_neg_derivation (H.squareDeformationProperty_of_local_levels hlev) k hk δ hδ

end Yau
