import RequestProject.Yau.Sec2_Splitting.Reduction

/-! # Lemma 2.1: removal of quadratic variables -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ### Concrete variable-deletion lemmas -/

lemma pderiv_X_of_ne {i j : Fin n} (h : i ≠ j) : pderiv i (X j : Poly n) = 0 := by
  classical
  simp [pderiv_X, Ne.symm h]

/-- Remove `x_u` from `a x_u² + F`. -/
lemma single_removal {w : Fin (n + 1) → ℕ} {u : Fin (n + 1)} {f : Poly (n + 1)} {a : ℂ}
    (ha : a ≠ 0) {F : Poly n} (hf : f = C a * X u ^ 2 + sU u F) :
    (IsIsolatedSingularity f ↔ IsIsolatedSingularity F) ∧
      (NoNegDer (w ∘ Fin.succAbove u) F → NoNegDer w f) := by
  have hsF : pderiv u (sU u F) = 0 :=
    pderiv_rename_of_ne _ (fun j => Fin.succAbove_ne u j) F
  have hdu : pderiv u f = C (2 * a) * X u := by
    rw [hf, map_add, hsF, add_zero, Derivation.leibniz, Derivation.leibniz_pow, derivation_C,
      pderiv_X_self]
    simp only [smul_eq_mul, nsmul_eq_mul, C_mul]; simp
    rw [show (C 2 : Poly (n + 1)) = 2 from map_ofNat C 2]; ring
  have hXu : (X u : Poly (n + 1)) ∈ jacobianIdeal f := by
    have : (X u : Poly (n + 1)) = C (2 * a)⁻¹ * pderiv u f := by
      rw [hdu, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by simpa using ha), C_1, one_mul]
    rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, rfl⟩)
  have hdj : ∀ j, pderiv (Fin.succAbove u j) f = sU u (pderiv j F) := by
    intro j
    rw [hf, map_add, Derivation.leibniz, Derivation.leibniz_pow, derivation_C,
      pderiv_X_of_ne (Fin.succAbove_ne u j), sU, pderiv_rename Fin.succAbove_right_injective]
    simp
  refine removal_transfer (psiU u) (sU u) (psiU_sU u) (fun p e hp => psiU_isWH u hp)
    (fun q e hq => sU_isWH u hq) (fun p => ?_) (fun j => ?_) (fun i => ?_)
  · have h1 := sub_sU_psiU_mem u p
    have : Ideal.span {(X u : Poly (n + 1))} ≤ jacobianIdeal f := by
      rw [Ideal.span_le]; simpa using hXu
    exact this h1
  · rw [← hdj]; exact Ideal.subset_span ⟨_, rfl⟩
  · refine Fin.succAboveCases u ?_ (fun j => ?_) i
    · rw [hdu, map_mul, psiU_X_self, mul_zero]; exact Ideal.zero_mem _
    · rw [hdj, psiU_sU]; exact Ideal.subset_span ⟨j, rfl⟩

lemma psiU_killV_succAbove (u : Fin (n + 1)) (v' : Fin n) (p : Poly (n + 1)) :
    psiU u (killV (Fin.succAbove u v') p) = killV v' (psiU u p) := by
  have : (psiU u).comp (killV (Fin.succAbove u v')) = (killV v').comp (psiU u) := by
    apply algHom_ext; intro j
    simp only [AlgHom.comp_apply]
    refine Fin.succAboveCases u ?_ (fun k => ?_) j
    · rw [killV_X_ne (Fin.succAbove_ne u v').symm]; simp
    · by_cases hk : k = v'
      · subst hk; simp [psiU]
      · rw [killV_X_ne (fun h => hk (Fin.succAbove_right_injective h))]
        simp only [psiU, aeval_X, Fin.insertNth_apply_succAbove]
        rw [killV_X_ne hk]
  exact congrArg (fun F : Poly (n + 1) →ₐ[ℂ] Poly n => F p) this

/-- Remove `x_u,x_v` from `x_u x_v + F`. -/
lemma pair_removal {w : Fin (n + 2) → ℕ} {u : Fin (n + 2)} {v' : Fin (n + 1)}
    {f : Poly (n + 2)} {F : Poly n}
    (hf : f = X u * X (Fin.succAbove u v') + sU u (sU v' F)) :
    (IsIsolatedSingularity f ↔ IsIsolatedSingularity F) ∧
      (NoNegDer (w ∘ Fin.succAbove u ∘ Fin.succAbove v') F → NoNegDer w f) := by
  set v := Fin.succAbove u v' with hv
  have huv : u ≠ v := (Fin.succAbove_ne u v').symm
  have hrr : ∀ q : Poly n, sU u (sU v' q) =
      rename (Fin.succAbove u ∘ Fin.succAbove v') q := by
    intro q; rw [sU, sU, rename_rename]
  have hinj : Function.Injective (Fin.succAbove u ∘ Fin.succAbove v') :=
    Fin.succAbove_right_injective.comp Fin.succAbove_right_injective
  have hzu : pderiv u (sU u (sU v' F)) = 0 := by
    rw [hrr]; exact pderiv_rename_of_ne _ (fun j => Fin.succAbove_ne u _) F
  have hzv : pderiv v (sU u (sU v' F)) = 0 := by
    rw [hrr]
    exact pderiv_rename_of_ne _ (fun j h =>
      Fin.succAbove_ne v' j (Fin.succAbove_right_injective h)) F
  have hdu : pderiv u f = X v := by
    rw [hf, map_add, hzu, Derivation.leibniz, pderiv_X_self, pderiv_X_of_ne huv]; simp
  have hdv : pderiv v f = X u := by
    rw [hf, map_add, hzv, Derivation.leibniz, pderiv_X_self, pderiv_X_of_ne huv.symm]; simp
  have hdj : ∀ j, pderiv (Fin.succAbove u (Fin.succAbove v' j)) f =
      sU u (sU v' (pderiv j F)) := by
    intro j
    have h1 : Fin.succAbove u (Fin.succAbove v' j) ≠ u := Fin.succAbove_ne u _
    have h2 : Fin.succAbove u (Fin.succAbove v' j) ≠ v :=
      fun h => Fin.succAbove_ne v' j (Fin.succAbove_right_injective h)
    rw [hf, map_add, Derivation.leibniz, pderiv_X_of_ne h1, pderiv_X_of_ne h2, hrr, hrr]
    rw [show Fin.succAbove u (Fin.succAbove v' j) = (Fin.succAbove u ∘ Fin.succAbove v') j
      from rfl, pderiv_rename hinj]
    simp
  have hXu : (X u : Poly (n + 2)) ∈ jacobianIdeal f := hdv ▸ Ideal.subset_span ⟨v, rfl⟩
  have hXv : (X v : Poly (n + 2)) ∈ jacobianIdeal f := hdu ▸ Ideal.subset_span ⟨u, rfl⟩
  have hψs : ∀ q, ((psiU v').comp (psiU u)) (((sU u).comp (sU v')) q) = q := by
    intro q; simp [psiU_sU]
  refine removal_transfer ((psiU v').comp (psiU u)) ((sU u).comp (sU v')) hψs
    (fun p e hp => psiU_isWH v' (psiU_isWH u hp))
    (fun q e hq => sU_isWH u (sU_isWH v' hq)) (fun p => ?_) (fun j => ?_) (fun i => ?_)
  · simp only [AlgHom.comp_apply]
    have e1 := sub_sU_psiU_mem u p
    have e2 := sub_sU_psiU_mem v' (psiU u p)
    rw [Ideal.mem_span_singleton] at e1 e2
    obtain ⟨K1, hK1⟩ := e1
    obtain ⟨K2, hK2⟩ := e2
    have : p - sU u (sU v' (psiU v' (psiU u p))) =
        X u * K1 + X v * sU u K2 := by
      have h3 := congrArg (sU u) hK2
      rw [map_sub, map_mul, sU, rename_X] at h3
      rw [← hK1]
      simp only [sU] at h3 ⊢
      rw [hv]
      linear_combination h3
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hXu) (Ideal.mul_mem_right _ _ hXv)
  · simp only [AlgHom.comp_apply]
    rw [← hdj]; exact Ideal.subset_span ⟨_, rfl⟩
  · simp only [AlgHom.comp_apply]
    refine Fin.succAboveCases u ?_ (fun k => ?_) i
    · rw [hdu, hv]; simp [psiU]
    · refine Fin.succAboveCases v' ?_ (fun j => ?_) k
      · rw [← hv, hdv]; simp [psiU]
      · rw [hdj, psiU_sU, psiU_sU]; exact Ideal.subset_span ⟨j, rfl⟩

end Yau
