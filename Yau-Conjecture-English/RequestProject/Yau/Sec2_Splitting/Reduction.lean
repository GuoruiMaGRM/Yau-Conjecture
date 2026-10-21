import RequestProject.Yau.Sec2_Splitting.Elementary

/-! # Elementary automorphisms and deletion of variables -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ}

/-! ### Elementary automorphisms `x_v ↦ a x_v + g`, with `g` independent of `x_v` -/

section elem

/-- The substitution `x_v ↦ a x_v + g`. -/
def elem (v : Fin n) (a : ℂ) (g : Poly n) : Poly n →ₐ[ℂ] Poly n :=
  aeval (Function.update X v (C a * X v + g))

variable {v : Fin n} {a : ℂ} {g : Poly n}

@[simp] lemma elem_X_self : elem v a g (X v) = C a * X v + g := by simp [elem]

lemma elem_X_ne {j : Fin n} (h : j ≠ v) : elem v a g (X j) = X j := by
  simp [elem, Function.update_of_ne h]

lemma FreeOf.elem_eq {p : Poly n} (hp : FreeOf v p) : elem v a g p = p :=
  hp.aeval_eq _ fun j hj => by simp [Function.update_of_ne hj]

lemma elem_comp {b : ℂ} {g' : Poly n} (hg' : FreeOf v g') :
    (elem v a g).comp (elem v b g') = elem v (a * b) (C b * g + g') := by
  apply algHom_ext; intro j
  by_cases hj : j = v
  · subst hj
    simp only [AlgHom.comp_apply, elem_X_self, map_add, map_mul, hg'.elem_eq, algHom_C,
      MvPolynomial.algebraMap_eq]
    ring
  · simp [elem_X_ne hj]

lemma elem_one_zero : elem v 1 0 = AlgHom.id ℂ (Poly n) := by
  apply algHom_ext; intro j
  by_cases hj : j = v
  · subst hj; simp
  · simp [elem_X_ne hj]

/-- The elementary automorphism as an algebra isomorphism. -/
def elemEquiv (v : Fin n) (a : ℂ) (ha : a ≠ 0) (g : Poly n) (hg : FreeOf v g) :
    Poly n ≃ₐ[ℂ] Poly n :=
  AlgEquiv.ofAlgHom (elem v a g) (elem v a⁻¹ (-(C a⁻¹ * g)))
    (by
      rw [elem_comp ((freeOf_C _).mul hg).neg, mul_inv_cancel₀ ha,
        show C a⁻¹ * g + -(C a⁻¹ * g) = 0 by ring, elem_one_zero])
    (by
      rw [elem_comp hg, inv_mul_cancel₀ ha,
        show C a * -(C a⁻¹ * g) + g = 0 by
          rw [mul_neg, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha]; simp, elem_one_zero])

lemma elem_isWH {w : Fin n → ℕ} (hgw : g.IsWeightedHomogeneous w (w v)) (j : Fin n) :
    (elem v a g (X j)).IsWeightedHomogeneous w (w j) := by
  by_cases hj : j = v
  · subst hj
    rw [elem_X_self]
    have := (isWeightedHomogeneous_C w a).mul (isWeightedHomogeneous_X ℂ w j)
    rw [zero_add] at this
    exact this.add hgw
  · rw [elem_X_ne hj]; exact isWeightedHomogeneous_X _ _ _

/-- Transfer along a weight-preserving elementary automorphism. -/
lemma elem_transfer {w : Fin n → ℕ} {f : Poly n} (ha : a ≠ 0) (hg : FreeOf v g)
    (hgw : g.IsWeightedHomogeneous w (w v)) :
    (IsIsolatedSingularity f ↔ IsIsolatedSingularity (elem v a g f)) ∧
      (NoNegDer w (elem v a g f) → NoNegDer w f) := by
  have := auto_transfer (f := f) (elemEquiv v a ha g hg) (elem_isWH hgw) (by
    intro j
    exact elem_isWH (by
      have := (isWeightedHomogeneous_C w (-a⁻¹)).mul hgw
      rw [zero_add] at this
      rwa [show -(C a⁻¹ * g) = C (-a⁻¹) * g by rw [C_neg, neg_mul]]) j)
  exact this

lemma elem_isWH' {w : Fin n → ℕ} (hgw : g.IsWeightedHomogeneous w (w v)) {p : Poly n} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) : (elem v a g p).IsWeightedHomogeneous w e :=
  algHom_isWH _ (elem_isWH hgw) hp

/-- An elementary automorphism in `x_v` preserves independence of another variable. -/
lemma FreeOf.elem_other {u : Fin n} (huv : u ≠ v) (hg : FreeOf u g) {p : Poly n}
    (hp : FreeOf u p) : FreeOf u (elem v a g p) := by
  have : (killV u).comp (elem v a g) = (elem v a g).comp (killV u) := by
    apply algHom_ext; intro j
    simp only [AlgHom.comp_apply]
    by_cases hj : j = v
    · subst hj
      rw [elem_X_self, killV_X_ne (Ne.symm huv), elem_X_self, map_add, map_mul, killV_C,
        killV_X_ne (Ne.symm huv)]
      unfold FreeOf at hg; rw [hg]
    · rw [elem_X_ne hj]
      by_cases hju : j = u
      · subst hju; simp
      · rw [killV_X_ne hju, elem_X_ne hj]
  unfold FreeOf at hp ⊢
  have h2 := congrArg (fun F : Poly n →ₐ[ℂ] Poly n => F p) this
  simp only [AlgHom.comp_apply] at h2
  rw [h2, hp]

end elem

/-! ### Independence of a variable and partial derivatives -/

lemma pderiv_killV_of_ne {u i : Fin n} (h : i ≠ u) (q : Poly n) :
    pderiv i (killV u q) = killV u (pderiv i q) := by
  classical
  rw [killV, pderiv_aeval, Finset.sum_eq_single i]
  · simp [Function.update_of_ne h]
  · intro j _ hji
    by_cases hj : j = u
    · subst hj; simp
    · simp [Function.update_of_ne hj, pderiv_X, hji]
  · simp

lemma FreeOf.pderiv_of_ne {u i : Fin n} (h : i ≠ u) {q : Poly n} (hq : FreeOf u q) :
    FreeOf u (pderiv i q) := by
  unfold FreeOf at *
  rw [← pderiv_killV_of_ne h, hq]

/-! ### Deleting a variable -/

section remove

/-- Set `x_u=0` and view the result in the polynomial ring in the remaining variables. -/
def psiU (u : Fin (n + 1)) : Poly (n + 1) →ₐ[ℂ] Poly n := aeval (Fin.insertNth u 0 X)

/-- The inclusion of the polynomial ring in the remaining variables. -/
def sU (u : Fin (n + 1)) : Poly n →ₐ[ℂ] Poly (n + 1) := rename (Fin.succAbove u)

variable (u : Fin (n + 1))

lemma psiU_sU (q : Poly n) : psiU u (sU u q) = q := by
  rw [psiU, sU, aeval_rename]
  have : (Fin.insertNth u (0 : Poly n) X ∘ Fin.succAbove u) = X := by
    funext j; simp
  rw [this, aeval_X_left_apply]

lemma sU_psiU (p : Poly (n + 1)) : sU u (psiU u p) = killV u p := by
  have : (sU u).comp (psiU u) = killV u := by
    apply algHom_ext; intro j
    simp only [AlgHom.comp_apply, psiU, aeval_X]
    refine Fin.succAboveCases u ?_ (fun k => ?_) j
    · simp
    · rw [Fin.insertNth_apply_succAbove, killV_X_ne (Fin.succAbove_ne u k), sU, rename_X]
  exact congrArg (fun F : Poly (n + 1) →ₐ[ℂ] Poly (n + 1) => F p) this

@[simp] lemma psiU_X_self : psiU u (X u) = 0 := by simp [psiU]

lemma sub_sU_psiU_mem (p : Poly (n + 1)) :
    p - sU u (psiU u p) ∈ Ideal.span {(X u : Poly (n + 1))} := by
  rw [sU_psiU]
  obtain ⟨K, hK⟩ := exists_killV_decomp (v := u) p
  rw [Ideal.mem_span_singleton]
  exact ⟨K, by rw [sub_eq_iff_eq_add']; exact hK⟩

lemma psiU_isWH {w : Fin (n + 1) → ℕ} {p : Poly (n + 1)} {e : ℕ}
    (hp : p.IsWeightedHomogeneous w e) :
    (psiU u p).IsWeightedHomogeneous (w ∘ Fin.succAbove u) e := by
  refine aeval_isWH (fun j => ?_) hp
  refine Fin.succAboveCases u ?_ (fun k => ?_) j
  · simp [isWeightedHomogeneous_zero]
  · rw [Fin.insertNth_apply_succAbove]
    exact isWeightedHomogeneous_X _ _ _

lemma sU_isWH {w : Fin (n + 1) → ℕ} {q : Poly n} {e : ℕ}
    (hq : q.IsWeightedHomogeneous (w ∘ Fin.succAbove u) e) :
    (sU u q).IsWeightedHomogeneous w e := by
  exact algHom_isWH (rename _) (fun j => by rw [rename_X]; exact isWeightedHomogeneous_X _ _ _) hq

lemma FreeOf.eq_sU_psiU {G : Poly (n + 1)} (hG : FreeOf u G) : G = sU u (psiU u G) := by
  rw [sU_psiU]; exact hG.symm

end remove

lemma pderiv_rename_of_ne {m : ℕ} (ι : Fin m → Fin n) {i : Fin n} (hi : ∀ j, ι j ≠ i)
    (p : Poly m) : pderiv i (rename ι p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp [Derivation.leibniz, hp, pderiv_X, hi k]

/-! ### An abstract variable-deletion lemma -/

section abstract

variable {m : ℕ} {w : Fin m → ℕ} {w' : Fin n → ℕ} {f : Poly m} {F : Poly n}

/-- Delete variables along a weight-preserving retraction. -/
lemma removal_transfer (ψ : Poly m →ₐ[ℂ] Poly n) (s : Poly n →ₐ[ℂ] Poly m)
    (hψs : ∀ q, ψ (s q) = q)
    (hψw : ∀ p e, p.IsWeightedHomogeneous w e → (ψ p).IsWeightedHomogeneous w' e)
    (hsw : ∀ q e, q.IsWeightedHomogeneous w' e → (s q).IsWeightedHomogeneous w e)
    (hker : ∀ p, p - s (ψ p) ∈ jacobianIdeal f)
    (hsJ : ∀ j, s (pderiv j F) ∈ jacobianIdeal f)
    (hψJ : ∀ i, ψ (pderiv i f) ∈ jacobianIdeal F) :
    (IsIsolatedSingularity f ↔ IsIsolatedSingularity F) ∧ (NoNegDer w' F → NoNegDer w f) := by
  have hsJ' : ∀ q ∈ jacobianIdeal F, s q ∈ jacobianIdeal f := by
    intro q hq
    have : jacobianIdeal F ≤ (jacobianIdeal f).comap s := by
      rw [jacobianIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hsJ j
    exact this hq
  have hψJ' : ∀ p ∈ jacobianIdeal f, ψ p ∈ jacobianIdeal F := by
    intro p hp
    have : jacobianIdeal f ≤ (jacobianIdeal F).comap ψ := by
      rw [jacobianIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩; exact hψJ i
    exact this hp
  have h2 : ∀ q e, q.IsWeightedHomogeneous w' e →
      ∃ p, p.IsWeightedHomogeneous w e ∧ ψ p = q :=
    fun q e hq => ⟨s q, hsw q e hq, hψs q⟩
  have h3 : ∀ p, ψ p ∈ jacobianIdeal F ↔ p ∈ jacobianIdeal f := by
    intro p
    refine ⟨fun h => ?_, hψJ' p⟩
    have := Ideal.add_mem _ (hker p) (hsJ' _ h)
    simpa using this
  exact ⟨isolated_transfer ψ h2 h3, noNegDer_transfer ψ hψw h2 h3⟩

end abstract

end Yau
