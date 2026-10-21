import RequestProject.Yau.Sec3_Radical.Radical

/-! # The core proof after removal of quadratic variables -/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ} {d : ℕ} {f : Poly n}

/-- The main theorem after splitting: there is no nonzero negative-degree derivation. -/
theorem Setup.no_neg_derivation (H : Setup w d f) (hV : SquareDeformationProperty w d f)
    (k : ℤ) (hk : k < 0) (δ : Derivation ℂ (MilnorAlgebra f) (MilnorAlgebra f))
    (hδ : IsDerivationOfDegree w f k δ) : δ = 0 := by
  classical
  by_contra hδ0
  set s := k.natAbs with hs_def
  have hs : 0 < s := by omega
  have hks : k = -(s : ℤ) := by omega
  rw [hks] at hδ
  obtain ⟨h, hh, hlift⟩ := lift_of_deg δ hδ
  have hJ : ∀ p ∈ jacobianIdeal f, polyDer h p ∈ jacobianIdeal f := by
    intro p hp
    rw [← Ideal.Quotient.eq_zero_iff_mem, hlift, Ideal.Quotient.eq_zero_iff_mem.mpr hp,
      map_zero]
  have hne : h ≠ 0 := by
    rintro rfl
    apply hδ0
    ext a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← hlift]
    simp [polyDer_apply]
  obtain ⟨s', hs', h', hh', hne', hJ', h2'⟩ := H.minimum hs hh hJ hne
  obtain ⟨j0, hj0⟩ : ∃ j, h' j ≠ 0 := by
    by_contra hc; push_neg at hc; exact hne' (funext hc)
  obtain ⟨k0, hk0mem, hk0min⟩ := Finset.exists_min_image
    (Finset.univ.filter fun j => h' j ≠ 0) w ⟨j0, by simp [hj0]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0mem hk0min
  have hk0s : s' ≤ w k0 := by
    by_contra hc; exact hk0mem ((hh' k0).2 (by omega))
  set r := w k0 - s'
  have hr : ∀ j, w j ≤ r → h' j = 0 := by
    intro j hj
    by_contra hc
    have := hk0min j hc
    omega
  obtain ⟨hIr, hI2⟩ := H.quotient hh' hJ' h2' r hr
  have hrad := H.orbit hs' hh' _ hIr hI2 k0
  exact hk0mem (H.radical hV r (h' k0) (hh' k0).1 hrad)

end Yau
