import RequestProject.Yau.Basic.Convergent
import RequestProject.Yau.Basic.Basic

/-!
# Polynomial and analytic Milnor algebras: Lemma A.1

If an ideal `I ⊆ ℂ[x]` contains a power of every variable, then the natural map
`ℂ[x]/I → ℂ{x}/Iℂ{x}` is an isomorphism of `ℂ`-algebras.
The proof truncates power series to a finite box of multi-indices and shows that
this truncation is multiplicative modulo `I`.
-/

open MvPowerSeries

noncomputable section

namespace Yau

variable {n : ℕ}

/-- The extension of `I ⊆ ℂ[x]` to the convergent power series ring `𝒪 = ℂ{x}`. -/
abbrev convIdeal (I : Ideal (Poly n)) : Ideal (ConvSeries n) := I.map polyToConv

section Box

variable (I : Ideal (Poly n)) (b : Fin n →₀ ℕ)

/-- If `x_i^{b_i+1} ∈ I` for every `i`, a polynomial with no monomial in the box `α ≤ b` belongs to `I`. -/
lemma mem_of_coeff_box (hI : ∀ i, (MvPolynomial.X i : Poly n) ^ (b i + 1) ∈ I) (p : Poly n)
    (hp : ∀ α ≤ b, p.coeff α = 0) : p ∈ I := by
  classical
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun α hα => ?_
  have hnot : ¬ α ≤ b := fun h => (MvPolynomial.mem_support_iff.mp hα) (hp α h)
  obtain ⟨i, hi⟩ : ∃ i, b i < α i := by
    by_contra h; push_neg at h; exact hnot (fun i => h i)
  have hle : Finsupp.single i (b i + 1) ≤ α := by
    intro j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Ne.symm hj]
  have : MvPolynomial.monomial α (p.coeff α) = (MvPolynomial.X i) ^ (b i + 1) *
      MvPolynomial.monomial (α - Finsupp.single i (b i + 1)) (p.coeff α) := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul,
      add_tsub_cancel_of_le hle]
  rw [this]
  exact I.mul_mem_right _ (hI i)

/-- Truncation to the box is multiplicative modulo `I`. -/
lemma trunc_mul_sub_mem (hI : ∀ i, (MvPolynomial.X i : Poly n) ^ (b i + 1) ∈ I)
    (F G : MvPowerSeries (Fin n) ℂ) :
    trunc' ℂ b (F * G) - trunc' ℂ b F * trunc' ℂ b G ∈ I := by
  classical
  apply mem_of_coeff_box I b hI
  intro α hα
  rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos hα, MvPolynomial.coeff_mul, coeff_mul,
    sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h1 : p.1 ≤ b := le_trans (hp ▸ le_self_add) hα
  have h2 : p.2 ≤ b := le_trans (hp ▸ le_add_self) hα
  rw [coeff_trunc', coeff_trunc', if_pos h1, if_pos h2]

/-- Truncation followed by projection to `ℂ[x]/I` defines a ring homomorphism on `ℂ[[x]]`. -/
def boxTrunc (hI : ∀ i, (MvPolynomial.X i : Poly n) ^ (b i + 1) ∈ I) :
    MvPowerSeries (Fin n) ℂ →+* Poly n ⧸ I where
  toFun F := Ideal.Quotient.mk I (trunc' ℂ b F)
  map_one' := by simp [trunc'_one]
  map_mul' F G := by
    rw [← map_mul, Ideal.Quotient.eq]
    exact trunc_mul_sub_mem I b hI F G
  map_zero' := by simp
  map_add' F G := by simp

variable {I b}

lemma boxTrunc_coe (hI : ∀ i, (MvPolynomial.X i : Poly n) ^ (b i + 1) ∈ I) (p : Poly n) :
    boxTrunc I b hI (p : MvPowerSeries (Fin n) ℂ) = Ideal.Quotient.mk I p := by
  classical
  show Ideal.Quotient.mk I _ = _
  rw [Ideal.Quotient.eq]
  apply mem_of_coeff_box I b hI
  intro α hα
  rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos hα, MvPolynomial.coeff_coe, sub_self]

/-- The first index `i` satisfying `b i < α i`, when one exists. -/
def firstBig (b α : Fin n →₀ ℕ) : Option (Fin n) :=
  (Finset.univ.filter (fun j => b j < α j)).min

lemma lt_of_firstBig {b α : Fin n →₀ ℕ} {i : Fin n} (h : firstBig b α = some i) :
    b i < α i := by
  have := Finset.mem_of_min h
  simpa using this

lemma exists_firstBig {b α : Fin n →₀ ℕ} (h : ¬ α ≤ b) : ∃ i, firstBig b α = some i := by
  have hne : (Finset.univ.filter (fun j => b j < α j)).Nonempty := by
    by_contra h'
    apply h
    intro j
    by_contra hj
    exact h' ⟨j, by simp; omega⟩
  obtain ⟨i, hi⟩ := Finset.min_of_nonempty hne
  exact ⟨i, hi⟩

lemma firstBig_le {b α : Fin n →₀ ℕ} (h : α ≤ b) : firstBig b α = none := by
  show (Finset.univ.filter (fun j => b j < α j)).min = ⊤
  rw [Finset.min_eq_top]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_lt]
  exact h j

/-- The `i`th summand of `F - trunc F = ∑ᵢ x_i^{b_i+1} Gᵢ`, collecting monomials whose first exponent outside the box is the `i`th. -/
def boxPiece (b : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ) (i : Fin n) :
    MvPowerSeries (Fin n) ℂ :=
  fun β => if firstBig b (β + Finsupp.single i (b i + 1)) = some i then
    coeff (β + Finsupp.single i (b i + 1)) F else 0

lemma coeff_boxPiece (b : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ) (i : Fin n)
    (β : Fin n →₀ ℕ) :
    coeff β (boxPiece b F i) = if firstBig b (β + Finsupp.single i (b i + 1)) = some i then
    coeff (β + Finsupp.single i (b i + 1)) F else 0 := rfl

lemma isConvergent_boxPiece (b : Fin n →₀ ℕ) {F : MvPowerSeries (Fin n) ℂ}
    (hF : IsConvergent F) (i : Fin n) : IsConvergent (boxPiece b F i) := by
  obtain ⟨C, R, hR, h⟩ := hF
  have hC := IsConvergent.nonneg_const h
  refine ⟨C * R ^ (b i + 1), R, hR, fun β => ?_⟩
  rw [coeff_boxPiece]
  split_ifs
  · refine (h _).trans (le_of_eq ?_)
    rw [map_add, pow_add, Finsupp.degree_single]; ring
  · rw [norm_zero]; positivity

lemma sub_trunc_eq_sum (b : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F - (trunc' ℂ b F : MvPowerSeries (Fin n) ℂ) =
      ∑ i, (X i) ^ (b i + 1) * boxPiece b F i := by
  classical
  ext α
  rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', map_sum]
  simp_rw [X_pow_eq, coeff_monomial_mul, one_mul, coeff_boxPiece]
  have key : ∀ i, (if Finsupp.single i (b i + 1) ≤ α then
      (if firstBig b (α - Finsupp.single i (b i + 1) + Finsupp.single i (b i + 1)) = some i then
        coeff (α - Finsupp.single i (b i + 1) + Finsupp.single i (b i + 1)) F else 0) else 0) =
      if firstBig b α = some i then coeff α F else 0 := by
    intro i
    split_ifs with h1 h2 h3 h3 h3
    · rw [tsub_add_cancel_of_le h1]
    · rw [tsub_add_cancel_of_le h1] at h2; contradiction
    · rw [tsub_add_cancel_of_le h1] at h2; contradiction
    · rfl
    · exfalso; apply h1
      have := lt_of_firstBig h3
      intro j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Ne.symm hj]
    · rfl
  simp_rw [key]
  by_cases hα : α ≤ b
  · rw [if_pos hα, sub_self, firstBig_le hα]; simp
  · rw [if_neg hα, sub_zero]
    obtain ⟨i, hi⟩ := exists_firstBig hα
    simp_rw [hi, Option.some.injEq]
    rw [Finset.sum_ite_eq]; simp

/-- Every convergent power series is congruent modulo `I𝒪` to its truncation to the box. -/
lemma sub_trunc_mem_convIdeal (hI : ∀ i, (MvPolynomial.X i : Poly n) ^ (b i + 1) ∈ I)
    (F : ConvSeries n) :
    F - polyToConv (trunc' ℂ b (F : MvPowerSeries (Fin n) ℂ)) ∈ convIdeal I := by
  have hconv : ∀ i, boxPiece b (F : MvPowerSeries (Fin n) ℂ) i ∈ ConvSeries n :=
    fun i => isConvergent_boxPiece b F.2 i
  have heq : F - polyToConv (trunc' ℂ b (F : MvPowerSeries (Fin n) ℂ)) =
      ∑ i, polyToConv ((MvPolynomial.X i : Poly n) ^ (b i + 1)) * ⟨_, hconv i⟩ := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, polyToConv_coe, sub_trunc_eq_sum, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Subalgebra.coe_mul, polyToConv_coe]
    simp
  rw [heq]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hI i))

end Box

variable {I : Ideal (Poly n)}

lemma exists_box (hI : ∀ i, ∃ N : ℕ, (MvPolynomial.X i : Poly n) ^ N ∈ I) :
    ∃ b : Fin n →₀ ℕ, ∀ i, (MvPolynomial.X i : Poly n) ^ (b i + 1) ∈ I := by
  choose N hN using hI
  refine ⟨Finsupp.equivFunOnFinite.symm N, fun i => ?_⟩
  rw [Finsupp.equivFunOnFinite_symm_apply_apply, pow_succ]
  exact I.mul_mem_right _ (hN i)

/-- Analytic ideal membership implies polynomial ideal membership for polynomials. -/
theorem mem_of_polyToConv_mem_convIdeal
    (hI : ∀ i, ∃ N : ℕ, (MvPolynomial.X i : Poly n) ^ N ∈ I)
    {p : Poly n} (hp : polyToConv p ∈ convIdeal I) : p ∈ I := by
  obtain ⟨b, hb⟩ := exists_box hI
  let φ : ConvSeries n →+* Poly n ⧸ I :=
    (boxTrunc I b hb).comp (ConvSeries n).val.toRingHom
  have hφ : ∀ q : Poly n, φ (polyToConv q) = Ideal.Quotient.mk I q := fun q => by
    show boxTrunc I b hb ((polyToConv q : ConvSeries n) : MvPowerSeries (Fin n) ℂ) = _
    rw [polyToConv_coe, boxTrunc_coe]
  have hle : convIdeal I ≤ RingHom.ker φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact hq
  have := hle hp
  rw [RingHom.mem_ker, hφ, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem polyToConv_mem_convIdeal_iff (hI : ∀ i, ∃ N : ℕ, (MvPolynomial.X i : Poly n) ^ N ∈ I)
    (p : Poly n) : polyToConv p ∈ convIdeal I ↔ p ∈ I :=
  ⟨mem_of_polyToConv_mem_convIdeal hI, fun h => Ideal.mem_map_of_mem _ h⟩

/-- The natural map `ℂ[x]/I → 𝒪/I𝒪`. -/
def quotientToConv (I : Ideal (Poly n)) : (Poly n ⧸ I) →ₐ[ℂ] ConvSeries n ⧸ convIdeal I :=
  Ideal.quotientMapₐ (convIdeal I) polyToConv Ideal.le_comap_map

lemma quotientToConv_mk (p : Poly n) :
    quotientToConv I (Ideal.Quotient.mk I p) = Ideal.Quotient.mk (convIdeal I) (polyToConv p) :=
  rfl

lemma quotientToConv_bijective (hI : ∀ i, ∃ N : ℕ, (MvPolynomial.X i : Poly n) ^ N ∈ I) :
    Function.Bijective (quotientToConv I) := by
  constructor
  · intro a a' h
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a'
    rw [quotientToConv_mk, quotientToConv_mk, Ideal.Quotient.eq, ← map_sub] at h
    rw [Ideal.Quotient.eq]
    exact mem_of_polyToConv_mem_convIdeal hI h
  · intro a
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, hb⟩ := exists_box hI
    refine ⟨Ideal.Quotient.mk I (trunc' ℂ b (F : MvPowerSeries (Fin n) ℂ)), ?_⟩
    rw [quotientToConv_mk, Ideal.Quotient.eq, ← neg_sub]
    exact neg_mem (sub_trunc_mem_convIdeal hb F)

/-- Lemma A.1: if `I` contains a power of every variable, then `ℂ[x]/I ≅ ℂ{x}/Iℂ{x}` as `ℂ`-algebras. -/
def quotientEquivConv (hI : ∀ i, ∃ N : ℕ, (MvPolynomial.X i : Poly n) ^ N ∈ I) :
    (Poly n ⧸ I) ≃ₐ[ℂ] ConvSeries n ⧸ convIdeal I :=
  AlgEquiv.ofBijective (quotientToConv I) (quotientToConv_bijective hI)

end Yau
