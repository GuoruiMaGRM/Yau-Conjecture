import RequestProject.Yau.Basic.Basic
import RequestProject.Yau.CommAlg.Depth

/-!
# Homogeneous systems of parameters in `ℂ[x]`

Positive-degree weighted homogeneous polynomials whose quotient is finite
dimensional form a regular sequence in any order. The proof localizes at the
origin, applies the Cohen–Macaulay criterion using the coordinate regular
sequence, and then uses the grading to return to the polynomial ring.
This applies in particular to the partial derivatives in Lemmas 3.3 and B.1.
-/

open MvPolynomial RingTheory.Sequence IsLocalRing

noncomputable section

namespace Yau

/-! ### Ideal-membership descriptions of regular sequences -/

section RingLemmas

variable {A : Type*} [CommRing A]

lemma isSMulRegular_quotient_iff (I : Ideal A) (a : A) :
    IsSMulRegular (A ⧸ (I • ⊤ : Submodule A A)) a ↔ ∀ b : A, a * b ∈ I → b ∈ I := by
  have hI : (I • ⊤ : Submodule A A) = I := by
    rw [smul_eq_mul, Ideal.mul_top]
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  constructor
  · intro h b hb
    have := h (Submodule.Quotient.mk b) (by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hI]; exact hb)
    rwa [Submodule.Quotient.mk_eq_zero, hI] at this
  · intro h u hu
    induction u using Submodule.Quotient.induction_on with
    | _ b =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hI] at hu
    rw [Submodule.Quotient.mk_eq_zero, hI]
    exact h b hu

/-- A list is weakly regular on its ring if and only if each element is a non-zero-divisor modulo its predecessors. -/
lemma isWeaklyRegular_self_iff (rs : List A) :
    IsWeaklyRegular A rs ↔ ∀ i (h : i < rs.length), ∀ b : A,
      rs[i] * b ∈ Ideal.ofList (rs.take i) → b ∈ Ideal.ofList (rs.take i) := by
  rw [isWeaklyRegular_iff]
  exact forall_congr' fun i => forall_congr' fun h => isSMulRegular_quotient_iff _ _

lemma ofList_map {B : Type*} [CommRing B] (f : A →+* B) (l : List A) :
    Ideal.ofList (l.map f) = (Ideal.ofList l).map f := by
  rw [Ideal.ofList, Ideal.ofList, Ideal.map_span]
  congr 1
  ext x
  simp

/-- A non-zero-divisor modulo an ideal remains so after localization. -/
lemma localization_nzd (P : Ideal A) [P.IsPrime] (I : Ideal A) (a : A)
    (h : ∀ b, a * b ∈ I → b ∈ I) (c : Localization.AtPrime P)
    (hc : algebraMap A _ a * c ∈ I.map (algebraMap A (Localization.AtPrime P))) :
    c ∈ I.map (algebraMap A (Localization.AtPrime P)) := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  rw [← IsLocalization.mk'_one (M := P.primeCompl) (Localization.AtPrime P) a,
    ← IsLocalization.mk'_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at hc
  obtain ⟨t, ht, htab⟩ := hc
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  refine ⟨t, ht, h _ ?_⟩
  rw [mul_left_comm]; simpa [mul_assoc] using htab

/-- A regular sequence remains regular after localization at a prime ideal. -/
lemma isWeaklyRegular_localization (P : Ideal A) [P.IsPrime] (rs : List A)
    (h : IsWeaklyRegular A rs) :
    IsWeaklyRegular (Localization.AtPrime P) (rs.map (algebraMap A (Localization.AtPrime P))) := by
  rw [isWeaklyRegular_self_iff] at h ⊢
  intro i hi c hc
  simp only [List.length_map] at hi
  rw [List.getElem_map, ← List.map_take, ofList_map] at hc
  rw [← List.map_take, ofList_map]
  exact localization_nzd P _ _ (h i hi) c hc

end RingLemmas

variable {n : ℕ}

/-! ### The local ring at the origin -/

/-- The maximal ideal at the origin, the kernel of evaluation at zero. -/
def originIdeal (n : ℕ) : Ideal (Poly n) :=
  RingHom.ker (MvPolynomial.constantCoeff : Poly n →+* ℂ)

instance originIdeal_isMaximal : (originIdeal n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, by simp⟩

/-- The local ring `ℂ[x]_𝔪`. -/
abbrev LocalPoly (n : ℕ) := Localization.AtPrime (originIdeal n)

lemma X_mem_originIdeal (i : Fin n) : (X i : Poly n) ∈ originIdeal n := by
  simp [originIdeal]

lemma X_mul_mem_span_X {s : Set (Fin n)} {i : Fin n} (hi : i ∉ s) (b : Poly n)
    (h : X i * b ∈ Ideal.span (X '' s)) : b ∈ Ideal.span (X '' s) := by
  classical
  rw [mem_ideal_span_X_image] at h ⊢
  intro m hm
  have hm' : m + Finsupp.single i 1 ∈ (X i * b).support := by
    rw [mem_support_iff, mul_comm, coeff_mul_X]
    exact mem_support_iff.1 hm
  obtain ⟨j, hj, hjm⟩ := h _ hm'
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  refine ⟨j, hj, ?_⟩
  simpa [Finsupp.single_apply, Ne.symm hji] using hjm

lemma mem_take_finRange_iff (i : ℕ) (a : Fin n) :
    a ∈ (List.finRange n).take i ↔ (a : ℕ) < i := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [List.getElem_finRange, Fin.cast_mk]
    exact lt_of_lt_of_le hk (min_le_left _ _)
  · intro h
    refine ⟨a, by simp [h, a.2], ?_⟩
    simp

/-- The coordinate variables form a regular sequence in `ℂ[x]`. -/
theorem isWeaklyRegular_X :
    IsWeaklyRegular (Poly n) ((List.finRange n).map (X : Fin n → Poly n)) := by
  rw [isWeaklyRegular_self_iff]
  intro i hi b hb
  simp only [List.length_map, List.length_finRange] at hi
  have hset : {r | r ∈ ((List.finRange n).map (X : Fin n → Poly n)).take i} =
      X '' {j : Fin n | (j : ℕ) < i} := by
    ext r
    simp only [Set.mem_setOf_eq, ← List.map_take, List.mem_map, Set.mem_image,
      mem_take_finRange_iff]
  rw [Ideal.ofList, hset] at hb ⊢
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] at hb
  exact X_mul_mem_span_X (by simp) b hb

/-- If `ℂ[x]/I` is finite dimensional, the only prime of `ℂ[x]_𝔪` containing `I` is the maximal ideal. -/
lemma isMaximal_of_finite_quotient (I : Ideal (Poly n)) (hfin : Module.Finite ℂ (Poly n ⧸ I))
    (Q : Ideal (LocalPoly n)) (hQ : Q.IsPrime)
    (hIQ : I.map (algebraMap (Poly n) (LocalPoly n)) ≤ Q) : Q.IsMaximal := by
  set P := Q.comap (algebraMap (Poly n) (LocalPoly n)) with hPdef
  have hIP : I ≤ P := Ideal.map_le_iff_le_comap.1 hIQ
  have hPm : P ≤ originIdeal n := by
    have h1 := Ideal.comap_mono (f := algebraMap (Poly n) (LocalPoly n))
      (IsLocalRing.le_maximalIdeal hQ.ne_top)
    rwa [Localization.AtPrime.comap_maximalIdeal] at h1
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ Q
  have hPmax : P.IsMaximal := by
    have : Module.Finite ℂ (Poly n ⧸ P) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ hIP).toLinearMap
        (Ideal.Quotient.factor_surjective hIP)
    have : IsArtinianRing (Poly n ⧸ P) := IsArtinianRing.of_finite ℂ _
    exact Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hPeq : P = originIdeal n := hPmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hPm
  have hQeq : Q = IsLocalRing.maximalIdeal (LocalPoly n) := by
    rw [← IsLocalization.map_comap (originIdeal n).primeCompl (LocalPoly n) Q, ← hPdef, hPeq,
      Localization.AtPrime.map_eq_maximalIdeal]
  rw [hQeq]; infer_instance

/-! ### Homogeneous ideals -/

section Homogeneous

variable {w : Fin n → ℕ}

lemma ofList_eq_span_range (l : List (Poly n)) :
    Ideal.ofList l = Ideal.span (Set.range fun k : Fin l.length => l[k]) := by
  rw [Ideal.ofList]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_range, List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, k.2, rfl⟩

/-- An ideal generated by weighted homogeneous polynomials contains every homogeneous component of each of its elements. -/
lemma weightedHomogeneousComponent_mem_ofList (l : List (Poly n))
    (hl : ∀ r ∈ l, ∃ e, r.IsWeightedHomogeneous w e) {b : Poly n}
    (hb : b ∈ Ideal.ofList l) (c : ℕ) :
    weightedHomogeneousComponent w c b ∈ Ideal.ofList l := by
  classical
  rw [ofList_eq_span_range] at hb ⊢
  obtain ⟨coef, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
  rw [map_sum]
  refine Ideal.sum_mem _ fun k _ => ?_
  obtain ⟨e, he⟩ := hl l[k] (List.getElem_mem _)
  rw [weightedHomogeneousComponent_mul_of_right _ _ e c he]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  · exact Ideal.zero_mem _

lemma mem_of_forall_weightedHomogeneousComponent_mem (I : Ideal (Poly n)) (b : Poly n)
    (h : ∀ c, weightedHomogeneousComponent w c b ∈ I) : b ∈ I := by
  rw [← sum_weightedHomogeneousComponent w b,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp b)]
  exact Ideal.sum_mem _ fun c _ => h c

/-- A homogeneous polynomial in `Iℂ[x]_𝔪` already belongs to the homogeneous ideal `I`, for positive weights. -/
lemma mem_of_algebraMap_mem (hw : ∀ i, 0 < w i) (l : List (Poly n))
    (hl : ∀ r ∈ l, ∃ e, r.IsWeightedHomogeneous w e) {b : Poly n} {c : ℕ}
    (hb : b.IsWeightedHomogeneous w c)
    (h : algebraMap (Poly n) (LocalPoly n) b ∈
      (Ideal.ofList l).map (algebraMap (Poly n) (LocalPoly n))) :
    b ∈ Ideal.ofList l := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (originIdeal n).primeCompl] at h
  obtain ⟨s, hs, hsb⟩ := h
  have h1 := weightedHomogeneousComponent_mem_ofList l hl hsb c
  rw [weightedHomogeneousComponent_mul_of_right _ _ c c hb, if_pos le_rfl, Nat.sub_self,
    weightedHomogeneousComponent_zero _ (fun i => (hw i).ne')] at h1
  have hs0 : coeff 0 s ≠ 0 := by
    intro h0
    apply hs
    simp [originIdeal, ← constantCoeff_eq] at h0 ⊢
    exact h0
  have : b = C (coeff 0 s)⁻¹ * (C (coeff 0 s) * b) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hs0, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h1

/-- A homogeneous sequence regular in `ℂ[x]_𝔪` is regular in `ℂ[x]`. -/
lemma isWeaklyRegular_of_localization (hw : ∀ i, 0 < w i) (gs : List (Poly n))
    (hgs : ∀ g ∈ gs, ∃ e, g.IsWeightedHomogeneous w e)
    (h : IsWeaklyRegular (LocalPoly n) (gs.map (algebraMap (Poly n) (LocalPoly n)))) :
    IsWeaklyRegular (Poly n) gs := by
  rw [isWeaklyRegular_self_iff] at h ⊢
  intro i hi b hb
  have hl : ∀ r ∈ gs.take i, ∃ e, r.IsWeightedHomogeneous w e :=
    fun r hr => hgs r (List.mem_of_mem_take hr)
  obtain ⟨e, he⟩ := hgs gs[i] (List.getElem_mem _)
  refine mem_of_forall_weightedHomogeneousComponent_mem (w := w) _ b fun c => ?_
  have h1 : gs[i] * weightedHomogeneousComponent w c b ∈ Ideal.ofList (gs.take i) := by
    have := weightedHomogeneousComponent_mem_ofList _ hl (mul_comm gs[i] b ▸ hb) (c + e)
    rw [weightedHomogeneousComponent_mul_of_right _ _ e _ he, if_pos (Nat.le_add_left _ _),
      Nat.add_sub_cancel] at this
    rwa [mul_comm]
  have h2 := h i (by simpa using hi) (algebraMap (Poly n) (LocalPoly n)
    (weightedHomogeneousComponent w c b))
  rw [List.getElem_map, ← List.map_take, ofList_map, ← map_mul] at h2
  exact mem_of_algebraMap_mem hw _ hl (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (h2 (Ideal.mem_map_of_mem _ h1))

end Homogeneous

/-! ### Main conclusion -/

/-- A homogeneous system of parameters is a regular sequence: positive-degree weighted homogeneous polynomials with finite-dimensional quotient are regular in any order. -/
theorem isWeaklyRegular_of_finite_quotient {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    (gs : List (Poly n)) (hlen : gs.length ≤ n)
    (hgs : ∀ g ∈ gs, ∃ e, 0 < e ∧ g.IsWeightedHomogeneous w e)
    (hfin : Module.Finite ℂ (Poly n ⧸ Ideal.ofList gs)) :
    IsWeaklyRegular (Poly n) gs := by
  refine isWeaklyRegular_of_localization hw gs (fun g hg => ?_) ?_
  · obtain ⟨e, -, he⟩ := hgs g hg; exact ⟨e, he⟩
  have hmem : ∀ r ∈ gs.map (algebraMap (Poly n) (LocalPoly n)),
      r ∈ IsLocalRing.maximalIdeal (LocalPoly n) := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (LocalPoly n) (originIdeal n)]
    obtain ⟨e, he0, he⟩ := hgs g hg
    simp only [originIdeal, RingHom.mem_ker]
    have := eval_zero_of_isWH_pos he he0
    simpa [MvPolynomial.eval_zero] using this
  refine Depth.isWeaklyRegular_of_primes_isMaximal _ (LocalPoly n) ⊥ n bot_le ?_ ?_ hmem ?_
  · refine ⟨((List.finRange n).map X).map (algebraMap (Poly n) (LocalPoly n)), by simp, ?_,
      isWeaklyRegular_localization _ _ isWeaklyRegular_X⟩
    intro r hr
    simp only [List.map_map, List.mem_map, List.mem_finRange, true_and,
      Function.comp_apply] at hr
    obtain ⟨i, rfl⟩ := hr
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (LocalPoly n) (originIdeal n)]
    exact X_mem_originIdeal i
  · simpa using hlen
  · intro Q hQ _ hgQ
    refine isMaximal_of_finite_quotient _ hfin Q hQ ?_
    rw [← ofList_map, Ideal.ofList, Ideal.span_le]
    exact fun r hr => hgQ r hr

end Yau
