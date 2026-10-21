import RequestProject.Yau.Sec3_Radical.LemmaC1

/-!
# Hilbert functions and Milnor-algebra dimensions

For homogeneous regular sequences, the Hilbert function of the quotient depends
only on the generator degrees. In particular, isolated weighted homogeneous
polynomials of the same degree and weights have Milnor algebras of equal dimension.
The proof computes each homogeneous component by a regular-element exact sequence
and sums the finitely many nonzero quotient components.
-/

open MvPolynomial

noncomputable section

namespace Yau

variable {n : ℕ} {w : Fin n → ℕ}

/-- The vector space `S_v` of weighted homogeneous polynomials of degree `v`. -/
abbrev gradedS (w : Fin n → ℕ) (v : ℕ) : Submodule ℂ (Poly n) := weightedHomogeneousSubmodule ℂ w v

lemma finite_weight_eq (hw : ∀ i, 0 < w i) (v : ℕ) :
    {d : Fin n →₀ ℕ | Finsupp.weight w d = v}.Finite := by
  refine (Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => v))).finite_toSet.subset ?_
  intro d hd
  simp only [Set.mem_setOf_eq] at hd
  simp only [Finset.coe_Iic, Set.mem_Iic]
  intro i
  simpa [hd] using Finsupp.le_weight w (hw i).ne' d

lemma finite_gradedS (hw : ∀ i, 0 < w i) (v : ℕ) : Module.Finite ℂ (gradedS w v) := by
  rw [gradedS, weightedHomogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {d : Fin n →₀ ℕ | Finsupp.weight w d = v} := (finite_weight_eq hw v).to_subtype
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp _).symm

/-- The degree-`v` part `I_v = I ∩ S_v` of an ideal. -/
def homPart (w : Fin n → ℕ) (I : Ideal (Poly n)) (v : ℕ) : Submodule ℂ (Poly n) :=
  I.restrictScalars ℂ ⊓ gradedS w v

lemma homPart_le (I : Ideal (Poly n)) (v : ℕ) : homPart w I v ≤ gradedS w v := inf_le_right

lemma finite_homPart (hw : ∀ i, 0 < w i) (I : Ideal (Poly n)) (v : ℕ) :
    Module.Finite ℂ (homPart w I v) := by
  haveI := finite_gradedS hw v
  exact Submodule.finiteDimensional_inf_right _ _

lemma finrank_homPart_le (hw : ∀ i, 0 < w i) (I : Ideal (Poly n)) (v : ℕ) :
    Module.finrank ℂ (homPart w I v) ≤ Module.finrank ℂ (gradedS w v) := by
  haveI := finite_gradedS hw v
  exact Submodule.finrank_mono (homPart_le I v)

/-- An ideal closed under taking weighted homogeneous components. -/
def IsHomogIdeal (w : Fin n → ℕ) (I : Ideal (Poly n)) : Prop :=
  ∀ b ∈ I, ∀ c, weightedHomogeneousComponent w c b ∈ I

lemma isHomogIdeal_sup_span {I : Ideal (Poly n)} (hI : IsHomogIdeal w I) {p : Poly n} {a : ℕ}
    (hp : p.IsWeightedHomogeneous w a) : IsHomogIdeal w (I ⊔ Ideal.span {p}) := by
  intro b hb c
  obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.1 hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_add, weightedHomogeneousComponent_mul_of_right _ _ a c hp]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hI i hi c)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self p))
  · exact Ideal.zero_mem _

/-- The regular-element exact sequence gives `dim (I+(p))_v = dim I_v + dim S_{v-a} - dim I_{v-a}` for `v ≥ a`; for `v<a` the degree-`v` part is unchanged. -/
theorem finrank_homPart_sup (hw : ∀ i, 0 < w i) {I : Ideal (Poly n)} (hI : IsHomogIdeal w I)
    {p : Poly n} {a : ℕ} (hp : p.IsWeightedHomogeneous w a) (hreg : ∀ b, p * b ∈ I → b ∈ I)
    (v : ℕ) :
    Module.finrank ℂ (homPart w (I ⊔ Ideal.span {p}) v) = Module.finrank ℂ (homPart w I v) +
      (if a ≤ v then Module.finrank ℂ (gradedS w (v - a)) - Module.finrank ℂ (homPart w I (v - a))
        else 0) := by
  classical
  haveI := finite_gradedS hw v
  haveI := finite_gradedS hw (v - a)
  haveI := finite_homPart hw I v
  haveI := finite_homPart hw I (v - a)
  -- If `p=0`, regularity forces `I` to be the whole ring.
  by_cases hp0 : p = 0
  · have hItop : I = ⊤ := (Ideal.eq_top_iff_one I).2 (hreg 1 (by simp [hp0]))
    subst hItop
    have h1 : ∀ u, homPart w (⊤ : Ideal (Poly n)) u = gradedS w u := fun u => by
      simp [homPart]
    rw [top_sup_eq, h1, h1]
    split_ifs <;> simp
  -- Decompose an element of `(I+(p))_v`.
  have hdecomp : ∀ y ∈ homPart w (I ⊔ Ideal.span {p}) v, ∃ i ∈ homPart w I v, ∃ r : Poly n,
      (a ≤ v → r ∈ gradedS w (v - a)) ∧ (¬ a ≤ v → r = 0) ∧ y = i + p * r := by
    intro y hy
    obtain ⟨hyI, hyS⟩ := hy
    obtain ⟨i, hi, z, hz, rfl⟩ := Submodule.mem_sup.1 hyI
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    have hyv := (show (i + r * p).IsWeightedHomogeneous w v from hyS).weightedHomogeneousComponent_same
    refine ⟨weightedHomogeneousComponent w v i,
      ⟨hI i hi v, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩,
      if a ≤ v then weightedHomogeneousComponent w (v - a) r else 0, fun h => ?_, fun h => ?_, ?_⟩
    · rw [if_pos h]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    · rw [if_neg h]
    · conv_lhs => rw [← hyv]
      rw [map_add, weightedHomogeneousComponent_mul_of_right _ _ a v hp]
      split_ifs <;> ring
  by_cases hav : a ≤ v
  · rw [if_pos hav]
    set A := homPart w I v
    set B := (gradedS w (v - a)).map (LinearMap.mulLeft ℂ p)
    have hinj : Function.Injective (LinearMap.mulLeft ℂ p) := fun x y hxy =>
      mul_left_cancel₀ hp0 hxy
    have hsup : homPart w (I ⊔ Ideal.span {p}) v = A ⊔ B := by
      apply le_antisymm
      · intro y hy
        obtain ⟨i, hi, r, hr, -, rfl⟩ := hdecomp y hy
        exact Submodule.add_mem_sup hi ⟨r, hr hav, rfl⟩
      · refine sup_le ?_ ?_
        · exact inf_le_inf_right _ (Submodule.restrictScalars_mono ℂ le_sup_left)
        · rintro _ ⟨r, hr, rfl⟩
          refine ⟨Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)), ?_⟩
          have := hp.mul (show r.IsWeightedHomogeneous w (v - a) from hr)
          rwa [show a + (v - a) = v by omega] at this
    have hinf : (A ⊓ B : Submodule ℂ (Poly n)) = (homPart w I (v - a)).map (LinearMap.mulLeft ℂ p) := by
      apply le_antisymm
      · rintro y ⟨⟨hyI, -⟩, r, hr, rfl⟩
        exact ⟨r, ⟨hreg r hyI, hr⟩, rfl⟩
      · rintro _ ⟨r, ⟨hrI, hr⟩, rfl⟩
        refine ⟨⟨Ideal.mul_mem_left _ _ hrI, ?_⟩, r, hr, rfl⟩
        have := hp.mul (show r.IsWeightedHomogeneous w (v - a) from hr)
        rwa [show a + (v - a) = v by omega] at this
    have hB : Module.finrank ℂ B = Module.finrank ℂ (gradedS w (v - a)) :=
      (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have hAB : Module.finrank ℂ (A ⊓ B : Submodule ℂ (Poly n)) = Module.finrank ℂ (homPart w I (v - a)) := by
      rw [hinf]; exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    haveI : Module.Finite ℂ B := Module.Finite.map _ _
    have key := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hsup]
    have hle := finrank_homPart_le hw I (v - a)
    omega
  · rw [if_neg hav, add_zero]
    have heq : homPart w (I ⊔ Ideal.span {p}) v = homPart w I v := by
      apply le_antisymm
      · intro y hy
        obtain ⟨i, hi, r, -, hr, rfl⟩ := hdecomp y hy
        rw [hr hav, mul_zero, add_zero]; exact hi
      · exact inf_le_inf_right _ (Submodule.restrictScalars_mono ℂ le_sup_left)
    rw [heq]

/-! ## Ideals generated by prefixes of the gradient -/

lemma span_partialSeq_Iio_eq (g : Poly n) (k : ℕ) :
    Ideal.span (partialSeq g '' Set.Iio k) =
      Ideal.span (Set.range fun i : Fin k => partialSeq g i) := by
  congr 1
  ext y; constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

lemma partialSeq_isWH {d : ℕ} {g : Poly n} (hg : g.IsWeightedHomogeneous w d) (k : ℕ) :
    (partialSeq g k).IsWeightedHomogeneous w (if h : k < n then d - w ⟨k, h⟩ else 0) := by
  by_cases h : k < n
  · simp only [partialSeq, h, dif_pos]; exact pderiv_f_isWH hg _
  · simp only [partialSeq, h, dif_neg, not_false_eq_true]; exact isWeightedHomogeneous_zero _ _ _

lemma isHomogIdeal_span_partialSeq {d : ℕ} {g : Poly n} (hg : g.IsWeightedHomogeneous w d)
    (k : ℕ) : IsHomogIdeal w (Ideal.span (partialSeq g '' Set.Iio k)) := by
  intro b hb c
  rw [span_partialSeq_Iio_eq] at hb ⊢
  exact weightedHomogeneousComponent_mem_span (fun i : Fin k => partialSeq g i)
    (fun i : Fin k => if h : (i : ℕ) < n then d - w ⟨i, h⟩ else 0) (fun i => partialSeq_isWH hg i) hb c

lemma span_partialSeq_n (g : Poly n) :
    Ideal.span (partialSeq g '' Set.Iio n) = jacobianIdeal g := by
  rw [partialSeq_image_Iio g le_rfl, jacobianIdeal]
  congr 1
  ext y; simp

/-- The Jacobian ideals of two isolated homogeneous polynomials with the same weights and degree have equal-dimensional homogeneous parts. -/
theorem finrank_homPart_jacobian_eq (hw : ∀ i, 0 < w i) {d : ℕ} {f g : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hg : g.IsWeightedHomogeneous w d)
    (hisof : IsIsolatedSingularity f) (hisog : IsIsolatedSingularity g) (hwd : ∀ i, w i < d)
    (v : ℕ) : Module.finrank ℂ (homPart w (jacobianIdeal f) v) =
      Module.finrank ℂ (homPart w (jacobianIdeal g) v) := by
  have key : ∀ k ≤ n, ∀ v, Module.finrank ℂ (homPart w (Ideal.span (partialSeq f '' Set.Iio k)) v) =
      Module.finrank ℂ (homPart w (Ideal.span (partialSeq g '' Set.Iio k)) v) := by
    intro k
    induction k with
    | zero =>
      intro _ v
      have h0 : Set.Iio (0 : ℕ) = ∅ := Set.eq_empty_of_forall_notMem fun x hx => Nat.not_lt_zero x hx
      rw [h0, Set.image_empty, Set.image_empty]
    | succ k ih =>
      intro hk v
      have hins : ∀ h : Poly n, Ideal.span (partialSeq h '' Set.Iio (k + 1)) =
          Ideal.span (partialSeq h '' Set.Iio k) ⊔ Ideal.span {partialSeq h k} := by
        intro h
        rw [show Set.Iio (k + 1) = insert k (Set.Iio k) by
          ext x; simp only [Set.mem_Iio, Set.mem_insert_iff]; omega,
          Set.image_insert_eq, Ideal.span_insert, sup_comm]
      rw [hins f, hins g,
        finrank_homPart_sup hw (isHomogIdeal_span_partialSeq hf k) (partialSeq_isWH hf k)
          (partialSeq_reg hw hf hisof hwd k (by omega)) v,
        finrank_homPart_sup hw (isHomogIdeal_span_partialSeq hg k) (partialSeq_isWH hg k)
          (partialSeq_reg hw hg hisog hwd k (by omega)) v,
        ih (by omega) v, ih (by omega)]
  have := key n le_rfl v
  rwa [span_partialSeq_n, span_partialSeq_n] at this

/-! ## The quotient dimension is the sum of its homogeneous dimensions -/

/-- For a homogeneous ideal with finite-dimensional quotient, all sufficiently large `T` satisfy `dim ℂ[x]/I = ∑_{v<T}(dim S_v-dim I_v)`. -/
theorem finrank_quot_eq_sum (hw : ∀ i, 0 < w i) {I : Ideal (Poly n)} (hI : IsHomogIdeal w I)
    (hfin : Module.Finite ℂ (Poly n ⧸ I)) :
    ∃ T, ∀ T' ≥ T, Module.finrank ℂ (Poly n ⧸ I) = ∑ v ∈ Finset.range T',
      (Module.finrank ℂ (gradedS w v) - Module.finrank ℂ (homPart w I v)) := by
  classical
  obtain ⟨B, hB1, hB2⟩ := exists_monomial_complement I
  set V : Submodule ℂ (Poly n) := restrictSupport ℂ B with hVdef
  have e := quotEquivOfComplement I V hB1 hB2
  haveI : Module.Finite ℂ V := Module.Finite.equiv e
  have hBfin : B.Finite := by
    have hVfin : Module.Finite ℂ (Finsupp.supported ℂ ℂ B) := by
      rw [hVdef] at this; exact this
    have : Module.Finite ℂ (B →₀ ℂ) := Module.Finite.equiv (Finsupp.supportedEquivFinsupp B)
    rcases Module.finite_finsupp_iff.1 this with h | h | ⟨-, h⟩
    · haveI := h; exact Set.finite_coe_iff.1 inferInstance
    · exact absurd h (not_subsingleton ℂ)
    · exact Set.finite_coe_iff.1 h
  set Bf := hBfin.toFinset with hBf
  have hBcoe : (Bf : Set (Fin n →₀ ℕ)) = B := hBfin.coe_toFinset
  -- The intersection `V ∩ S_v` is spanned by the degree-`v` monomials in `B`.
  have hVv : ∀ v, V ⊓ gradedS w v =
      restrictSupport ℂ ((Bf.filter fun m => Finsupp.weight w m = v : Finset _) : Set _) := by
    intro v
    rw [gradedS, weightedHomogeneousSubmodule_eq_finsupp_supported, hVdef, restrictSupport,
      ← Finsupp.supported_inter, Finset.coe_filter, ← hBcoe]
    rfl
  have hcard : ∀ s : Finset (Fin n →₀ ℕ),
      Module.finrank ℂ (restrictSupport ℂ (s : Set (Fin n →₀ ℕ))) = s.card := by
    intro s
    have := (Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) (s : Set (Fin n →₀ ℕ))).finrank_eq
    rw [Module.finrank_finsupp_self] at this
    simpa using this
  -- Complementary subspaces in each degree.
  have hpiece : ∀ v, (Bf.filter fun m => Finsupp.weight w m = v).card +
      Module.finrank ℂ (homPart w I v) = Module.finrank ℂ (gradedS w v) := by
    intro v
    haveI := finite_gradedS hw v
    haveI := finite_homPart hw I v
    haveI : Module.Finite ℂ (V ⊓ gradedS w v : Submodule ℂ (Poly n)) :=
      Submodule.finiteDimensional_inf_right _ _
    have key := Submodule.finrank_sup_add_finrank_inf_eq (V ⊓ gradedS w v) (homPart w I v)
    have hsup : V ⊓ gradedS w v ⊔ homPart w I v = gradedS w v := by
      apply le_antisymm (sup_le inf_le_right (homPart_le I v))
      intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hB2 y)
      have hyv := (show y.IsWeightedHomogeneous w v from hy).weightedHomogeneousComponent_same
      rw [← hyv, ← hab, map_add]
      exact Submodule.add_mem_sup
        ⟨restrictSupport_component_mem ha v, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
        ⟨hI b hb v, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
    have hinf : V ⊓ gradedS w v ⊓ homPart w I v = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨⟨hyV, -⟩, hyI, -⟩
      exact (Submodule.mem_bot ℂ).2 (hB1 y hyV hyI)
    rw [hsup, hinf, finrank_bot, add_zero, hVv, hcard] at key
    exact key.symm
  -- Choose `T` larger than every monomial weight in `B`.
  refine ⟨Bf.sup (fun m => Finsupp.weight w m) + 1, fun T' hT' => ?_⟩
  rw [e.finrank_eq, show V = restrictSupport ℂ (Bf : Set (Fin n →₀ ℕ)) by
    rw [hBcoe], hcard]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun m => Finsupp.weight w m) (t := Finset.range T')
    (fun m hm => by
      have h1 : Finsupp.weight w m ≤ Bf.sup (fun m => Finsupp.weight w m) :=
        Finset.le_sup (f := fun m => Finsupp.weight w m) hm
      simp only [Finset.coe_range, Set.mem_Iio]; omega)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have := hpiece v
  omega

/-- Isolated weighted homogeneous polynomials with the same weights and degree have Milnor algebras of equal dimension. -/
theorem finrank_milnorAlgebra_eq_of_isWH (hw : ∀ i, 0 < w i) {d : ℕ} {f g : Poly n}
    (hf : f.IsWeightedHomogeneous w d) (hg : g.IsWeightedHomogeneous w d)
    (hisof : IsIsolatedSingularity f) (hisog : IsIsolatedSingularity g) (hwd : ∀ i, w i < d) :
    Module.finrank ℂ (MilnorAlgebra g) = Module.finrank ℂ (MilnorAlgebra f) := by
  obtain ⟨Tf, hTf⟩ := finrank_quot_eq_sum hw
    (fun b hb c => weightedHomogeneousComponent_mem_jacobianIdeal hf hb c) hisof
  obtain ⟨Tg, hTg⟩ := finrank_quot_eq_sum hw
    (fun b hb c => weightedHomogeneousComponent_mem_jacobianIdeal hg hb c) hisog
  rw [hTf (max Tf Tg) (le_max_left _ _), hTg (max Tf Tg) (le_max_right _ _)]
  exact Finset.sum_congr rfl fun v _ => by
    rw [finrank_homPart_jacobian_eq hw hf hg hisof hisog hwd v]

end Yau
