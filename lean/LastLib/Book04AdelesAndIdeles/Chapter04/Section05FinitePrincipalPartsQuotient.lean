import LastLib.Book04AdelesAndIdeles.Chapter04.Section01TheFiniteAdeleRing

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators Topology RestrictedProduct

/-! ### 4.5 The finite principal-parts quotient -/

def chapter04RingOfIntegersEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Chapter04RingOfIntegers K →+* K :=
  algebraMap (Chapter04RingOfIntegers K) K

abbrev Chapter04RingOfIntegersAddSubgroup
    (K : Type*) [Field K] [NumberField K] : AddSubgroup K :=
  (chapter04RingOfIntegersEmbedding K).range.toAddSubgroup

abbrev Chapter04GlobalPrincipalPartsQuotient
    (K : Type*) [Field K] [NumberField K] :=
  K ⧸ Chapter04RingOfIntegersAddSubgroup K

abbrev Chapter04FinitePrincipalPartsQuotient
    (K : Type*) [Field K] [NumberField K] :=
  Chapter04FiniteAdeleRing K ⧸ Chapter04FiniteIntegralAdeleAddSubgroup K

def chapter04FinitePrincipalPartsQuotientMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter04FiniteAdeleRing K →+
      Chapter04FinitePrincipalPartsQuotient K :=
  QuotientAddGroup.mk' (Chapter04FiniteIntegralAdeleAddSubgroup K)

def chapter04GlobalToFiniteAdeleAdditiveMap
    (K : Type*) [Field K] [NumberField K] :
    K →+ Chapter04FiniteAdeleRing K :=
  (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K).toAddMonoidHom

def chapter04PrincipalPartsMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter04GlobalPrincipalPartsQuotient K →+
      Chapter04FinitePrincipalPartsQuotient K :=
  QuotientAddGroup.lift (Chapter04RingOfIntegersAddSubgroup K)
    ((chapter04FinitePrincipalPartsQuotientMap K).comp
      (chapter04GlobalToFiniteAdeleAdditiveMap K)) (by
        intro x hx
        rcases hx with ⟨a, rfl⟩
        change QuotientAddGroup.mk' (Chapter04FiniteIntegralAdeleAddSubgroup K)
          (chapter04GlobalToFiniteAdeleAdditiveMap K
            (algebraMap (𝓞 K) K a)) = 0
        change (↑(chapter04GlobalToFiniteAdeleAdditiveMap K
            (algebraMap (𝓞 K) K a)) : Chapter04FinitePrincipalPartsQuotient K) =
          ↑(0 : Chapter04FiniteAdeleRing K)
        rw [QuotientAddGroup.eq_iff_sub_mem]
        apply (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).2
        intro v
        simp only [sub_zero]
        change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) ∈
          v.adicCompletionIntegers K
        rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) a]
        exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers
          (R := 𝓞 K) (K := K) v a)

@[simp]
theorem chapter04PrincipalPartsMap_apply
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter04PrincipalPartsMap K (QuotientAddGroup.mk' _ a) =
      chapter04FinitePrincipalPartsQuotientMap K
        (chapter04GlobalToFiniteAdeleAdditiveMap K a) := by
  rfl

theorem chapter04_principalParts_map_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter04PrincipalPartsMap K) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) y
  rw [chapter04PrincipalPartsMap_apply, chapter04PrincipalPartsMap_apply] at h
  have hzero :
      chapter04FinitePrincipalPartsQuotientMap K
          (chapter04GlobalToFiniteAdeleAdditiveMap K (a - b)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have hmem :
      chapter04GlobalToFiniteAdeleAdditiveMap K (a - b) ∈
        Chapter04FiniteIntegralAdeleAddSubgroup K := by
    change (↑(chapter04GlobalToFiniteAdeleAdditiveMap K (a - b)) :
      Chapter04FinitePrincipalPartsQuotient K) = ↑(0 : Chapter04FiniteAdeleRing K) at hzero
    simpa only [sub_zero] using (QuotientAddGroup.eq_iff_sub_mem).mp hzero
  have hlocal : ∀ v : Chapter04FinitePlace K,
      ((a - b : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    exact (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).1 hmem v
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  change a - b ∈ (chapter04RingOfIntegersEmbedding K).range
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := 𝓞 K) (K := K) (a - b)
  intro v
  rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
    (𝓞 K) K v).1 (hlocal v)

theorem chapter04_principalParts_map_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter04PrincipalPartsMap K) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04FiniteIntegralAdeleAddSubgroup K) y
  obtain ⟨a, ha⟩ :=
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01_principal_parts_approximation K x
  refine ⟨QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a, ?_⟩
  rw [chapter04PrincipalPartsMap_apply]
  change (↑(chapter04GlobalToFiniteAdeleAdditiveMap K a) :
      Chapter04FinitePrincipalPartsQuotient K) =
    QuotientAddGroup.mk' (Chapter04FiniteIntegralAdeleAddSubgroup K) x
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  apply (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K _).2
  intro v
  change algebraMap K (v.adicCompletion K) a - x v ∈
    v.adicCompletionIntegers K
  have hneg := (v.adicCompletionIntegers K).neg_mem
    (x v - (a : v.adicCompletion K)) (ha v)
  have hcoe : (a : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a := by
    simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rw [hcoe] at hneg
  simpa [sub_eq_add_neg, add_comm] using hneg

noncomputable def chapter04PrincipalPartsEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter04GlobalPrincipalPartsQuotient K ≃+
      Chapter04FinitePrincipalPartsQuotient K :=
  AddEquiv.ofBijective (chapter04PrincipalPartsMap K)
    ⟨chapter04_principalParts_map_injective K,
      chapter04_principalParts_map_surjective K⟩

noncomputable def chapter04_principalParts_quotient_is_an_abstract_additive_group_isomorphism
    (K : Type*) [Field K] [NumberField K] :
    Chapter04GlobalPrincipalPartsQuotient K ≃+
      Chapter04FinitePrincipalPartsQuotient K :=
  chapter04PrincipalPartsEquiv K

def chapter04GlobalPrincipalPartsQuotientIsTorsion
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ x : Chapter04GlobalPrincipalPartsQuotient K,
    ∃ n : ℕ, n ≠ 0 ∧ n • x = 0

theorem chapter04_global_principalParts_quotient_is_torsion
    (K : Type*) [Field K] [NumberField K] :
    chapter04GlobalPrincipalPartsQuotientIsTorsion K := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Chapter04RingOfIntegersAddSubgroup K) x
  obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
  rcases hb with ⟨d, hd⟩
  let I : Ideal (𝓞 K) := Ideal.span ({(b : 𝓞 K)} : Set (𝓞 K))
  have hI : I ≠ ⊥ := by
    intro h
    have hmem : (b : 𝓞 K) ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← h]
      exact Ideal.subset_span (by simp)
    simpa [mem_nonZeroDivisors_iff_ne_zero.mp b.property] using hmem
  let n : ℕ := Ideal.absNorm (Ideal.under ℤ I)
  have hn : n ≠ 0 := by
    have hdiv : n ∣ Ideal.absNorm I := by
      exact Int.absNorm_under_dvd_absNorm I
    have hnorm : Ideal.absNorm I ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr hI
    intro hn
    have hzero : (0 : ℕ) ∣ Ideal.absNorm I := by
      simpa [n, hn] using hdiv
    exact hnorm (by simpa using hzero)
  have hnmem : (n : 𝓞 K) ∈ I := by
    exact Int.absNorm_under_mem I
  change (n : 𝓞 K) ∈ Ideal.span ({(b : 𝓞 K)} : Set (𝓞 K)) at hnmem
  rcases Ideal.mem_span_singleton.mp hnmem with ⟨c, hc⟩
  refine ⟨n, hn, ?_⟩
  change QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) (n • a) = 0
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  simp only [sub_zero]
  change n • a ∈ (chapter04RingOfIntegersEmbedding K).range
  rw [nsmul_eq_mul]
  refine ⟨c * d, ?_⟩
  change algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K d = (n : K) * a
  have hcn : (n : K) = ((b : 𝓞 K) : K) * (c : K) := by
    simpa using congrArg (algebraMap (𝓞 K) K) hc
  rw [hd, hcn]
  simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

theorem chapter04_global_principalParts_quotient_is_not_additively_free
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsAddTorsionFree (Chapter04GlobalPrincipalPartsQuotient K) := by
  have hH : Chapter04RingOfIntegersAddSubgroup K ≠ ⊤ := by
    intro h
    have hsurj : Function.Surjective (algebraMap (𝓞 K) K) := by
      intro x
      have hx : x ∈ Chapter04RingOfIntegersAddSubgroup K := by
        rw [h]
        trivial
      change x ∈ (chapter04RingOfIntegersEmbedding K).range at hx
      exact hx
    exact RingOfIntegers.not_isField K
      ((IsFractionRing.surjective_iff_isField (R := 𝓞 K) (K := K)).mp hsurj)
  have hnot : ¬ ∀ x : K, x ∈ Chapter04RingOfIntegersAddSubgroup K := by
    intro hall
    apply hH
    exact top_unique (fun x _ => hall x)
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  have hmk : QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a ≠ 0 := by
    intro hzero
    have hmem : a - 0 ∈ Chapter04RingOfIntegersAddSubgroup K :=
      (QuotientAddGroup.eq_iff_sub_mem).mp hzero
    exact ha (by simpa using hmem)
  have hnontriv : Nontrivial (Chapter04GlobalPrincipalPartsQuotient K) :=
    ⟨⟨QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K) a, 0, hmk⟩⟩
  apply @not_isAddTorsionFree_of_isAddTorsion _ inferInstance hnontriv
  intro x
  obtain ⟨n, hn, hnx⟩ := chapter04_global_principalParts_quotient_is_torsion K x
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, Nat.pos_of_ne_zero hn, hnx⟩

theorem chapter04_finitePrincipalPartsQuotient_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Chapter04FinitePrincipalPartsQuotient K) := by
  exact QuotientAddGroup.discreteTopology
    (chapter04_finiteIntegralAdele_is_compact_open K).2

abbrev chapter04PrincipalPartsTransportedDiscreteTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
  TopologicalSpace.induced (chapter04PrincipalPartsEquiv K) ⊤

theorem chapter04_principalParts_transport_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter04GlobalPrincipalPartsQuotient K)
      (chapter04PrincipalPartsTransportedDiscreteTopology K) := by
  sorry

abbrev chapter04GlobalDiagonalSubspaceTopology
    (K : Type*) [Field K] [NumberField K] : TopologicalSpace K :=
  TopologicalSpace.induced
    (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K)
    inferInstance

theorem chapter04_global_diagonal_is_dense
    (K : Type*) [Field K] [NumberField K] :
    DenseRange (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K) := by
  sorry

abbrev chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter04GlobalPrincipalPartsQuotient K) :=
  TopologicalSpace.coinduced
    (QuotientAddGroup.mk' (Chapter04RingOfIntegersAddSubgroup K))
    (chapter04GlobalDiagonalSubspaceTopology K)

theorem chapter04_global_diagonal_subspace_is_not_discrete
    (K : Type*) [Field K] [NumberField K] :
    ¬ @DiscreteTopology K (chapter04GlobalDiagonalSubspaceTopology K) := by
  sorry

theorem chapter04_global_dense_subspace_quotient_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    @DiscreteTopology (Chapter04GlobalPrincipalPartsQuotient K)
      (chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K) := by
  sorry

theorem chapter04_principalParts_transport_is_the_dense_subspace_quotient_topology
    (K : Type*) [Field K] [NumberField K] :
    chapter04PrincipalPartsTransportedDiscreteTopology K =
      chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K := by
  /- PRIOR ATTEMPT: the preceding proof asserted that the dense-subspace
     quotient was non-discrete.  Since the integral subgroup is open in the
     induced finite-adele topology, that assertion was mathematically false. -/
  sorry

theorem chapter04_principalParts_quotient_is_a_topological_additive_group_isomorphism
    (K : Type*) [Field K] [NumberField K] :
    @Continuous (Chapter04GlobalPrincipalPartsQuotient K)
        (Chapter04FinitePrincipalPartsQuotient K)
        (chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K) inferInstance
        (chapter04PrincipalPartsEquiv K) ∧
      @Continuous (Chapter04FinitePrincipalPartsQuotient K)
        (Chapter04GlobalPrincipalPartsQuotient K)
        inferInstance (chapter04GlobalPrincipalPartsDenseSubspaceQuotientTopology K)
        (chapter04PrincipalPartsEquiv K).symm := by
  sorry

def chapter04FiniteAdeleSingleCoordinate
    (K : Type*) [Field K] [NumberField K]
    (v₀ : Chapter04FinitePlace K) (z : Chapter04FiniteLocalField K v₀) :
    Chapter04FiniteAdeleRing K := by
  classical
  exact ⟨fun v => if h : v = v₀ then h ▸ z else 0, by
    sorry⟩

@[simp]
theorem chapter04FiniteAdeleSingleCoordinate_apply_same
    (K : Type*) [Field K] [NumberField K]
    (v₀ : Chapter04FinitePlace K) (z : Chapter04FiniteLocalField K v₀) :
    chapter04FiniteAdeleSingleCoordinate K v₀ z v₀ = z := by
  sorry

theorem chapter04FiniteAdeleSingleCoordinate_apply_ne
    (K : Type*) [Field K] [NumberField K]
    (v₀ : Chapter04FinitePlace K) (z : Chapter04FiniteLocalField K v₀)
    {v : Chapter04FinitePlace K} (hv : v ≠ v₀) :
    chapter04FiniteAdeleSingleCoordinate K v₀ z v = 0 := by
  sorry

theorem chapter04_finite_principal_parts_are_represented_by_one_global_element
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    ∃ a : K, ∀ v : Chapter04FinitePlace K,
      x v - (a : Chapter04FiniteLocalField K v) ∈
        chapter04FiniteLocalIntegerSet K v := by
  sorry

def chapter04RationalPrincipalPartsCorrectionExample
    (p q : Chapter04FinitePlace ℚ) (_hpq : p ≠ q)
    (r s : ℚ) (_hr : r ≠ 0) (_hs : s ≠ 0) :
    Chapter04FiniteAdeleRing ℚ :=
  chapter04FiniteAdeleSingleCoordinate ℚ p
      (((r : Chapter04FiniteLocalField ℚ p)⁻¹) ^ 2 +
        (r : Chapter04FiniteLocalField ℚ p)⁻¹) +
    chapter04FiniteAdeleSingleCoordinate ℚ q
      (s : Chapter04FiniteLocalField ℚ q)⁻¹

theorem chapter04_rational_principal_parts_correction_example
    (p q : Chapter04FinitePlace ℚ) (hpq : p ≠ q)
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) :
    ∃ a : ℚ, ∀ v : Chapter04FinitePlace ℚ,
      chapter04RationalPrincipalPartsCorrectionExample p q hpq r s hr hs v -
          (a : Chapter04FiniteLocalField ℚ v) ∈
      chapter04FiniteLocalIntegerSet ℚ v := by
  sorry

def chapter04RationalDisplayedPrincipalPartsFamily
    (p q : Chapter04RationalPrime) (hpq : p ≠ q) :
    Chapter04RationalFiniteRestrictedProduct := by
  classical
  exact RestrictedProduct.mk (fun r =>
    if h : r = p then
      h ▸ (((p.1 : Chapter04RationalPadic p)⁻¹) ^ 2 +
        (p.1 : Chapter04RationalPadic p)⁻¹)
    else if h : r = q then
      h ▸ (q.1 : Chapter04RationalPadic q)⁻¹
    else 0) (by
      sorry)

def chapter04RationalDisplayedPrincipalPartsRepresentative
    (p q : Chapter04RationalPrime) : ℚ :=
  (p.1 : ℚ)⁻¹ ^ 2 + (p.1 : ℚ)⁻¹ + (q.1 : ℚ)⁻¹

theorem chapter04_rational_displayed_principal_parts_are_represented
    (p q : Chapter04RationalPrime) (hpq : p ≠ q) :
    ∀ r : Chapter04RationalPrime,
      chapter04RationalDisplayedPrincipalPartsFamily p q hpq r -
          (chapter04RationalDisplayedPrincipalPartsRepresentative p q :
            Chapter04RationalPadic r) ∈ Chapter04RationalPadicIntegerSubring r := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
