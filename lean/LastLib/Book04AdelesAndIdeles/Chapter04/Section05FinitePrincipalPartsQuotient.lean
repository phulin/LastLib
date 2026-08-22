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
  sorry

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
  sorry

theorem chapter04_global_principalParts_quotient_is_not_additively_free
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsAddTorsionFree (Chapter04GlobalPrincipalPartsQuotient K) := by
  sorry

theorem chapter04_finitePrincipalPartsQuotient_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Chapter04FinitePrincipalPartsQuotient K) := by
  sorry

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
