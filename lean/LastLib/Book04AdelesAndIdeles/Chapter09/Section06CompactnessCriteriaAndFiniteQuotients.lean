import LastLib.Book04AdelesAndIdeles.Chapter09.Section04StructureOfIdeleClassGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain
open scoped RestrictedProduct

/-!
## 9.6. Compactness criteria and finite quotients
-/

theorem chapter09_finite_range_of_continuous_map_from_compact_to_discrete
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [CompactSpace G]
    [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hf : Continuous f) :
    (Set.range f).Finite := by
  have hcompact : IsCompact (Set.range f) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hf
  exact hcompact.finite_of_discrete

structure Chapter09DiscreteArithmeticQuotient
    (G : Type*) [Group G] [TopologicalSpace G]
    (H : Type*) [Group H] [TopologicalSpace H] [DiscreteTopology H] where
  map : G →* H
  continuous_map : Continuous map

private theorem chapter09_finite_unit_ideles_isOpen
    (K : Type*) [Field K] [NumberField K] :
    IsOpen (chapter09FiniteUnitIdeles K : Set (Chapter09FiniteAdele K)ˣ) := by
  let U : Set (Chapter09FiniteAdele K) :=
    {z | ∀ v : HeightOneSpectrum (𝓞 K),
      z v ∈ v.adicCompletionIntegers K}
  have hU : IsOpen U := by
    change IsOpen {z : Chapter09FiniteAdele K |
      ∀ v : HeightOneSpectrum (𝓞 K),
        z v ∈ v.adicCompletionIntegers K}
    exact RestrictedProduct.isOpen_forall_mem (fun v =>
      Valued.isOpen_valuationSubring (v.adicCompletion K))
  have heq : (chapter09FiniteUnitIdeles K : Set (Chapter09FiniteAdele K)ˣ) =
      (fun x : (Chapter09FiniteAdele K)ˣ => (x : Chapter09FiniteAdele K)) ⁻¹' U ∩
        (fun x : (Chapter09FiniteAdele K)ˣ =>
          (↑(x⁻¹) : Chapter09FiniteAdele K)) ⁻¹' U := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro v
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
        have hv :=
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one x).1 hx v
        change Valued.v ((x : Chapter09FiniteAdele K) v) = 1 at hv
        exact hv.le
      · intro v
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
        have hv :=
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one x⁻¹).1
            ((chapter09FiniteUnitIdeles K).inv_mem hx) v
        change Valued.v ((↑(x⁻¹) : Chapter09FiniteAdele K) v) = 1 at hv
        exact hv.le
    · rintro ⟨hx, hxi⟩
      apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one x).2
      intro v
      have hxv := hx v
      have hixv := hxi v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hxv hixv
      change Valued.v ((x : Chapter09FiniteAdele K) v) ≤ 1 at hxv
      change Valued.v ((↑(x⁻¹) : Chapter09FiniteAdele K) v) ≤ 1 at hixv
      have hne : (x : Chapter09FiniteAdele K) v ≠ 0 := by
        exact LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_component_ne_zero x v
      have hge : 1 ≤ Valued.v ((x : Chapter09FiniteAdele K) v) := by
        let u :=
          (RestrictedProduct.unitsEquiv
            (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) x) v
        have huval : (u : v.adicCompletion K) =
            ((x : Chapter09FiniteAdele K) v) :=
          RestrictedProduct.unitsEquiv_apply v x
        have huinv :
            (RestrictedProduct.unitsEquiv
              (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) (x⁻¹)) v =
              u⁻¹ := by
          exact congrArg (fun z => z v)
            ((RestrictedProduct.unitsEquiv
              (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)).map_inv x)
        have huinvval :
            (↑((RestrictedProduct.unitsEquiv
              (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
                (x⁻¹)) v) : v.adicCompletion K) =
              (↑(u⁻¹) : v.adicCompletion K) :=
          congrArg Units.val huinv
        have hixv' : Valued.v (↑(u⁻¹) : v.adicCompletion K) ≤ 1 := by
          calc
            Valued.v (↑(u⁻¹) : v.adicCompletion K) =
                Valued.v (↑((RestrictedProduct.unitsEquiv
                  (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
                    (x⁻¹)) v) : v.adicCompletion K) :=
              congrArg Valued.v huinvval.symm
            _ = Valued.v ((↑(x⁻¹) : Chapter09FiniteAdele K) v) := by
              rw [RestrictedProduct.unitsEquiv_apply]
              rfl
            _ ≤ 1 := hixv
        have hge' : 1 ≤ Valued.v (u : v.adicCompletion K) :=
          (Valuation.one_le_val_iff Valued.v (Units.ne_zero u)).2 (by
            rw [← Units.val_inv_eq_inv_val u]
            exact hixv')
        rw [← huval]
        exact hge'
      exact le_antisymm hxv hge
  rw [heq]
  exact (hU.preimage Units.continuous_val).inter
    (hU.preimage Units.continuous_coe_inv)

private theorem chapter09_finite_idele_ideal_continuous_standard
    (K : Type*) [Field K] [NumberField K] :
    @Continuous (Chapter09FiniteAdele K)ˣ
      (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K)
      inferInstance ⊥
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K) := by
  let : TopologicalSpace
      (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K) := ⊥
  have hkernel : IsOpen (chapter09FiniteUnitIdeles K : Set (Chapter09FiniteAdele K)ˣ) :=
    chapter09_finite_unit_ideles_isOpen K
  have hdisc : @DiscreteTopology
      (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K) ⊥ :=
    discreteTopology_bot _
  apply (@continuous_discrete_rng
    (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K)
    (Chapter09FiniteAdele K)ˣ inferInstance ⊥ hdisc
    (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K)).2
  intro I
  obtain ⟨x, hx⟩ :=
    LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_surjective K I
  have hpre :
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K) ⁻¹'
          ({I} : Set (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K)) =
        (fun z : (Chapter09FiniteAdele K)ˣ => x * z) ''
          (MonoidHom.ker
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K) :
              Set (Chapter09FiniteAdele K)ˣ) := by
    ext y
    constructor
    · intro hy
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K y = I at hy
      have hmem : x⁻¹ * y ∈ MonoidHom.ker
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K) := by
        rw [MonoidHom.mem_ker]
        simp [map_mul, hx, hy]
      exact ⟨x⁻¹ * y, hmem, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (x * z) = I
      rw [map_mul, hx, MonoidHom.mem_ker.mp hz, mul_one]
  rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel] at hpre
  rw [hpre]
  exact @isOpenMap_mul_left (Chapter09FiniteAdele K)ˣ inferInstance Units.instGroup
    inferInstance x _ hkernel

theorem chapter09_discrete_arithmetic_quotient_has_finite_image
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [CompactSpace G]
    [TopologicalSpace H] [DiscreteTopology H]
    (Q : Chapter09DiscreteArithmeticQuotient G H) :
    (Set.range Q.map).Finite := by
  exact chapter09_finite_range_of_continuous_map_from_compact_to_discrete
    Q.map Q.continuous_map

theorem chapter09NormOneClassIdealClassMap_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09NormOneClassIdealClassMap K) := by
  change Continuous (fun x : chapter09ClassNormOne K =>
    chapter09IdeleClassIdealClassMap K x.1)
  apply Continuous.comp
  · apply (QuotientGroup.isQuotientMap_mk
      (chapter09PrincipalIdeleSubgroup K)).continuous_iff.mpr
    change Continuous (fun x : Chapter09Idele K =>
      (chapter09CanonicalIdeleIdealData K).idealClassMap
        (chapter09FiniteIdelePartHom K x))
    change Continuous (fun x : Chapter09Idele K =>
      ClassGroup.mk K
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
          (chapter09FiniteIdelePartHom K x)))
    let : TopologicalSpace
        (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K) := ⊥
    let : DiscreteTopology
        (LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K) :=
      discreteTopology_bot _
    exact continuous_of_discreteTopology.comp
      ((chapter09_finite_idele_ideal_continuous_standard K).comp
        (continuous_snd.comp (chapter09IdeleProductContinuousEquiv K).continuous))
  · exact continuous_subtype_val

theorem chapter09_ideal_class_group_is_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) := by
  infer_instance

theorem chapter09_ideal_class_group_is_finite_as_set
    (K : Type*) [Field K] [NumberField K] :
    (Set.univ : Set (ClassGroup (𝓞 K))).Finite := by
  exact Set.toFinite _

theorem chapter09_normOne_class_maps_to_finite_ideal_class_group
    (K : Type*) [Field K] [NumberField K] :
    (Set.range (chapter09NormOneClassIdealClassMap K)).Finite := by
  exact chapter09_finite_range_of_continuous_map_from_compact_to_discrete
    (chapter09NormOneClassIdealClassMap K)
    (chapter09NormOneClassIdealClassMap_continuous K)

abbrev Chapter09ArchMagnitudeQuotient
    (K : Type*) [Field K] [NumberField K] :=
  Chapter09Idele K ⧸ chapter09PrincipalTimesFiniteUnits K

def chapter09ArchMagnitudeModule
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchMagnitudeQuotient K →* Chapter09PositiveReal :=
  QuotientGroup.lift (chapter09PrincipalTimesFiniteUnits K)
    (chapter09IdeleModuleHom K) (by
      intro x hx
      apply (MonoidHom.mem_ker).2
      rcases Subgroup.mem_sup.mp hx with ⟨p, hp, q, hq, rfl⟩
      rcases hp with ⟨a, rfl⟩
      rcases hq with ⟨u, hu, rfl⟩
      rw [(chapter09IdeleModuleHom K).map_mul]
      change chapter09IdeleModule (chapter09PrincipalIdele K a) *
        chapter09IdeleModule (chapter09FiniteUnitIdeleEmbedding K u) = 1
      rw [chapter09PrincipalIdele_module_eq_one,
        chapter09FiniteUnitIdele_module_eq_one ⟨u, hu⟩]
      simp)

theorem chapter09ArchMagnitudeModule_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09ArchMagnitudeModule K (QuotientGroup.mk x) =
      chapter09IdeleModuleHom K x := by
  rfl

theorem chapter09ArchMagnitudeModule_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09ArchMagnitudeModule K) := by
  intro t
  rcases chapter09IdeleModule_surjective K t with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [chapter09ArchMagnitudeModule_apply]
  exact hx

private theorem chapter09ArchMagnitudeModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09ArchMagnitudeModule K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (chapter09PrincipalTimesFiniteUnits K)).continuous_iff.mpr
  change Continuous (fun x : Chapter09Idele K =>
    chapter09ArchMagnitudeModule K (QuotientGroup.mk x))
  have hcomp : (fun x : Chapter09Idele K =>
      chapter09ArchMagnitudeModule K (QuotientGroup.mk x)) =
      chapter09IdeleModuleHom K := by
    funext x
    exact chapter09ArchMagnitudeModule_apply x
  rw [hcomp]
  exact chapter09IdeleModule_continuous K

private theorem chapter09_positive_real_not_compact :
    ¬ IsCompact (Set.univ : Set Chapter09PositiveReal) := by
  intro hcompact
  have hcompact' : IsCompact
      ((fun x : Chapter09PositiveReal => Units.val x) ''
        (Set.univ : Set Chapter09PositiveReal)) :=
    hcompact.image Units.continuous_val
  rcases hcompact'.bddAbove with ⟨B, hB⟩
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  let t : Chapter09PositiveReal := Units.mk0 (2 : NNReal) htwo
  rcases pow_unbounded_of_one_lt B (show 1 < Units.val t by
    norm_num [t]) with ⟨n, hn⟩
  have hbound : Units.val (t ^ n) ≤ B :=
    hB ⟨t ^ n, Set.mem_univ _, rfl⟩
  exact (not_lt_of_ge hbound) (by simpa using hn)

theorem chapter09ArchMagnitudeQuotient_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter09ArchMagnitudeQuotient K)) := by
  intro hcompact
  have himage : IsCompact (Set.range (chapter09ArchMagnitudeModule K)) := by
    rw [← Set.image_univ]
    exact hcompact.image (chapter09ArchMagnitudeModule_continuous K)
  have huniv : Set.range (chapter09ArchMagnitudeModule K) =
      (Set.univ : Set Chapter09PositiveReal) :=
    Set.range_eq_univ.mpr (chapter09ArchMagnitudeModule_surjective K)
  apply chapter09_positive_real_not_compact
  rw [← huniv]
  exact himage

/- The full idele class group has the same obstruction: its positive real
module quotient cannot be made finite by a discrete quotient argument. -/
theorem chapter09_full_idele_class_group_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter09IdeleClassGroup K)) :=
  chapter09_idele_class_group_is_not_compact K

theorem chapter09_compactness_requires_norm_one_or_archimedean_quotient
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09ClassNormOne K)) ∧
      ¬ IsCompact (Set.univ : Set (Chapter09ArchMagnitudeQuotient K)) := by
  exact ⟨chapter09_normOne_class_compact K,
    chapter09ArchMagnitudeQuotient_is_not_compact K⟩

end

end LastLib.Book04AdelesAndIdeles.Chapter09
