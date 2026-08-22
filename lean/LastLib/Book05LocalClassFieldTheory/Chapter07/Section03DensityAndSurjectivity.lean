import LastLib.Book05LocalClassFieldTheory.Chapter07.Section02Continuity
import Mathlib.Topology.Baire.LocallyCompactRegular

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory Opposite

/-- Every finite quotient of local reciprocity is onto. -/
theorem chapter07_local_reciprocity_surjective_on_finite_level
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Function.Surjective
      (fun x : Kˣ =>
        InfiniteGalois.proj L
          ((chapter07AbelianGaloisLimitEquiv K KAb)
            (chapter07LocalReciprocity S x))) := by
  exact fun y => Exists.elim (S.surjective L y)
    (fun x hx => ⟨x, (chapter07_finite_artin_is_the_reciprocity_projection S L x).trans hx⟩)

/-- For the canonical finite-level Galois system, surjectivity on every finite
projection is equivalent to density in the inverse limit. -/
theorem chapter07_local_reciprocity_dense_iff_finite_projections_surjective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    DenseRange (chapter07LocalReciprocity S) ↔
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Function.Surjective
          (fun x : Kˣ =>
            InfiniteGalois.proj L
              ((chapter07AbelianGaloisLimitEquiv K KAb)
                (chapter07LocalReciprocity S x))) := by
  constructor
  · intro _ L
    exact chapter07_local_reciprocity_surjective_on_finite_level S L
  · intro h
    refine dense_iff_inter_open.mpr ?_
    intro U hU hUne
    obtain ⟨σ, hσ⟩ := hUne
    let V : Set Gal(KAb / K) := (fun τ => σ * τ) ⁻¹' U
    have hVopen : IsOpen V := by
      exact hU.preimage (continuous_const.mul continuous_id)
    have hVone : (1 : Gal(KAb / K)) ∈ V := by
      change σ * 1 ∈ U
      simpa using hσ
    obtain ⟨L, hL⟩ :=
      (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois V).mp
        (hVopen.mem_nhds hVone)
    obtain ⟨x, hx⟩ :=
      h L
        (InfiniteGalois.proj L
          ((chapter07AbelianGaloisLimitEquiv K KAb) σ))
    have hfix :
        σ⁻¹ * chapter07LocalReciprocity S x ∈
          (L.fixingSubgroup : Set Gal(KAb / K)) := by
      have hfix' :
          σ⁻¹ * chapter07LocalReciprocity S x ∈
              (L.fixingSubgroup : Set Gal(KAb / K)) ↔
            (σ⁻¹ * chapter07LocalReciprocity S x).restrictNormalHom L = 1 := by
        simpa only [SetLike.mem_coe] using
          (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff
            (σ⁻¹ * chapter07LocalReciprocity S x) L)
      apply hfix'.2
      change InfiniteGalois.proj L
          ((chapter07AbelianGaloisLimitEquiv K KAb)
            (σ⁻¹ * chapter07LocalReciprocity S x)) = 1
      have he :
          (chapter07AbelianGaloisLimitEquiv K KAb) σ⁻¹ =
            ((chapter07AbelianGaloisLimitEquiv K KAb) σ)⁻¹ := by
        exact (chapter07AbelianGaloisLimitEquiv K KAb).toMulEquiv.map_inv σ
      have hx' :
          InfiniteGalois.proj L
              ((chapter07AbelianGaloisLimitEquiv K KAb)
                (chapter07LocalReciprocity S x)) =
            InfiniteGalois.proj L
              ((chapter07AbelianGaloisLimitEquiv K KAb) σ) := by
        exact hx
      calc
        _ = (InfiniteGalois.proj L
              ((chapter07AbelianGaloisLimitEquiv K KAb) σ))⁻¹ *
            InfiniteGalois.proj L
              ((chapter07AbelianGaloisLimitEquiv K KAb)
                (chapter07LocalReciprocity S x)) := by
          rw [map_mul, map_mul, he, map_inv (InfiniteGalois.proj L)]
        _ = 1 := by rw [hx', inv_mul_cancel]
    have hVmem : σ⁻¹ * chapter07LocalReciprocity S x ∈ V := hL hfix
    refine ⟨chapter07LocalReciprocity S x, ?_, ⟨x, rfl⟩⟩
    change σ * (σ⁻¹ * chapter07LocalReciprocity S x) ∈ U at hVmem
    simpa [mul_assoc] using hVmem

/-- The image of local reciprocity is dense in the profinite abelian Galois
group. -/
theorem chapter07_local_reciprocity_dense
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    DenseRange (chapter07LocalReciprocity S) := by
  apply
    (chapter07_local_reciprocity_dense_iff_finite_projections_surjective S).2
  intro L
  exact chapter07_local_reciprocity_surjective_on_finite_level S L

/-- Data for the maximal unramified quotient in arithmetic normalization. -/
/- LOCAL_DEPENDENCY_GUESS: earlier local-field chapters provide the maximal
unramified quotient and identify its arithmetic coordinate. -/
structure Chapter07ArithmeticUnramifiedQuotient
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K))) where
  localField : Chapter07LocalFieldData K
  G : Type*
  [groupG : Group G]
  [topologyG : TopologicalSpace G]
  [topologicalGroupG : IsTopologicalGroup G]
  quotient : Gal(KAb / K) →* G
  quotient_continuous : Continuous quotient
  quotient_surjective : Function.Surjective quotient
  quotient_kernel :
    (letI : Group G := groupG; quotient.ker = I)
  completionEquiv : G ≃ₜ* Chapter07ProfiniteIntegers
  uniformizer : Kˣ
  valuation_uniformizer :
    localField.valuation (uniformizer : K) = (1 : WithTop ℤ)
  coordinate_uniformizer :
    localField.valuation_coordinate.valuation uniformizer =
      Multiplicative.ofAdd 1
  reciprocity_valuation :
    ∀ x : Kˣ,
      completionEquiv (quotient (chapter07LocalReciprocity S x)) =
      chapter07IntegerToProfiniteCompletion
        (Multiplicative.toAdd (localField.valuation_coordinate.valuation x))

/-- The arithmetic unramified coordinate of reciprocity has exactly the
integer image inside the profinite integers. -/
theorem chapter07_unramified_reciprocity_image_is_integer
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K)))
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S I) :
    Set.range (fun x : Kˣ =>
      U.completionEquiv (U.quotient (chapter07LocalReciprocity S x))) =
      Set.range chapter07IntegerToProfiniteCompletion := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.toAdd
      (U.localField.valuation_coordinate.valuation x),
      (U.reciprocity_valuation x).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨U.uniformizer ^ z, ?_⟩
    change U.completionEquiv
      (U.quotient (chapter07LocalReciprocity S (U.uniformizer ^ z))) =
      chapter07IntegerToProfiniteCompletion z
    rw [U.reciprocity_valuation]
    simp [map_zpow, U.coordinate_uniformizer]

/-- The integral powers form a dense proper subgroup of the profinite
integers. -/
theorem chapter07_integer_image_dense_and_proper :
    Dense (Set.range chapter07IntegerToProfiniteCompletion) ∧
      Set.range chapter07IntegerToProfiniteCompletion ≠
        (Set.univ : Set Chapter07ProfiniteIntegers) := by
  have hrange :
      Set.range chapter07IntegerToProfiniteCompletion =
        Set.range (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Multiplicative.ofAdd z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨Multiplicative.toAdd z, by
        change chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)
            (Multiplicative.ofAdd (Multiplicative.toAdd z)) =
          chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ) z
        simp⟩
  rw [hrange]
  constructor
  · apply dense_iff_inter_open.mpr
    rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
    have hpre : ⟨spc, hspc⟩ ∈ Subtype.val ⁻¹' s := hsv.symm ▸ uDefaultSpec
    have hspc_s : spc ∈ s := hpre
    rcases (isOpen_pi_iff.mp hsO) _ hspc_s with ⟨J, fJ, hJ1, hJ2⟩
    let M : Subgroup (Multiplicative ℤ) :=
      iInf fun (j : J) => j.1.toSubgroup
    have hM : M.Normal :=
      Subgroup.normal_iInf_normal fun j => inferInstance
    have hMFinite : M.FiniteIndex := by
      apply Subgroup.finiteIndex_iInf
      infer_instance
    have hMOpen : IsOpen (M : Set (Multiplicative ℤ)) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun i => i.1.isOpen
    let m : Chapter07OpenFiniteIndexNormalSubgroup (Multiplicative ℤ) :=
      { toSubgroup := M
        isNormal' := hM
        isFiniteIndex' := hMFinite
        isOpen := hMOpen }
    rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
    use chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ) origin
    refine ⟨?_, origin, rfl⟩
    rw [← hsv]
    apply hJ2
    intro a a_in_J
    let M_to_Na : m ⟶ a :=
      (iInf_le (fun (j : J) => (j.1.toSubgroup)) ⟨a, a_in_J⟩).hom
    rw [← (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ) origin).property
      M_to_Na]
    have heta_m :
        (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ) origin).val m =
          QuotientGroup.mk' M origin := by
      rfl
    rw [heta_m, horigin]
    exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right
  · intro hsurj
    have hsurj' :
        Function.Surjective
          (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)) := by
      intro y
      have hy : y ∈ Set.range
          (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)) := by
        rw [hsurj]
        trivial
      exact hy
    have hcount : Countable Chapter07ProfiniteIntegers := by
      rw [countable_iff_nonempty_embedding]
      obtain ⟨e, he⟩ := Countable.exists_injective_nat (Multiplicative ℤ)
      refine ⟨⟨fun y => e (Function.invFun
        (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)) y), ?_⟩⟩
      exact he.comp (Function.RightInverse.injective
        (Function.rightInverse_invFun hsurj'))
    obtain ⟨y, hy⟩ := nonempty_interior_of_iUnion_of_closed
      (f := fun y : Chapter07ProfiniteIntegers => ({y} : Set Chapter07ProfiniteIntegers))
      (fun _ => isClosed_singleton) (by
        ext z
        constructor
        · intro _
          trivial
        · intro _
          exact Set.mem_iUnion.2 ⟨z, rfl⟩)
    obtain ⟨z, hz⟩ := hy
    have hyz : y = z := by
      exact (Set.mem_singleton_iff.mp (interior_subset hz)).symm
    have hy_nhds : ({y} : Set Chapter07ProfiniteIntegers) ∈ nhds y := by
      have hy_interior : y ∈ interior ({y} : Set Chapter07ProfiniteIntegers) := by
        rw [← hyz] at hz
        exact hz
      exact mem_interior_iff_mem_nhds.mp hy_interior
    have hopen_y : IsOpen ({y} : Set Chapter07ProfiniteIntegers) := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      have hxy : x = y := Set.mem_singleton_iff.mp hx
      simpa [hxy] using hy_nhds
    have hopen_all : ∀ x : Chapter07ProfiniteIntegers,
        IsOpen ({x} : Set Chapter07ProfiniteIntegers) := by
      intro x
      have himage : IsOpen
          ((fun z : Chapter07ProfiniteIntegers => (x * y⁻¹) * z) ''
            ({y} : Set Chapter07ProfiniteIntegers)) :=
        isOpenMap_mul_left (x * y⁻¹) _ hopen_y
      have himage_eq :
          (fun z : Chapter07ProfiniteIntegers => (x * y⁻¹) * z) ''
              ({y} : Set Chapter07ProfiniteIntegers) = {x} := by
        ext w
        constructor
        · rintro ⟨z, hz, rfl⟩
          simp only [Set.mem_singleton_iff] at hz
          subst z
          simp
        · intro hw
          have hwx : w = x := Set.mem_singleton_iff.mp hw
          subst w
          exact ⟨y, rfl, by simp⟩
      rw [← himage_eq]
      exact himage
    have hdisc : DiscreteTopology Chapter07ProfiniteIntegers :=
      (discreteTopology_iff_isOpen_singleton).2 hopen_all
    have hfinite : Finite Chapter07ProfiniteIntegers :=
      @finite_of_compact_of_discrete _ _ inferInstance hdisc
    have hres : AddGroup.ResiduallyFinite ℤ := by
      apply AddGroup.residuallyFinite_of_forall_exists_finite_addMonoidHom
      intro g hg
      let n : ℕ := g.natAbs + 1
      let f : ℤ →+ ZMod n := (Int.castRingHom (ZMod n)).toAddMonoidHom
      have hf : f g ≠ 0 := by
        change (g : ZMod n) ≠ 0
        intro hzero
        have hdvd : (n : ℤ) ∣ g :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd g n).mp hzero
        obtain ⟨k, hk⟩ := hdvd
        have hdvd_nat : n ∣ g.natAbs := by
          refine ⟨k.natAbs, ?_⟩
          rw [← Int.natAbs_natCast n, ← Int.natAbs_mul]
          exact congrArg Int.natAbs hk
        apply (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hg) ?_) hdvd_nat
        exact Nat.lt_succ_self _
      exact ⟨ZMod n, inferInstance, inferInstance, f, hf⟩
    have heta_inj : Function.Injective
        (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)) := by
      intro x y hxy
      by_contra hxy'
      have hdiff : Multiplicative.toAdd (x * y⁻¹) ≠ 0 := by
        intro h
        have hxy_add : Multiplicative.toAdd x = Multiplicative.toAdd y := by
          change Multiplicative.toAdd x - Multiplicative.toAdd y = 0 at h
          exact sub_eq_zero.mp h
        exact hxy' (congrArg Multiplicative.ofAdd hxy_add)
      obtain ⟨H, hHFinite, hdH⟩ :=
        (AddGroup.residuallyFinite_iff_exists_finiteIndex.mp hres)
          (Multiplicative.toAdd (x * y⁻¹)) hdiff
      let Hmul : Subgroup (Multiplicative ℤ) := H.toSubgroup
      have hHmulFinite : Hmul.FiniteIndex :=
        (AddSubgroup.finiteIndex_toSubgroup_iff H).2 hHFinite
      let m : Chapter07OpenFiniteIndexNormalSubgroup (Multiplicative ℤ) :=
        { toSubgroup := Hmul
          isNormal' := inferInstance
          isFiniteIndex' := hHmulFinite
          isOpen := isOpen_discrete _ }
      have hcoord := congrArg
        (fun q : Chapter07ProfiniteIntegers =>
          chapter07OpenProfiniteCompletionProjection (Multiplicative ℤ) m q) hxy
      have hquot :
          (x : Multiplicative ℤ ⧸ Hmul) = y := by
        change chapter07OpenProfiniteCompletionProjection (Multiplicative ℤ) m
            (chapter07OpenProfiniteCompletionEta (Multiplicative ℤ) x) =
          chapter07OpenProfiniteCompletionProjection (Multiplicative ℤ) m
            (chapter07OpenProfiniteCompletionEta (Multiplicative ℤ) y) at hcoord
        change (x : Multiplicative ℤ ⧸ m.toSubgroup) = y
        simpa only [chapter07OpenProfiniteCompletionProjection_eta] using hcoord
      have hdmem : x * y⁻¹ ∈ Hmul :=
        (QuotientGroup.eq_iff_div_mem).mp hquot
      exact hdH (by exact hdmem)
    have hsourcefinite : Finite (Multiplicative ℤ) :=
      @Finite.of_injective _ _ hfinite
        (chapter07OpenProfiniteCompletionEtaFn (Multiplicative ℤ)) heta_inj
    exact Infinite.not_finite hsourcefinite

/-- No genuinely nonintegral profinite Frobenius exponent is represented by a
field element under the arithmetic-normalized unramified quotient. -/
theorem chapter07_local_reciprocity_not_surjective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K)))
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S I) :
    ¬ Function.Surjective (chapter07LocalReciprocity S) := by
  sorry

/-- A topological group equivalence preserves compactness. -/
theorem chapter07_no_topological_equiv_from_noncompact_to_compact
    {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [NoncompactSpace X] [Group Y] [TopologicalSpace Y] [CompactSpace Y] :
    ¬ Nonempty (X ≃ₜ* Y) := by
  sorry

/-- The multiplicative group of a complete discretely valued local field with
finite residue field is noncompact. -/
/- LOCAL_DEPENDENCY_GUESS: the preceding local-field topology chapters supply
the valuation topology and its noncompact valuation coordinate. -/
theorem chapter07_local_field_units_noncompact
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ] (D : Chapter07LocalFieldData K) :
    NoncompactSpace Kˣ := by
  exact
    @LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01_local_field_units_noncompact
      K _ D.valuation D.local_field _ _ D.unit_group_topology
      D.unit_group_topological inferInstance D.coordinate_equiv

/-- The profinite abelian Galois target is compact. -/
theorem chapter07_reciprocity_target_is_compact
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    IsCompact (Set.univ : Set (Gal(KAb / K))) := by
  sorry

/-- The compactness obstruction for identifying K-units literally with the
whole profinite Galois group. -/
theorem chapter07_reciprocity_is_not_a_topological_equivalence
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ] [NoncompactSpace Kˣ]
    [IsAbelianGalois K KAb]
    (hcompact : IsCompact (Set.univ : Set (Gal(KAb / K)))) :
    ¬ Nonempty (Kˣ ≃ₜ* Gal(KAb / K)) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
