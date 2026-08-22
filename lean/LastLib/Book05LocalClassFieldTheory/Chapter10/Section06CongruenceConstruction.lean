import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

local instance chapter10_isMulCommutative_of_commGroup
    {G : Type*} [CommGroup G] : IsMulCommutative G :=
  IsMulCommutative.of_comm (fun _ _ => mul_comm _ _)

/-! ## 10.6. Building an extension from congruence data -/

/- The subgroup presentation `H = <πᵐ a> V`, with `a` kept in the canonical
   ring-of-integers unit group. -/
def chapter10PresentedSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (π : Kˣ) (a : Chapter10RingUnitGroup D.valuation)
    (m : ℕ) (V : Subgroup Kˣ) : Subgroup Kˣ :=
  Subgroup.zpowers
      (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V

theorem chapter10_mem_presented_subgroup_iff
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (π : Kˣ) (a : Chapter10RingUnitGroup D.valuation)
    (m : ℕ) (V : Subgroup Kˣ) (x : Kˣ) :
    x ∈ chapter10PresentedSubgroup D π a m V ↔
      ∃ z : ℤ, ∃ v : V,
        x = (π ^ m * chapter10RingUnitInField D.valuation a) ^ z * (v : Kˣ) := by
  change x ∈ Subgroup.zpowers
      (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V ↔ _
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, v, hv, hxy⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨z, ⟨v, hv⟩, ?_⟩
    rw [← hxy, ← hz]
  · rintro ⟨z, v, hx⟩
    have hz : (π ^ m * chapter10RingUnitInField D.valuation a) ^ z ∈
        Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) :=
      (Subgroup.mem_zpowers_iff).2 ⟨z, rfl⟩
    refine ⟨(π ^ m * chapter10RingUnitInField D.valuation a) ^ z, hz,
      (v : Kˣ), v.property, ?_⟩
    exact hx.symm

/- The unit filtration is cofinal among neighborhoods of the identity. -/
theorem chapter10_open_subgroup_contains_deep_units
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [TopologicalSpace Kˣ]
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (V : Subgroup Kˣ) (hopen : IsOpen (V : Set Kˣ)) :
    ∃ n : ℕ, Chapter10FieldUnitFiltration D.valuation n ≤ V := by
  obtain ⟨n, hn⟩ := hbasis.2 (V : Set Kˣ) (hopen.mem_nhds V.one_mem)
  exact ⟨n, fun x hx => hn hx⟩

private theorem chapter10_field_filtration_quotient_finite
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) (n : ℕ)
    : Finite ((Chapter10FieldUnitFiltration D.valuation 0) ⧸
      (Chapter10FieldUnitFiltration D.valuation n).subgroupOf
      (Chapter10FieldUnitFiltration D.valuation 0)) := by
  let A := Chapter10ValuationRing D.valuation
  let U : ℕ → Subgroup Aˣ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A
  let V : ℕ → Subgroup Kˣ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10FieldUnitFiltration A
  let _ : (U n).FiniteIndex := by
    cases n with
    | zero =>
        change (
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
            A 0).FiniteIndex
        rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_zero]
        infer_instance
    | succ n =>
        let _ : Finite (
            LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10PrecisionQuotient
              A (n + 1)) :=
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_finite_residue_finite_precision_quotients
            A n D.valuationRing_dvr
        let f : Aˣ →* (
            LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10PrecisionQuotient
              A (n + 1))ˣ :=
          Units.map
            (Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom
        have hker : f.ker = U (n + 1) := by
          ext u
          constructor
          · intro hu
            change f u = 1 at hu
            have hv := congrArg Units.val hu
            change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
                (u : A) = 1 at hv
            change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
            apply Ideal.Quotient.eq_zero_iff_mem.mp
            rw [map_sub]
            exact sub_eq_zero.mpr hv
          · intro hu
            apply MonoidHom.mem_ker.mpr
            apply Units.ext
            change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
                (u : A) = 1
            rw [← sub_eq_zero]
            change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
                ((u : A) - 1) = 0
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
        rw [← hker]
        infer_instance
  let hUn0 : U n ≤ U 0 := by
    intro u hu
    change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n at hu
    change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ 0
    exact (Ideal.pow_le_pow_right (Nat.zero_le n)) hu
  let f : Aˣ →* V 0 :=
    { toFun := fun u =>
        ⟨Units.map A.subtype.toMonoidHom u, by
          change Units.map A.subtype.toMonoidHom u ∈
            (U 0).map (Units.map A.subtype.toMonoidHom)
          exact ⟨u, by
            simp [U, LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitLayer],
            rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp }
  have hf_surj : Function.Surjective f := by
    intro x
    rcases x.property with ⟨u, hu, hux⟩
    refine ⟨(u : Aˣ), ?_⟩
    apply Subtype.ext
    exact hux
  have hf_inj : Function.Injective f := by
    intro u v huv
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun x : V 0 => ((x : Kˣ) : K)) huv
  let ef : Aˣ ≃* V 0 := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let F : Aˣ →* (V 0 ⧸ (V n).subgroupOf (V 0)) :=
    (QuotientGroup.mk' ((V n).subgroupOf (V 0))).comp ef.toMonoidHom
  have hFsurj : Function.Surjective F :=
    (QuotientGroup.mk'_surjective _).comp ef.surjective
  have hker : F.ker = U n := by
    ext u
    constructor
    · intro hu
      change F u = 1 at hu
      have huV : (ef u : V 0) ∈ (V n).subgroupOf (V 0) :=
        (QuotientGroup.eq_one_iff _).mp hu
      change (ef u : Kˣ) ∈ V n at huV
      rcases huV with ⟨a, ha, hEq⟩
      have heq : ef u = ef (a : Aˣ) := by
        apply Subtype.ext
        change Units.map A.subtype.toMonoidHom u =
          Units.map A.subtype.toMonoidHom (a : Aˣ)
        exact hEq.symm
      rw [ef.injective heq]
      exact ha
    · intro hu
      apply MonoidHom.mem_ker.mpr
      change QuotientGroup.mk' ((V n).subgroupOf (V 0)) (ef u) = 1
      apply (QuotientGroup.eq_one_iff _).2
      change (ef u : Kˣ) ∈ V n
      change Units.map A.subtype.toMonoidHom u ∈
        (U n).map (Units.map A.subtype.toMonoidHom)
      exact ⟨u, hu, rfl⟩
  let eV : (Aˣ ⧸ U n) ≃* (V 0 ⧸ (V n).subgroupOf (V 0)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)
  exact Finite.of_equiv _ eV.toEquiv

/- A source-order version with the local valuation made explicit. -/
theorem chapter10_congruence_precision_data
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [TopologicalSpace Kˣ]
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (V : Subgroup Kˣ) (_hV : V ≤ chapter10LocalUnitSubgroup D)
    (hopen : IsOpen (V : Set Kˣ))
    (a : Chapter10RingUnitGroup D.valuation) :
    ∃ n r : ℕ, 1 ≤ n ∧ 0 < r ∧
      Chapter10FieldUnitFiltration D.valuation n ≤ V ∧
      chapter10RingUnitInField D.valuation (a ^ r) ∈ V := by
  obtain ⟨k, hk⟩ := chapter10_open_subgroup_contains_deep_units D hbasis V hopen
  have hdesc : Chapter10FieldUnitFiltration D.valuation (k + 1) ≤
      Chapter10FieldUnitFiltration D.valuation k := by
    intro x hx
    change x ∈ (Chapter10UnitFiltration D.valuation (k + 1)).map
      (Units.map (Chapter10ValuationRing D.valuation).subtype.toMonoidHom) at hx
    rcases hx with ⟨u, hu, rfl⟩
    exact ⟨u,
      chapter10_unit_filtration_descending D.valuation k hu, rfl⟩
  let n := k + 1
  have hn : 1 ≤ n := by
    dsimp [n]
    omega
  have hdeep : Chapter10FieldUnitFiltration D.valuation n ≤ V := by
    exact hdesc.trans hk
  let U₀ := Chapter10FieldUnitFiltration D.valuation 0
  let Uₙ := Chapter10FieldUnitFiltration D.valuation n
  let _ : Finite (U₀ ⧸ Uₙ.subgroupOf U₀) :=
    chapter10_field_filtration_quotient_finite D n
  have hrel : Uₙ.relIndex U₀ ≠ 0 := by
    change (Uₙ.subgroupOf U₀).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  let a₀ : Kˣ := chapter10RingUnitInField D.valuation a
  have ha₀ : a₀ ∈ U₀ := by
    change a₀ ∈ (Chapter10UnitFiltration D.valuation 0).map
      (Units.map (Chapter10ValuationRing D.valuation).subtype.toMonoidHom)
    exact ⟨a, by
      simp [Chapter10UnitFiltration,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08UnitLayer], rfl⟩
  obtain ⟨r, hr, _, har⟩ :=
    Subgroup.exists_pow_mem_of_relIndex_ne_zero hrel ha₀
  have harV : a₀ ^ r ∈ V := hdeep har.1
  refine ⟨n, r, hn, hr, hdeep, ?_⟩
  rw [map_pow]
  exact harV

/- After replacing `m` by `m' = r m`, the ambient norm subgroup lies in the
   presented subgroup. -/
theorem chapter10_congruence_ambient_subgroup_le_presented
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (π : Kˣ) (a : Chapter10RingUnitGroup D.valuation)
    (m n r : ℕ) (V : Subgroup Kˣ)
    (hn : Chapter10FieldUnitFiltration D.valuation n ≤ V)
    (hr : chapter10RingUnitInField D.valuation (a ^ r) ∈ V) :
    chapter10ValueUnitSubgroup D π (r * m) n ≤
      chapter10PresentedSubgroup D π a m V := by
  change Subgroup.zpowers (π ^ (r * m)) ⊔
      Chapter10FieldUnitFiltration D.valuation n ≤
    Subgroup.zpowers
        (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V
  apply sup_le
  · apply Subgroup.zpowers_le_of_mem
    have hg : π ^ m * chapter10RingUnitInField D.valuation a ∈
        Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V :=
      (le_sup_left :
        Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ≤
          Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V)
        ((Subgroup.mem_zpowers_iff).2 ⟨1, by simp⟩)
    have ha : (chapter10RingUnitInField D.valuation a) ^ r ∈
        Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V :=
      (le_sup_right : V ≤
        Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V) hr
    have hprod :
        (π ^ m * chapter10RingUnitInField D.valuation a) ^ r *
            (chapter10RingUnitInField D.valuation a ^ r)⁻¹ ∈
          Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V :=
      (Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V).mul_mem
        ((Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V).pow_mem hg r)
        ((Subgroup.zpowers (π ^ m * chapter10RingUnitInField D.valuation a) ⊔ V).inv_mem ha)
    simpa [mul_pow, pow_mul, mul_comm] using hprod
  · exact hn.trans le_sup_right

/- The finite coordinate group before imposing the displayed generator
   relation.  This single-relation quotient is the special case in which no
   further image of `V` is being imposed; the corrected general quotient is
   `Chapter10CongruencePresentedQuotient` below. -/
abbrev chapter10CongruenceFiniteGroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ) : Type _ :=
  Multiplicative (ZMod m') × (Chapter10PrecisionQuotient D.valuation n)ˣ

local instance chapter10CongruenceFiniteGroup_commGroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) (m' n : ℕ) :
    CommGroup (chapter10CongruenceFiniteGroup D m' n) := by
  infer_instance

def chapter10CongruenceRelationGenerator
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m m' n : ℕ) (a : Chapter10RingUnitGroup D.valuation) :
    chapter10CongruenceFiniteGroup D m' n :=
  (Multiplicative.ofAdd (m : ZMod m'),
    chapter10PrecisionUnitReduction D.valuation n a)

/- LOCAL_DEPENDENCY_GUESS: the earlier valuation/unit decomposition supplies a
   normalized surjective coordinate map with this kernel.  A finite coordinate
   map packages the valuation coordinate and the unit
   reduction map.  Its kernel is the common deep subgroup, and the displayed
   generator formula fixes the normalization of the two coordinates. -/
structure Chapter10CongruenceCoordinateData
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ) where
  coordinate : Kˣ →*
    chapter10CongruenceFiniteGroup D m' n
  surjective : Function.Surjective coordinate
  kernel_eq : coordinate.ker =
    chapter10ValueUnitSubgroup D D.uniformizer m' n
  generator_apply : ∀ (m : ℕ) (a : Chapter10RingUnitGroup D.valuation),
    coordinate (D.uniformizer ^ m * chapter10RingUnitInField D.valuation a) =
      chapter10CongruenceRelationGenerator D m m' n a

def chapter10CongruenceRelationSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m m' n : ℕ) (a : Chapter10RingUnitGroup D.valuation) :
    Subgroup (chapter10CongruenceFiniteGroup D m' n) :=
  Subgroup.zpowers
    (chapter10CongruenceRelationGenerator D m m' n a)

abbrev Chapter10CongruenceQuotient
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m m' n : ℕ) (a : Chapter10RingUnitGroup D.valuation) : Type _ :=
  chapter10CongruenceFiniteGroup D m' n ⧸
    chapter10CongruenceRelationSubgroup D m m' n a

def chapter10CongruencePresentedRelationSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ) (C : Chapter10CongruenceCoordinateData D m' n)
    (m : ℕ) (a : Chapter10RingUnitGroup D.valuation)
    (V : Subgroup Kˣ) :
    Subgroup (chapter10CongruenceFiniteGroup D m' n) :=
  Subgroup.map C.coordinate
    (chapter10PresentedSubgroup D D.uniformizer a m V)

abbrev Chapter10CongruencePresentedQuotient
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ) (C : Chapter10CongruenceCoordinateData D m' n)
    (m : ℕ) (a : Chapter10RingUnitGroup D.valuation)
    (V : Subgroup Kˣ) : Type _ :=
  chapter10CongruenceFiniteGroup D m' n ⧸
    chapter10CongruencePresentedRelationSubgroup D m' n C m a V

theorem chapter10_congruence_presented_quotient_equiv
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ) (C : Chapter10CongruenceCoordinateData D m' n)
    (m : ℕ) (a : Chapter10RingUnitGroup D.valuation) (V : Subgroup Kˣ)
    (hbase : chapter10ValueUnitSubgroup D D.uniformizer m' n ≤
      chapter10PresentedSubgroup D D.uniformizer a m V) :
    Nonempty
      ((Kˣ ⧸ chapter10PresentedSubgroup D D.uniformizer a m V) ≃*
        Chapter10CongruencePresentedQuotient D m' n C m a V) := by
  let H := chapter10PresentedSubgroup D D.uniformizer a m V
  let M := Subgroup.map C.coordinate H
  let F : Kˣ →* (chapter10CongruenceFiniteGroup D m' n ⧸ M) :=
    (QuotientGroup.mk' M).comp C.coordinate
  have hFsurj : Function.Surjective F :=
    (QuotientGroup.mk'_surjective M).comp C.surjective
  have hFker : F.ker = H := by
    ext x
    constructor
    · intro hx
      change F x = 1 at hx
      have hxM : C.coordinate x ∈ M :=
        (QuotientGroup.eq_one_iff (N := M) _).mp hx
      rcases Subgroup.mem_map.mp hxM with ⟨y, hy, hxy⟩
      have hdiff : y⁻¹ * x ∈ C.coordinate.ker := by
        apply MonoidHom.mem_ker.mpr
        change C.coordinate (y⁻¹ * x) = 1
        rw [map_mul, map_inv, hxy]
        simp
      rw [C.kernel_eq] at hdiff
      simpa using H.mul_mem hy (hbase hdiff)
    · intro hx
      apply MonoidHom.mem_ker.mpr
      change QuotientGroup.mk' M (C.coordinate x) = 1
      apply (QuotientGroup.eq_one_iff (N := M) _).2
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have e : Kˣ ⧸ H ≃*
      chapter10CongruenceFiniteGroup D m' n ⧸ M :=
    (QuotientGroup.quotientMulEquivOfEq hFker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)
  exact ⟨e⟩

theorem chapter10_congruence_quotient_is_finite
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (m m' n : ℕ) (hm' : 0 < m') (hn : 0 < n)
    (a : Chapter10RingUnitGroup D.valuation) :
    Finite (Chapter10CongruenceQuotient D m m' n a) := by
  cases n with
  | zero => omega
  | succ n =>
      let _ : NeZero m' := ⟨Nat.ne_of_gt hm'⟩
      let _ : Finite (Chapter10PrecisionQuotient D.valuation (n + 1)) :=
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_finite_residue_finite_precision_quotients
          (Chapter10ValuationRing D.valuation) n D.valuationRing_dvr
      infer_instance

theorem chapter10_congruence_presented_quotient_is_finite
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (m' n : ℕ) (hm' : 0 < m') (hn : 0 < n)
    (C : Chapter10CongruenceCoordinateData D m' n)
    (m : ℕ) (a : Chapter10RingUnitGroup D.valuation) (V : Subgroup Kˣ) :
    Finite (Chapter10CongruencePresentedQuotient D m' n C m a V) := by
  cases n with
  | zero => omega
  | succ n =>
      let _ : NeZero m' := ⟨Nat.ne_of_gt hm'⟩
      let _ : Finite (Chapter10PrecisionQuotient D.valuation (n + 1)) :=
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_finite_residue_finite_precision_quotients
          (Chapter10ValuationRing D.valuation) n D.valuationRing_dvr
      infer_instance

/- The subgroup in the finite Galois group corresponding to a presented base
   subgroup is the image of that subgroup under finite reciprocity. -/
def chapter10CongruenceGaloisSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ)
    (A : Chapter10ExplicitAmbientExtension D m' n)
    (H : Subgroup Kˣ) : Subgroup (Gal(A.field / K)) := by
  letI : FiniteDimensional K A.field := A.finite
  exact Subgroup.map A.artin.reciprocity H

def chapter10CongruenceFixedField
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ)
    (A : Chapter10ExplicitAmbientExtension D m' n)
    (H : Subgroup Kˣ) : IntermediateField K A.field :=
  IntermediateField.fixedField (chapter10CongruenceGaloisSubgroup D m' n A H)

theorem chapter10_congruence_fixed_field_corresponds_to_presented_subgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ)
    (A : Chapter10ExplicitAmbientExtension D m' n)
    (π : Kˣ) (a : Chapter10RingUnitGroup D.valuation)
    (m : ℕ) (V : Subgroup Kˣ)
    (H : Subgroup Kˣ)
    (hpresented : H = chapter10PresentedSubgroup D π a m V)
    [FiniteDimensional K A.field]
    [FiniteDimensional K (chapter10CongruenceFixedField D m' n A H)]
    (hkernel : chapter10NormSubgroup K A.field ≤ H) :
    chapter10NormSubgroup K
        (chapter10CongruenceFixedField D m' n A H) = H := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the unramified and formal-module constructions of
   the preceding chapters supply the explicit finite abelian ambient field
   `E_{m',n}` with this norm subgroup. -/
theorem chapter10_explicit_ambient_extension_exists
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m' n : ℕ) (hm' : 0 < m') (hn : 0 < n) :
    Nonempty (Chapter10ExplicitAmbientExtension D m' n) := by
  sorry

theorem chapter10_finite_abelian_extensions_have_finite_conductor
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace Kˣ]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : Chapter10LocalFieldProfile K)
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (hopen : IsOpen (chapter10NormSubgroup K L : Set Kˣ)) :
    Chapter10FiniteConductor D (chapter10NormSubgroup K L) := by
  exact chapter10_open_subgroup_contains_deep_units D hbasis
    (chapter10NormSubgroup K L) hopen

theorem chapter10_open_norm_subgroup_has_finite_conductor
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter10LocalFieldProfile K)
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ)) :
    Chapter10FiniteConductor D H := by
  exact chapter10_open_subgroup_contains_deep_units D hbasis H hopen

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
