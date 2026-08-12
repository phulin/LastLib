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
  sorry

/- The unit filtration is cofinal among neighborhoods of the identity. -/
theorem chapter10_open_subgroup_contains_deep_units
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [TopologicalSpace Kˣ]
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (V : Subgroup Kˣ) (hopen : IsOpen (V : Set Kˣ)) :
    ∃ n : ℕ, Chapter10FieldUnitFiltration D.valuation n ≤ V := by
  sorry

/- A source-order version with the local valuation made explicit. -/
theorem chapter10_congruence_precision_data
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [TopologicalSpace Kˣ]
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (V : Subgroup Kˣ) (hV : V ≤ chapter10LocalUnitSubgroup D)
    (hopen : IsOpen (V : Set Kˣ))
    (a : Chapter10RingUnitGroup D.valuation) :
    ∃ n r : ℕ, 1 ≤ n ∧ 0 < r ∧
      Chapter10FieldUnitFiltration D.valuation n ≤ V ∧
      chapter10RingUnitInField D.valuation (a ^ r) ∈ V := by
  sorry

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
  sorry

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
  sorry

theorem chapter10_congruence_quotient_is_finite
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (m m' n : ℕ) (hm' : 0 < m') (hn : 0 < n)
    (a : Chapter10RingUnitGroup D.valuation) :
    Finite (Chapter10CongruenceQuotient D m m' n a) := by
  sorry

theorem chapter10_congruence_presented_quotient_is_finite
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (m' n : ℕ) (hm' : 0 < m') (hn : 0 < n)
    (C : Chapter10CongruenceCoordinateData D m' n)
    (m : ℕ) (a : Chapter10RingUnitGroup D.valuation) (V : Subgroup Kˣ) :
    Finite (Chapter10CongruencePresentedQuotient D m' n C m a V) := by
  sorry

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
  sorry

theorem chapter10_open_norm_subgroup_has_finite_conductor
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter10LocalFieldProfile K)
    (hbasis :
      LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
        D.valuation)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ)) :
    Chapter10FiniteConductor D H := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
