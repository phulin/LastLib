import LastLib.Book04AdelesAndIdeles.Chapter03.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.1 The algebraic construction -/

/- SOURCE_ISSUE:
  The sentence that the direct sum "excludes the family whose component is 1
  everywhere, and therefore has no multiplicative identity" is false for the
  usual direct sum: the all-identity family has empty support and is included.
  The intended defect is that the direct sum excludes families with infinitely
  many non-identity coordinates.  In additive notation, use a nonzero
  constant family for the counterexample and do not attribute a multiplicative
  identity to the additive direct sum.
-/

universe u v

section MultiplicativeRestrictedProducts

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- The restricted product inherits its group structure from the dependent
product, so all operations are componentwise. -/
instance chapter03_restrictedProduct_is_group
    (H : ∀ i, Subgroup (G i)) :
    Group (Chapter03RestrictedProduct H) := by
  infer_instance

theorem chapter03_restrictedProduct_mul_apply
    (H : ∀ i, Subgroup (G i)) (x y : Chapter03RestrictedProduct H) (i : I) :
    ((x * y : Chapter03RestrictedProduct H) : ∀ i, G i) i =
      ((x : ∀ i, G i) i) * ((y : ∀ i, G i) i) := by
  rfl

theorem chapter03_restrictedProduct_inv_apply
    (H : ∀ i, Subgroup (G i)) (x : Chapter03RestrictedProduct H) (i : I) :
    ((x⁻¹ : Chapter03RestrictedProduct H) : ∀ i, G i) i =
      (((x : ∀ i, G i) i)⁻¹) := by
  rfl

theorem chapter03_restrictedProduct_one_apply
    (H : ∀ i, Subgroup (G i)) (i : I) :
    ((1 : Chapter03RestrictedProduct H) : ∀ i, G i) i = 1 := by
  rfl

/-- A finite set of unrestricted indices can be absorbed into every stage. -/
theorem chapter03_unrestricted_coordinate_is_automatic
    (H : ∀ i, Subgroup (G i)) {i : I} (hH : H i = ⊤)
    (x : ∀ i, G i) : x i ∈ H i := by
  rw [hH]
  exact Set.mem_univ _

/-- Stage membership says exactly that the exceptional set is contained in
the chosen finite set of unrestricted coordinates. -/
theorem chapter03_stage_mem_iff_exceptional_subset
    (H : ∀ i, Subgroup (G i)) (S : Set I)
    (x : Chapter03RestrictedProduct H) :
    x ∈ chapter03StageSubgroup H S ↔
      chapter03ExceptionalSet H (x : ∀ i, G i) ⊆ S := by
  sorry

theorem chapter03_stage_contains_restricted_family
    (H : ∀ i, Subgroup (G i)) (S : Set I)
    (x : Chapter03RestrictedProduct H)
    (hS : chapter03ExceptionalSet H (x : ∀ i, G i) ⊆ S) :
    x ∈ chapter03StageSubgroup H S := by
  exact (chapter03_stage_mem_iff_exceptional_subset H S x).2 hS

theorem chapter03_restrictedProduct_is_increasing_union_of_stages
    (H : ∀ i, Subgroup (G i)) :
    (Set.univ : Set (Chapter03RestrictedProduct H)) =
      ⋃ S : Chapter03FiniteStageIndex,
        (chapter03StageSubgroup H S.1 : Set (Chapter03RestrictedProduct H)) :=
  chapter03_restrictedProduct_eq_iUnion_finite_stages H

/-- The coordinate type used to display a stage as
`∏ i ∈ S, G i × ∏ i ∉ S, H i`. -/
noncomputable def chapter03StageCoordinateType
    {I : Type u} {G : I → Type v} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) (i : I) : Type _ := by
  classical
  exact if i ∈ S then G i else ↥(H i)

abbrev Chapter03StageCoordinateProduct
    {I : Type u} {G : I → Type v} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) : Type _ :=
  ∀ i, chapter03StageCoordinateType H S i

theorem chapter03_stage_is_coordinate_product
    {I : Type u} {G : I → Type v} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) {S : Set I} (hS : S.Finite) :
    Nonempty (Chapter03Stage H S ≃
      Chapter03StageCoordinateProduct H S) := by
  sorry

/-- The additive construction uses local integral additive subgroups. -/
instance chapter03_additive_restrictedProduct_is_add_group
    {I : Type u} {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) :
    AddGroup (Chapter03AdditiveRestrictedProduct H) := by
  infer_instance

/-- The additive integral model attached to a valuation subring. -/
def chapter03ValuationRingAdditiveSubgroup
    {L : Type*} [Field L] (A : ValuationSubring L) : AddSubgroup L :=
  A.toSubring.toAddSubgroup

/-- The multiplicative unit model attached to a valuation subring, embedded in
the unit group of its fraction field. -/
def chapter03ValuationRingUnitSubgroup
    {L : Type*} [Field L] (A : ValuationSubring L) : Subgroup Lˣ :=
  (⊤ : Subgroup Aˣ).map (Units.map A.subtype.toMonoidHom)

theorem chapter03_valuationRing_additive_model_mem_iff
    {L : Type*} [Field L] (A : ValuationSubring L) (x : L) :
    x ∈ chapter03ValuationRingAdditiveSubgroup A ↔ x ∈ A :=
  Iff.rfl

theorem chapter03_valuationRing_unit_model_mem_iff
    {L : Type*} [Field L] (A : ValuationSubring L) (x : Lˣ) :
    x ∈ chapter03ValuationRingUnitSubgroup A ↔
      ∃ u : Aˣ, Units.map A.subtype.toMonoidHom u = x := by
  sorry

end MultiplicativeRestrictedProducts

end
end LastLib.Book04AdelesAndIdeles.Chapter03
