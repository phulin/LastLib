import LastLib.Book04AdelesAndIdeles.Chapter03.Dependencies
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.1 The algebraic construction -/

/-!
The book's direct-sum warning is read additively: finite support is measured
away from `0`, so the zero family is included while a constant family of
nonzero elements is excluded when the index set is infinite.  This is distinct
from a multiplicative direct sum, whose support is measured away from `1` and
which therefore contains its all-identity family.
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
  change (∀ i, i ∉ S → ((x : ∀ i, G i) i) ∈ H i) ↔
    chapter03ExceptionalSet H (x : ∀ i, G i) ⊆ S
  constructor
  · intro hx i hi
    by_contra hnot
    exact hi (hx i hnot)
  · intro hx i hi
    by_contra hnot
    exact hi (hx (by simpa [chapter03ExceptionalSet] using hnot))

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

noncomputable def chapter03_stage_is_coordinate_product
    {I : Type u} {G : I → Type v} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) {S : Set I} (hS : S.Finite) :
    Chapter03Stage H S ≃ Chapter03StageCoordinateProduct H S := by
  classical
  have hmem : ∀ i, i ∈ S → chapter03StageCoordinateType H S i = G i := by
    intro i hi
    simp [chapter03StageCoordinateType, hi]
  have hnotmem : ∀ i, i ∉ S → chapter03StageCoordinateType H S i = H i := by
    intro i hi
    simp [chapter03StageCoordinateType, hi]
  let forward : Chapter03Stage H S → Chapter03StageCoordinateProduct H S :=
    fun x i => by
      by_cases hi : i ∈ S
      · have htype := hmem i hi
        exact htype.symm ▸ ((x : ∀ i, G i) i)
      · have htype := hnotmem i hi
        exact htype.symm ▸
          (⟨((x : ∀ i, G i) i), x.property i hi⟩ : H i)
  let backward : Chapter03StageCoordinateProduct H S → Chapter03Stage H S :=
    fun y =>
      ⟨⟨fun i => by
          by_cases hi : i ∈ S
          · have htype := hmem i hi
            exact htype ▸ y i
          · have htype := hnotmem i hi
            exact ((htype ▸ y i : H i) : G i)
        , by
          filter_upwards [hS.compl_mem_cofinite] with i hi
          have hi' : i ∉ S := by simpa using hi
          have htype := hnotmem i hi'
          have hprop := (htype ▸ y i).property
          convert hprop using 1; simp [chapter03StageCoordinateType, hi']⟩,
        by
          intro i hi
          have hi' : i ∉ S := hi
          have htype := hnotmem i hi'
          have hprop := (htype ▸ y i).property
          convert hprop using 1; simp [chapter03StageCoordinateType, hi']⟩
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S <;>
      simp [forward, backward, eqRec_eq_cast, hi]
  · intro y
    funext i
    by_cases hi : i ∈ S <;>
      simp [forward, backward, eqRec_eq_cast, hi]

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
  simp only [chapter03ValuationRingUnitSubgroup, Subgroup.mem_map,
    Subgroup.mem_top, true_and]

end MultiplicativeRestrictedProducts

end
end LastLib.Book04AdelesAndIdeles.Chapter03
