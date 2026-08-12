import LastLib.Book04AdelesAndIdeles.Chapter03.Section01TheAlgebraicConstruction

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.2 The restricted-product topology -/

universe u v

section RestrictedTopology

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

theorem chapter03_basicProductCondition_inter
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (U V : ∀ i, Set (G i))
    (hU : chapter03BasicProductCondition H U)
    (hV : chapter03BasicProductCondition H V) :
    chapter03BasicProductCondition H (fun i => U i ∩ V i) := by
  sorry

theorem chapter03_basicProductSet_isOpen_of_condition
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (U : ∀ i, Set (G i))
    (hU : chapter03BasicProductCondition H U) :
    IsOpen (chapter03BasicProductSet H U) :=
  chapter03_basicProductSet_isOpen H U hU

/-- Left translates of basic products are the neighborhoods used in the
restricted-product basis. -/
def chapter03LeftTranslate
    (H : ∀ i, Subgroup (G i)) (a : Chapter03RestrictedProduct H)
    (s : Set (Chapter03RestrictedProduct H)) :
    Set (Chapter03RestrictedProduct H) :=
  {x | a⁻¹ * x ∈ s}

theorem chapter03_leftTranslate_mem_iff
    (H : ∀ i, Subgroup (G i)) (a : Chapter03RestrictedProduct H)
    (s : Set (Chapter03RestrictedProduct H))
    (x : Chapter03RestrictedProduct H) :
    x ∈ chapter03LeftTranslate H a s ↔ a⁻¹ * x ∈ s :=
  Iff.rfl

theorem chapter03_basicProduct_translates_form_basis
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    ∀ x : Chapter03RestrictedProduct H, ∀ s ∈ 𝓝 x,
      ∃ a : Chapter03RestrictedProduct H,
        ∃ U : ∀ i, Set (G i),
          chapter03BasicProductCondition H U ∧
            x ∈ chapter03LeftTranslate H a
              (chapter03BasicProductSet H U) ∧
            chapter03LeftTranslate H a
              (chapter03BasicProductSet H U) ⊆ s := by
  sorry

/-- The ordinary product topology on a stage, viewed through its coordinate
    map into the unrestricted dependent product. -/
@[instance_reducible]
def chapter03StageProductTopology
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    TopologicalSpace (Chapter03Stage H S) :=
  TopologicalSpace.induced
    (fun x : Chapter03Stage H S =>
      ((x : Chapter03Stage H S).1 : ∀ i, G i)) inferInstance

/-- The topology inherited by a stage from the restricted product topology. -/
@[instance_reducible]
def chapter03StageSubtypeTopology
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    TopologicalSpace (Chapter03Stage H S) :=
  TopologicalSpace.induced
    (fun x : Chapter03Stage H S => (x : Chapter03RestrictedProduct H))
    inferInstance

instance chapter03Stage.topologicalSpace
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (S : Set I) :
    TopologicalSpace (Chapter03Stage H S) :=
  chapter03StageSubtypeTopology H S

theorem chapter03_stage_subtype_topology_eq_product_topology
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) {S : Set I} (hS : S.Finite)
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    chapter03StageSubtypeTopology H S = chapter03StageProductTopology H S := by
  sorry

theorem chapter03_stage_is_open_subgroup
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) {S : Set I} (hS : S.Finite)
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsOpen (chapter03StageSubgroup H S : Set (Chapter03RestrictedProduct H)) :=
  chapter03_stage_isOpen H hS hH

theorem chapter03_restrictedProduct_is_topologicalGroup
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsTopologicalGroup (Chapter03RestrictedProduct H) := by
  sorry

theorem chapter03_additive_restrictedProduct_is_topologicalAddGroup
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsTopologicalAddGroup (Chapter03AdditiveRestrictedProduct H) := by
  sorry

theorem chapter03_additive_basicProductSet_isOpen
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i)) (U : ∀ i, Set (G i))
    (hU : chapter03AdditiveBasicProductCondition H U) :
    IsOpen (chapter03AdditiveBasicProductSet H U) := by
  sorry

theorem chapter03_mem_additiveBasicProductSet_iff
    {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (U : ∀ i, Set (G i))
    (x : Chapter03AdditiveRestrictedProduct H) :
    x ∈ chapter03AdditiveBasicProductSet H U ↔
      ∀ i, (x : ∀ i, G i) i ∈ U i :=
  Iff.rfl

theorem chapter03_additiveBasicProductSet_inter
    {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (U V : ∀ i, Set (G i)) :
    chapter03AdditiveBasicProductSet H U ∩
        chapter03AdditiveBasicProductSet H V =
      chapter03AdditiveBasicProductSet H (fun i => U i ∩ V i) := by
  ext x
  change
    ((∀ i, ((x : ∀ i, G i) i) ∈ U i) ∧
      (∀ i, ((x : ∀ i, G i) i) ∈ V i)) ↔
      ∀ i, ((x : ∀ i, G i) i) ∈ U i ∩ V i
  constructor
  · rintro ⟨hU, hV⟩ i
    exact ⟨hU i, hV i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem chapter03_restrictedProduct_topology_is_generated_by_basicProducts
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) :
    chapter03RestrictedProductTopology H =
      TopologicalSpace.generateFrom (chapter03BasicOpenSets H) :=
  rfl

/-- The restricted topology requires the distinguished subgroup at every
unmentioned coordinate; the unrestricted product topology does not. -/
theorem chapter03_restrictedTopology_differs_from_unrestricted_subspace
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i)))
    (hproper : chapter03InfinitelyManyProperDistinguishedSubgroups H) :
    chapter03RestrictedProductTopology H ≠
      chapter03UnrestrictedProductSubspaceTopology H :=
  chapter03_restrictedTopology_ne_subspaceTopology H hH hproper

end RestrictedTopology

end
end LastLib.Book04AdelesAndIdeles.Chapter03
