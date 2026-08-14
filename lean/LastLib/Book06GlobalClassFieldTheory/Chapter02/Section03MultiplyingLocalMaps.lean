import LastLib.Book06GlobalClassFieldTheory.Chapter02.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u v w

/-! ## 2.3. Multiplying the local maps -/

/-- The finite-level global Artin map on ideles. -/
abbrev chapter02GlobalArtinMap
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) : chapter02Ideles D →* G :=
  chapter02GlobalArtinHom A

theorem chapter02_global_artin_product_is_finite
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) :
    chapter02GlobalArtinMap A x =
      Finset.prod (chapter02GlobalArtinIndexSet A x)
        (fun v => A.localArtin v (x.1 v)) :=
  rfl

theorem chapter02_global_artin_product_factors_are_trivial_off_finite_set
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) {v : V}
    (hv : v ∉ chapter02GlobalArtinIndexSet A x) :
    A.localArtin v (x.1 v) = 1 := by
  exact chapter02_global_artin_factor_eq_one_outside_index_set A x hv

theorem chapter02_global_artin_product_can_use_any_supporting_finset
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x : chapter02Ideles D) (S : Finset V)
    (hS : ∀ v : V, v ∉ S → A.localArtin v (x.1 v) = 1) :
    chapter02GlobalArtinMap A x = Finset.prod S (fun v => A.localArtin v (x.1 v)) := by
  exact chapter02_global_artin_eq_prod_of_contains_all_nontrivial_factors A x S hS

theorem chapter02_global_artin_adjacent_factors_commute
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v v' : V) (x : chapter02Ideles D) :
    A.localArtin v (x.1 v) * A.localArtin v' (x.1 v') =
      A.localArtin v' (x.1 v') * A.localArtin v (x.1 v) := by
  exact mul_comm _ _

theorem chapter02_global_artin_map_map_mul
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (x y : chapter02Ideles D) :
    chapter02GlobalArtinMap A (x * y) =
      chapter02GlobalArtinMap A x * chapter02GlobalArtinMap A y := by
  exact (chapter02GlobalArtinMap A).map_mul x y

/-
Continuity is deliberately a separate interface: the restricted-product
topology is supplied by the adelic chapter, while the local maps are the
continuous local reciprocity maps.
-/

theorem chapter02_global_artin_map_continuous
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G)
    [TopologicalSpace (chapter02Ideles D)] [TopologicalSpace G]
    [IsTopologicalGroup (chapter02Ideles D)] [IsTopologicalGroup G]
    [∀ x, TopologicalSpace (H x)]
    (T : Chapter02GlobalArtinTopologyData A) :
    Continuous (chapter02GlobalArtinMap A) :=
  chapter02_global_artin_continuous A T

theorem chapter02_global_artin_kernel_contains_standard_open_subgroup
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) :
    chapter02StandardArtinKernelSubgroup A ≤ (chapter02GlobalArtinMap A).ker := by
  exact chapter02_standard_artin_kernel_subgroup_le_kernel A

/-
No surjectivity field occurs in `Chapter02GlobalArtinData`: at this stage the
product map is only constructed and shown continuous.  Surjectivity belongs to
the finite global reciprocity theorem in the later chapter.
-/

/-- The global decomposition subgroup attached to a place. -/
def chapter02GlobalDecompositionGroup
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v : V) : Subgroup G :=
  A.decomposition v

/-- Complete splitting is triviality of the decomposition group. -/
def chapter02GlobalCompletelySplitAt
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v : V) : Prop :=
  chapter02GlobalDecompositionGroup A v = ⊥

theorem chapter02_global_completely_split_iff_decomposition_group_bot
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v : V) :
    chapter02GlobalCompletelySplitAt A v ↔
      chapter02GlobalDecompositionGroup A v = ⊥ :=
  Iff.rfl

theorem chapter02_global_local_factor_killed_at_completely_split_place
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v : V)
    (hv : chapter02GlobalCompletelySplitAt A v) (a : H v) :
    A.localArtin v a = 1 := by
  have ha : A.localArtin v a ∈ A.decomposition v := by
    rw [← A.local_artin_range v]
    exact ⟨a, rfl⟩
  change A.decomposition v = ⊥ at hv
  rw [hv] at ha
  exact ha

theorem chapter02_global_local_factor_is_trivial_iff_decomposition_group_trivial
    {V : Type u} {H : V → Type v} [∀ x, CommGroup (H x)]
    {G : Type w} [CommGroup G]
    {D : Chapter02RestrictedProductData V H}
    (A : Chapter02GlobalArtinData D G) (v : V) :
    (∀ a : H v, A.localArtin v a = 1) ↔
      chapter02GlobalDecompositionGroup A v = ⊥ := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter02
