import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Topology

/-! ## 2.2. Open subgroups of finite index -/

def Chapter02OpenFiniteIndexSubgroup
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (H : Subgroup Kˣ) : Prop :=
  IsOpen (H : Set Kˣ) ∧ Finite (Kˣ ⧸ H)

def Chapter02FiniteDiscreteQuotient
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (H : Subgroup Kˣ) [TopologicalSpace (Kˣ ⧸ H)] : Prop :=
  Finite (Kˣ ⧸ H) ∧ DiscreteTopology (Kˣ ⧸ H)

def chapter02QuotientProjection
    {K : Type*} [Field K] (H : Subgroup Kˣ) :
    Kˣ →* (Kˣ ⧸ H) :=
  QuotientGroup.mk' H

theorem chapter02_mem_value_unit_subgroup_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) (x : Kˣ) :
    x ∈ chapter02ValueUnitSubgroup v π m n ↔
      ∃ z : ℤ, ∃ u : chapter02FieldUnitFiltration v n,
        x = π ^ ((m : ℤ) * z) * (u : Kˣ) := by
  sorry

theorem chapter02_value_unit_subgroup_contains_deep_units
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) :
    chapter02FieldUnitFiltration v n ≤
      chapter02ValueUnitSubgroup v π m n := by
  intro u hu
  exact
    (le_sup_right :
      chapter02FieldUnitFiltration v n ≤
        chapter02ValueUnitSubgroup v π m n) hu

theorem chapter02_value_unit_subgroup_contains_value_powers
    {K : Type*} [Field K]
  (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) :
    Subgroup.zpowers (π ^ m) ≤ chapter02ValueUnitSubgroup v π m n := by
  exact le_sup_left

def Chapter02QuotientTopology
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H : Subgroup G) [TopologicalSpace (G ⧸ H)] : Prop :=
  ∀ s : Set (G ⧸ H),
    IsOpen s ↔ IsOpen ((QuotientGroup.mk' H) ⁻¹' s)

theorem chapter02_open_subgroup_iff_quotient_discrete
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (H : Subgroup G) [TopologicalSpace (G ⧸ H)]
    (hquotient : Chapter02QuotientTopology H) :
    IsOpen (H : Set G) ↔ DiscreteTopology (G ⧸ H) := by
  sorry

theorem proposition_2_1_open_finite_index_criterion
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hlocal : Chapter02LocalField v)
    [TopologicalSpace Kˣ]
    (hbasis : Chapter02FieldUnitFiltrationNeighborhoodBasis v)
    (π : Kˣ) (hπ : chapter02IsUniformizerUnit v π)
    (H : Subgroup Kˣ) [TopologicalSpace (Kˣ ⧸ H)]
    (hquotient : Chapter02QuotientTopology H) :
    (Chapter02OpenFiniteIndexSubgroup H ↔
      ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
        chapter02ValueUnitSubgroup v π m n ≤ H) ∧
      (Chapter02OpenFiniteIndexSubgroup H ↔
        Chapter02FiniteDiscreteQuotient H) := by
  sorry

theorem chapter02_finite_quotient_of_value_unit_neighborhood
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [TopologicalSpace Kˣ]
    (hbasis : Chapter02FieldUnitFiltrationNeighborhoodBasis v)
    (π : Kˣ) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (H : Subgroup Kˣ)
    (hH : chapter02ValueUnitSubgroup v π m n ≤ H)
    (hfinite : Finite (Kˣ ⧸ chapter02ValueUnitSubgroup v π m n)) :
    Chapter02OpenFiniteIndexSubgroup H := by
  sorry

theorem chapter02_finite_index_open_requires_continuity
    {G Q : Type*} [Group G] [Group Q]
    [TopologicalSpace G] [TopologicalSpace Q] (H : Subgroup G)
    [DiscreteTopology Q] (φ : G →* Q)
    (hker : MonoidHom.ker φ = H)
    (hcontinuous : Continuous φ) :
    IsOpen (H : Set G) := by
  sorry

/- A concrete profinite test object records why an abstract finite quotient is
   not enough: discontinuous finite-valued homomorphisms can have non-open
   kernels. -/
theorem chapter02_profinite_finite_index_need_not_be_open :
    ∃ H : Subgroup (Multiplicative (ℕ → ZMod 2)),
      Finite ((Multiplicative (ℕ → ZMod 2)) ⧸ H) ∧
        ¬IsOpen (H : Set (Multiplicative (ℕ → ZMod 2))) := by
  sorry

/- A dense proper subgroup of a Hausdorff compact group is not closed.  This
   is the topological obstruction behind the warning about algebraically
   generated candidates for norm groups. -/
theorem chapter02_dense_proper_subgroup_not_closed
    {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]
    (H : Subgroup G) (hdense : Dense (H : Set G)) (hproper : H ≠ ⊤) :
    ¬IsClosed (H : Set G) := by
  sorry

theorem chapter02_norm_candidate_with_dense_unit_part_not_closed
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [T2Space Kˣ]
    (H : Subgroup Kˣ) (hdense : Dense (H : Set Kˣ))
    (hproper : H ≠ ⊤) : ¬IsClosed (H : Set Kˣ) := by
  exact chapter02_dense_proper_subgroup_not_closed H hdense hproper

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
