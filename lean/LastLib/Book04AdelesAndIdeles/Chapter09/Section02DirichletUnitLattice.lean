import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open scoped BigOperators NNReal

open NumberField IsDedekindDomain

/-!
## 9.2. Dirichlet's unit lattice
-/

def chapter09LogHyperplane
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℝ (InfinitePlace K → ℝ) where
  carrier := {t | ∑ v : InfinitePlace K, t v = 0}
  zero_mem' := by simp
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

theorem chapter09LogHyperplane_mem_iff
    {K : Type*} [Field K] [NumberField K] {t : InfinitePlace K → ℝ} :
    t ∈ chapter09LogHyperplane K ↔ ∑ v : InfinitePlace K, t v = 0 :=
  Iff.rfl

def chapter09InfiniteLogVector
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) : InfinitePlace K → ℝ :=
  fun v => Real.log
    (((chapter09NormUnit ((MulEquiv.piUnits x) v) ^ v.mult : Chapter09PositiveReal) :
      ℝ≥0) : ℝ)

def chapter09InfiniteLogMap
    (K : Type*) [Field K] [NumberField K] :
    (Chapter09InfiniteAdele K)ˣ →* Multiplicative (InfinitePlace K → ℝ) where
  toFun x := Multiplicative.ofAdd (chapter09InfiniteLogVector x)
  map_one' := by
    sorry
  map_mul' x y := by
    sorry

@[simp]
theorem chapter09InfiniteLogMap_apply
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) :
    chapter09InfiniteLogMap K x = Multiplicative.ofAdd (chapter09InfiniteLogVector x) :=
  rfl

def chapter09RealSignGroup : Subgroup ℝˣ where
  carrier := {u | ‖(u : ℝ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

def chapter09ComplexUnitCircle : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    sorry
  inv_mem' := by
    sorry

abbrev Chapter09ArchimedeanPhaseModel
    (K : Type*) [Field K] [NumberField K] :=
  ({w : InfinitePlace K // NumberField.InfinitePlace.IsReal w} →
      chapter09RealSignGroup) ×
    ({w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} →
      chapter09ComplexUnitCircle)

def chapter09InfiniteLogKernel
    (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter09InfiniteAdele K)ˣ :=
  (chapter09InfiniteLogMap K).ker

theorem chapter09_infinite_log_kernel_equiv_phase_model
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (chapter09InfiniteLogKernel K ≃*
      Chapter09ArchimedeanPhaseModel K) := by
  sorry

/-! The algebraic phase identification is also an identification of the
subgroup topologies; this is the form needed to transfer compactness. -/
theorem chapter09_infinite_log_kernel_continuous_equiv_phase_model
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (chapter09InfiniteLogKernel K ≃ₜ*
      Chapter09ArchimedeanPhaseModel K) := by
  sorry

theorem chapter09_infinite_log_kernel_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09InfiniteLogKernel K)) := by
  sorry

def chapter09GlobalUnitLogEmbeddingRaw
    (K : Type*) [Field K] [NumberField K] :
    Additive ((𝓞 K)ˣ) →+ (InfinitePlace K → ℝ) where
  toFun u := chapter09InfiniteLogVector (chapter09InfiniteUnitEmbedding K u.toMul)
  map_zero' := by
    sorry
  map_add' u v := by
    sorry

def chapter09GlobalUnitLogEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Additive ((𝓞 K)ˣ) →+ chapter09LogHyperplane K where
  toFun u := ⟨chapter09GlobalUnitLogEmbeddingRaw K u, by
    sorry⟩
  map_zero' := by
    sorry
  map_add' u v := by
    sorry

theorem chapter09_global_unit_log_lies_in_hyperplane
    {K : Type*} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) :
    chapter09GlobalUnitLogEmbeddingRaw K (Additive.ofMul u) ∈
      chapter09LogHyperplane K := by
  sorry

theorem chapter09_global_unit_log_kernel
    (K : Type*) [Field K] [NumberField K] :
    (chapter09GlobalUnitLogEmbeddingRaw K).ker =
      (NumberField.Units.torsion K).toAddSubgroup := by
  sorry

def chapter09UnitLogLattice
    (K : Type*) [Field K] [NumberField K] :
    Submodule ℤ (chapter09LogHyperplane K) :=
  Submodule.map (chapter09GlobalUnitLogEmbedding K).toIntLinearMap ⊤

theorem chapter09UnitLogLattice_mem_iff
    {K : Type*} [Field K] [NumberField K]
    {t : chapter09LogHyperplane K} :
    t ∈ chapter09UnitLogLattice K ↔
      ∃ u : Additive ((𝓞 K)ˣ), chapter09GlobalUnitLogEmbedding K u = t := by
  sorry

theorem chapter09UnitLogLattice_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter09UnitLogLattice K) := by
  sorry

attribute [instance] chapter09UnitLogLattice_discrete

theorem chapter09UnitLogLattice_span_eq_top
    (K : Type*) [Field K] [NumberField K] :
    Submodule.span ℝ (chapter09UnitLogLattice K : Set (chapter09LogHyperplane K)) = ⊤ := by
  sorry

theorem chapter09UnitLogLattice_is_full_lattice
    (K : Type*) [Field K] [NumberField K] :
    IsZLattice ℝ (chapter09UnitLogLattice K) := by
  exact ⟨chapter09UnitLogLattice_span_eq_top K⟩

/- This is the bounded fundamental-region interface extracted from the
Minkowski argument: every logarithmic vector is reduced by a global unit into
one fixed bounded, hence compact, region. -/
theorem chapter09_unit_log_reduction
    (K : Type*) [Field K] [NumberField K] :
    ∃ B : Set (chapter09LogHyperplane K), IsCompact B ∧
      ∀ t : chapter09LogHyperplane K, ∃ u : Additive ((𝓞 K)ˣ),
        t - chapter09GlobalUnitLogEmbedding K u ∈ B := by
  sorry

theorem chapter09_unit_log_lattice_is_discrete_and_cocompact
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter09UnitLogLattice K) ∧
      ∃ B : Set (chapter09LogHyperplane K), IsCompact B ∧
        ∀ t : chapter09LogHyperplane K, ∃ u : Additive ((𝓞 K)ˣ),
          t - chapter09GlobalUnitLogEmbedding K u ∈ B := by
  exact ⟨chapter09UnitLogLattice_discrete K, chapter09_unit_log_reduction K⟩

theorem chapter09_unit_rank_eq_card_infinite_places_sub_one
    (K : Type*) [Field K] [NumberField K] :
    NumberField.Units.rank K = Fintype.card (InfinitePlace K) - 1 := by
  rfl

/- The structure theorem in the source is intentionally noncanonical. -/
theorem chapter09_dirichlet_unit_theorem
    (K : Type*) [Field K] [NumberField K] :
    Nonempty ((𝓞 K)ˣ ≃*
      (NumberField.Units.torsion K) ×
        Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) := by
  sorry

theorem chapter09_dirichlet_unit_theorem_kernel_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (NumberField.Units.torsion K) := by
  infer_instance

end

end LastLib.Book04AdelesAndIdeles.Chapter09
