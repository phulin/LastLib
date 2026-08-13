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
    intro x y hx hy
    change (∑ v : InfinitePlace K, (x v + y v)) = 0
    change (∑ v : InfinitePlace K, x v = 0) at hx
    change (∑ v : InfinitePlace K, y v = 0) at hy
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change (∑ v : InfinitePlace K, ((c • x) v)) = 0
    change (∑ v : InfinitePlace K, x v = 0) at hx
    simp only [Pi.smul_apply]
    rw [← Finset.smul_sum, hx, smul_zero]

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
    apply Multiplicative.ext
    change chapter09InfiniteLogVector (1 : (Chapter09InfiniteAdele K)ˣ) = 0
    funext v
    unfold chapter09InfiniteLogVector
    have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
      (MulEquiv.piUnits).map_one
    rw [hpi]
    simp [chapter09NormUnit]
  map_mul' x y := by
    apply Multiplicative.ext
    change chapter09InfiniteLogVector (x * y) =
      chapter09InfiniteLogVector x + chapter09InfiniteLogVector y
    funext v
    unfold chapter09InfiniteLogVector
    have hpi : MulEquiv.piUnits (x * y) = MulEquiv.piUnits x * MulEquiv.piUnits y :=
      (MulEquiv.piUnits).map_mul x y
    rw [hpi]
    simp only [Pi.mul_apply]
    have hnorm : chapter09NormUnit ((MulEquiv.piUnits x) v *
        (MulEquiv.piUnits y) v) =
        chapter09NormUnit ((MulEquiv.piUnits x) v) *
          chapter09NormUnit ((MulEquiv.piUnits y) v) :=
      (chapter09NormUnitHom).map_mul _ _
    rw [hnorm, mul_pow]
    simp only [Units.val_mul, NNReal.coe_mul, Pi.add_apply]
    have hx0 : (((chapter09NormUnit ((MulEquiv.piUnits x) v) ^ v.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero _
        (Units.ne_zero (chapter09NormUnit ((MulEquiv.piUnits x) v)))
    have hy0 : (((chapter09NormUnit ((MulEquiv.piUnits y) v) ^ v.mult :
        Chapter09PositiveReal) : ℝ≥0) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero _
        (Units.ne_zero (chapter09NormUnit ((MulEquiv.piUnits y) v)))
    rw [Real.log_mul hx0 hy0]

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
    intro u v hu hv
    change ‖(u : ℝ)‖ = 1 at hu
    change ‖(v : ℝ)‖ = 1 at hv
    change ‖((u * v : ℝˣ) : ℝ)‖ = 1
    simp [Units.val_mul, hu, hv]
  inv_mem' := by
    intro u hu
    change ‖(u : ℝ)‖ = 1 at hu
    change ‖((u⁻¹ : ℝˣ) : ℝ)‖ = 1
    simp [norm_inv, hu]

def chapter09ComplexUnitCircle : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖(u : ℂ)‖ = 1 at hu
    change ‖(v : ℂ)‖ = 1 at hv
    change ‖((u * v : ℂˣ) : ℂ)‖ = 1
    simp [Units.val_mul, hu, hv]
  inv_mem' := by
    intro u hu
    change ‖(u : ℂ)‖ = 1 at hu
    change ‖((u⁻¹ : ℂˣ) : ℂ)‖ = 1
    simp [norm_inv, hu]

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
    change chapter09InfiniteLogVector (chapter09InfiniteUnitEmbedding K 1) = 0
    exact congrArg (fun z : Multiplicative (InfinitePlace K → ℝ) => z)
      ((chapter09InfiniteLogMap K).map_one)
  map_add' u v := by
    rw [toMul_add, (chapter09InfiniteUnitEmbedding K).map_mul]
    have h := (chapter09InfiniteLogMap K).map_mul
      (chapter09InfiniteUnitEmbedding K u.toMul)
      (chapter09InfiniteUnitEmbedding K v.toMul)
    exact congrArg (fun z : Multiplicative (InfinitePlace K → ℝ) => z) h

def chapter09GlobalUnitLogEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Additive ((𝓞 K)ˣ) →+ chapter09LogHyperplane K where
  toFun u := ⟨chapter09GlobalUnitLogEmbeddingRaw K u, by
    rw [chapter09LogHyperplane_mem_iff]
    change (∑ v : InfinitePlace K,
      Real.log ((((chapter09NormUnit
        ((MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult :
          Chapter09PositiveReal) : ℝ≥0) : ℝ))) = 0
    have hmodule := (chapter09ArchimedeanUnitEmbedding K u.toMul).property
    change chapter09InfiniteIdeleModule
      (chapter09InfiniteUnitEmbedding K u.toMul) = 1 at hmodule
    have hprod :
        (∏ v : InfinitePlace K,
          ((((chapter09NormUnit
            ((MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult :
              Chapter09PositiveReal) : ℝ≥0) : ℝ))) = 1 := by
      have h := congrArg (fun z : Chapter09PositiveReal => ((z : ℝ≥0) : ℝ)) hmodule
      simpa [chapter09InfiniteIdeleModule] using h
    rw [← Real.log_prod]
    · rw [hprod]
      simp
    · intro v hv
      exact_mod_cast Units.ne_zero
        (chapter09NormUnit
          ((MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u.toMul)) v) ^ v.mult)
  ⟩
  map_zero' := by
    apply Subtype.ext
    exact (chapter09GlobalUnitLogEmbeddingRaw K).map_zero
  map_add' u v := by
    apply Subtype.ext
    exact (chapter09GlobalUnitLogEmbeddingRaw K).map_add u v

theorem chapter09_global_unit_log_lies_in_hyperplane
    {K : Type*} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) :
    chapter09GlobalUnitLogEmbeddingRaw K (Additive.ofMul u) ∈
      chapter09LogHyperplane K := by
  exact (chapter09GlobalUnitLogEmbedding K (Additive.ofMul u)).property

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
  rw [chapter09UnitLogLattice, Submodule.mem_map]
  simp

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
