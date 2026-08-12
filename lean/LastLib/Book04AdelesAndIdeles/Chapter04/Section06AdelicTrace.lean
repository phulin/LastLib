import LastLib.Book04AdelesAndIdeles.Chapter04.Section04ScalarExtension

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators TensorProduct Topology RestrictedProduct

/-! ### 4.6 Adelic trace -/

abbrev Chapter04InfinitePlaceAbove
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (v : Chapter04InfinitePlace K) :=
  {w : Chapter04InfinitePlace L // w.LiesOver v}

structure Chapter04AdelicTraceData
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] where
  finiteTrace :
    ∀ v : Chapter04FinitePlace K,
      (∀ w : Chapter04FinitePlaceAbove K L v,
        Chapter04FiniteLocalField L w.1) →+
          Chapter04FiniteLocalField K v
  finiteBranchFintype :
    ∀ v : Chapter04FinitePlace K,
      Fintype (Chapter04FinitePlaceAbove K L v)
  finiteBranchTrace :
    ∀ (v : Chapter04FinitePlace K)
      (w : Chapter04FinitePlaceAbove K L v),
      Chapter04FiniteLocalField L w.1 →+
        Chapter04FiniteLocalField K v
  finiteTrace_eq_sum :
    ∀ (v : Chapter04FinitePlace K)
      (x : ∀ w : Chapter04FinitePlaceAbove K L v,
        Chapter04FiniteLocalField L w.1),
      finiteTrace v x =
        letI := finiteBranchFintype v
        ∑ w, finiteBranchTrace v w (x w)
  infiniteTrace :
    ∀ v : Chapter04InfinitePlace K,
      (∀ w : Chapter04InfinitePlaceAbove K L v,
        w.1.Completion) →+ v.Completion
  infiniteBranchFintype :
    ∀ v : Chapter04InfinitePlace K,
      Fintype (Chapter04InfinitePlaceAbove K L v)
  infiniteBranchTrace :
    ∀ (v : Chapter04InfinitePlace K)
      (w : Chapter04InfinitePlaceAbove K L v),
      w.1.Completion →+ v.Completion
  infiniteTrace_eq_sum :
    ∀ (v : Chapter04InfinitePlace K)
      (x : ∀ w : Chapter04InfinitePlaceAbove K L v, w.1.Completion),
      infiniteTrace v x =
        letI := infiniteBranchFintype v
        ∑ w, infiniteBranchTrace v w (x w)
  finiteTrace_preserves_integral :
    ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite,
      ∀ x : ∀ w : Chapter04FinitePlaceAbove K L v,
        Chapter04FiniteLocalField L w.1,
        (∀ w, x w ∈ chapter04FiniteLocalIntegerSet L w.1) →
          finiteTrace v x ∈ chapter04FiniteLocalIntegerSet K v

/- LOCAL_DEPENDENCY_GUESS: the canonical local completed-field trace maps and
their almost-everywhere integrality preservation are expected from the local
extension interfaces; the structure above keeps those inputs separate from
the global adelic trace conclusion. -/
theorem chapter04_adelic_trace_data_exists
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] :
    Nonempty (Chapter04AdelicTraceData K L) := by
  sorry

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L]

def chapter04AdelicTrace
    (D : Chapter04AdelicTraceData K L) :
    Chapter04AdeleRing L →+ Chapter04AdeleRing K where
  toFun y :=
    (fun v => D.infiniteTrace v (fun w => y.1 w.1),
      ⟨fun v => D.finiteTrace v (fun w => y.2 w.1), by
        sorry⟩)
  map_zero' := by
    sorry
  map_add' x y := by
    sorry

theorem chapter04AdelicTrace_apply_infinite
    (D : Chapter04AdelicTraceData K L)
    (y : Chapter04AdeleRing L) (v : Chapter04InfinitePlace K) :
    (chapter04AdelicTrace D y).1 v =
      D.infiniteTrace v (fun w => y.1 w.1) := by
  rfl

theorem chapter04AdelicTrace_apply_finite
    (D : Chapter04AdelicTraceData K L)
    (y : Chapter04AdeleRing L) (v : Chapter04FinitePlace K) :
    (chapter04AdelicTrace D y).2 v =
      D.finiteTrace v (fun w => y.2 w.1) := by
  rfl

theorem chapter04AdelicTrace_apply_infinite_as_sum_over_branches
    (D : Chapter04AdelicTraceData K L)
    (y : Chapter04AdeleRing L) (v : Chapter04InfinitePlace K) :
    (chapter04AdelicTrace D y).1 v =
      letI := D.infiniteBranchFintype v
      ∑ w, D.infiniteBranchTrace v w (y.1 w.1) := by
  change D.infiniteTrace v (fun w => y.1 w.1) = _
  exact D.infiniteTrace_eq_sum v (fun w => y.1 w.1)

theorem chapter04AdelicTrace_apply_finite_as_sum_over_branches
    (D : Chapter04AdelicTraceData K L)
    (y : Chapter04AdeleRing L) (v : Chapter04FinitePlace K) :
    (chapter04AdelicTrace D y).2 v =
      letI := D.finiteBranchFintype v
      ∑ w, D.finiteBranchTrace v w (y.2 w.1) := by
  change D.finiteTrace v (fun w => y.2 w.1) = _
  exact D.finiteTrace_eq_sum v (fun w => y.2 w.1)

theorem chapter04_adelic_trace_is_continuous
    (D : Chapter04AdelicTraceData K L) :
    Continuous (chapter04AdelicTrace D) := by
  sorry

def chapter04AdeleBaseScalarMap
    (e : L ⊗[K] Chapter04AdeleRing K ≃ₐ[K] Chapter04AdeleRing L) :
    Chapter04AdeleRing K →+* Chapter04AdeleRing L :=
  (e.toAlgHom.comp (Algebra.TensorProduct.includeRight :
    Chapter04AdeleRing K →ₐ[K] L ⊗[K] Chapter04AdeleRing K)).toRingHom

theorem chapter04_adelic_trace_is_linear_over_the_base_adele_ring
    (D : Chapter04AdelicTraceData K L)
    (e : L ⊗[K] Chapter04AdeleRing K ≃ₐ[K] Chapter04AdeleRing L)
    (a : Chapter04AdeleRing K) (y : Chapter04AdeleRing L) :
    chapter04AdelicTrace D (chapter04AdeleBaseScalarMap e a * y) =
      a * chapter04AdelicTrace D y := by
  sorry

theorem chapter04_adelic_trace_on_principal_adeles
    (D : Chapter04AdelicTraceData K L) (a : L) :
    chapter04AdelicTrace D (algebraMap L (Chapter04AdeleRing L) a) =
      algebraMap K (Chapter04AdeleRing K) (Algebra.trace K L a) := by
  sorry

def chapter04IntegralLocalTraceSurjective
    (D : Chapter04AdelicTraceData K L) (v : Chapter04FinitePlace K) : Prop :=
  ∀ y : Chapter04FiniteLocalIntegerRing K v,
    ∃ x : ∀ w : Chapter04FinitePlaceAbove K L v,
      Chapter04FiniteLocalIntegerRing L w.1,
      D.finiteTrace v (fun w =>
        (x w : Chapter04FiniteLocalField L w.1)) = y

def chapter04GlobalTracePairingNondegenerate
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∀ x : L, (∀ y : L, Algebra.trace K L (x * y) = 0) → x = 0

theorem chapter04_global_trace_pairing_is_nondegenerate
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsScalarTower ℚ K L] :
    chapter04GlobalTracePairingNondegenerate K L := by
  sorry

def chapter04TraceHasANontrivialKernel
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  ∃ x : L, x ≠ 0 ∧ Algebra.trace K L x = 0

theorem chapter04_trace_can_annihilate_nonzero_elements
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (hdegree : 1 < Module.finrank K L) :
    chapter04TraceHasANontrivialKernel K L := by
  sorry

/- The field-level trace pairing and integral trace surjectivity are kept as
separate predicates: ramification may obstruct the latter even when the former
is nondegenerate. -/
def chapter04TraceIntegralityFailureAtRamifiedPlace
    (D : Chapter04AdelicTraceData K L) : Prop :=
  ∃ v : Chapter04FinitePlace K,
    ¬ chapter04FiniteExtensionUnramifiedAt K L v ∧
      ¬ chapter04IntegralLocalTraceSurjective D v

def chapter04FiniteAlgebraTrace
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : A) : K :=
  Algebra.trace K A x

def chapter04FiniteAlgebraNorm
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : A) : K :=
  Algebra.norm K x

theorem chapter04_trace_is_trace_of_multiplication
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : A) :
    chapter04FiniteAlgebraTrace K A x =
      LinearMap.trace K A (Algebra.lmul K A x) := by
  rfl

theorem chapter04_norm_is_determinant_of_multiplication
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : A) :
    chapter04FiniteAlgebraNorm K A x =
      LinearMap.det (Algebra.lmul K A x) := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the restriction maps from the branches of a tower
of completions are not yet exposed by the earlier chapter APIs. The following
data records those local restriction maps and their local trace compatibility;
the global transitivity statement then does not assume the desired global map
equality as a premise. -/
structure Chapter04AdelicTraceTowerLocalData
    (K L M : Type*) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [FiniteDimensional K M] [IsScalarTower ℚ K L]
    [IsScalarTower ℚ L M] [IsScalarTower ℚ K M]
    [IsScalarTower K L M] where
  baseTrace : Chapter04AdelicTraceData K L
  upperTrace : Chapter04AdelicTraceData L M
  compositeTrace : Chapter04AdelicTraceData K M
  finiteRestrictionIndex :
    ∀ (v : Chapter04FinitePlace K)
      (u : Chapter04FinitePlaceAbove K L v)
      (_z : Chapter04FinitePlaceAbove L M u.1),
      Chapter04FinitePlaceAbove K M v
  finiteRestrictionIndex_underlying_eq :
    ∀ (v : Chapter04FinitePlace K)
      (u : Chapter04FinitePlaceAbove K L v)
      (z : Chapter04FinitePlaceAbove L M u.1),
      (finiteRestrictionIndex v u z).1 = z.1
  infiniteRestrictionIndex :
    ∀ (v : Chapter04InfinitePlace K)
      (u : Chapter04InfinitePlaceAbove K L v)
      (_z : Chapter04InfinitePlaceAbove L M u.1),
      Chapter04InfinitePlaceAbove K M v
  infiniteRestrictionIndex_underlying_eq :
    ∀ (v : Chapter04InfinitePlace K)
      (u : Chapter04InfinitePlaceAbove K L v)
      (z : Chapter04InfinitePlaceAbove L M u.1),
      (infiniteRestrictionIndex v u z).1 = z.1
  finite_trace_is_locally_transitive :
    ∀ (v : Chapter04FinitePlace K)
      (y : ∀ m : Chapter04FinitePlaceAbove K M v,
        Chapter04FiniteLocalField M m.1),
      compositeTrace.finiteTrace v y =
        baseTrace.finiteTrace v (fun u =>
          upperTrace.finiteTrace u.1 (fun z =>
            finiteRestrictionIndex_underlying_eq v u z ▸
              y (finiteRestrictionIndex v u z)))
  infinite_trace_is_locally_transitive :
    ∀ (v : Chapter04InfinitePlace K)
      (y : ∀ m : Chapter04InfinitePlaceAbove K M v,
        m.1.Completion),
      compositeTrace.infiniteTrace v y =
        baseTrace.infiniteTrace v (fun u =>
          upperTrace.infiniteTrace u.1 (fun z =>
            infiniteRestrictionIndex_underlying_eq v u z ▸
              y (infiniteRestrictionIndex v u z)))

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra L M] [Algebra K M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
  [IsScalarTower ℚ K L] [IsScalarTower ℚ L M] [IsScalarTower ℚ K M]
  [IsScalarTower K L M]

theorem chapter04_adelic_trace_is_transitive_in_towers
    (T : Chapter04AdelicTraceTowerLocalData K L M) :
    chapter04AdelicTrace T.compositeTrace =
      (chapter04AdelicTrace T.baseTrace).comp
        (chapter04AdelicTrace T.upperTrace) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
