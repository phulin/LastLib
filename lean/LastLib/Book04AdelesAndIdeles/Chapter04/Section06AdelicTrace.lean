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
  finiteTrace_on_principal :
    ∀ (v : Chapter04FinitePlace K) (a : L),
      finiteTrace v (fun w => (a : Chapter04FiniteLocalField L w.1)) =
        (Algebra.trace K L a : Chapter04FiniteLocalField K v)
  finiteTrace_continuous :
    ∀ v : Chapter04FinitePlace K, Continuous (finiteTrace v)
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
  infiniteTrace_on_principal :
    ∀ (v : Chapter04InfinitePlace K) (a : L),
      infiniteTrace v (fun w => (a : w.1.Completion)) =
        (Algebra.trace K L a : v.Completion)
  infiniteTrace_continuous :
    ∀ v : Chapter04InfinitePlace K, Continuous (infiniteTrace v)
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
        let bad : Set (Chapter04FinitePlace L) :=
          chapter04FiniteAdeleExceptionalSet L y.2
        let base : Chapter04FinitePlace L → Chapter04FinitePlace K := fun w =>
          { asIdeal := Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
            isPrime := Ideal.comap_isPrime _ _
            ne_bot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) w.ne_bot }
        have hbad : bad.Finite := by
          exact chapter04_finiteAdele_exceptionalSet_finite L y.2
        have hbase : (base '' bad).Finite := hbad.image base
        filter_upwards [D.finiteTrace_preserves_integral, hbase.compl_mem_cofinite]
          with v htrace hv
        apply htrace
        intro w
        by_contra hw
        have hwbad : w.1 ∈ bad := by
          simpa [bad, chapter04FiniteAdeleExceptionalSet] using hw
        have hbasew : base w.1 = v := by
          dsimp [base]
          apply HeightOneSpectrum.ext
          exact w.2
        apply hv
        exact ⟨w.1, hwbad, hbasew⟩⟩)
  map_zero' := by
    apply chapter04_adeleRing_ext K
    · funext v
      change D.infiniteTrace v (fun _ => 0) = 0
      exact (D.infiniteTrace v).map_zero
    · apply Subtype.ext
      funext v
      change D.finiteTrace v (fun _ => 0) = 0
      exact (D.finiteTrace v).map_zero
  map_add' x y := by
    apply chapter04_adeleRing_ext K
    · funext v
      change D.infiniteTrace v (fun w => x.1 w.1 + y.1 w.1) =
        D.infiniteTrace v (fun w => x.1 w.1) + D.infiniteTrace v (fun w => y.1 w.1)
      exact (D.infiniteTrace v).map_add _ _
    · apply Subtype.ext
      funext v
      change D.finiteTrace v (fun w => x.2 w.1 + y.2 w.1) =
        D.finiteTrace v (fun w => x.2 w.1) + D.finiteTrace v (fun w => y.2 w.1)
      exact (D.finiteTrace v).map_add _ _

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
  classical
  let finiteMap : Chapter04FiniteAdeleRing L → Chapter04FiniteAdeleRing K := fun x =>
    (chapter04AdelicTrace D ((0 : Chapter04InfiniteAdeleRing L), x)).2
  have hfinite : Continuous finiteMap := by
    apply (RestrictedProduct.continuous_dom (f := finiteMap)).2
    intro S hS
    have hSc : Sᶜ.Finite :=
      Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
    let bad : Set (Chapter04FinitePlace L) := Sᶜ
    let base : Chapter04FinitePlace L → Chapter04FinitePlace K := fun w =>
      { asIdeal := Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
        isPrime := Ideal.comap_isPrime _ _
        ne_bot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) w.ne_bot }
    let good : Set (Chapter04FinitePlace K) :=
      {v | ∀ x : ∀ w : Chapter04FinitePlaceAbove K L v,
        Chapter04FiniteLocalField L w.1,
        (∀ w, x w ∈ chapter04FiniteLocalIntegerSet L w.1) →
          D.finiteTrace v x ∈ chapter04FiniteLocalIntegerSet K v}
    have hgood : goodᶜ.Finite := by
      refine (Filter.eventually_cofinite.mp D.finiteTrace_preserves_integral).subset ?_
      intro v hv
      change v ∉ good
      intro hgv
      apply hv
      intro x hx
      exact hgv x hx
    let T : Set (Chapter04FinitePlace K) :=
      {v | (∀ w : Chapter04FinitePlaceAbove K L v, w.1 ∈ S) ∧ v ∈ good}
    have hTc : Tᶜ.Finite := by
      refine ((hSc.image base).union hgood).subset ?_
      intro v hv
      by_cases hforall : ∀ w : Chapter04FinitePlaceAbove K L v, w.1 ∈ S
      · right
        intro hgoodv
        apply hv
        exact ⟨hforall, hgoodv⟩
      · left
        rcases not_forall.mp hforall with ⟨w, hw⟩
        have hbasew : base w.1 = v := by
          dsimp [base]
          apply HeightOneSpectrum.ext
          exact w.2
        exact ⟨w.1, hw, hbasew⟩
    have hT : Filter.cofinite ≤ Filter.principal T :=
      Filter.le_principal_iff.mpr (Filter.mem_cofinite.mpr hTc)
    let gS :
        (Πʳ w : Chapter04FinitePlace L,
          [Chapter04FiniteLocalField L w,
            chapter04FiniteLocalIntegerSet L w]_[Filter.principal S]) →
        (Πʳ v : Chapter04FinitePlace K,
          [Chapter04FiniteLocalField K v,
            chapter04FiniteLocalIntegerSet K v]_[Filter.principal T]) := fun z =>
      ⟨fun v => D.finiteTrace v (fun w => z.1 w.1), by
        filter_upwards [Filter.eventually_principal.mpr (fun v hv => hv)] with v hv
        apply hv.2
        intro w
        exact Filter.eventually_principal.mp z.2 w.1 (hv.1 w)⟩
    have hgS : Continuous gS := by
      apply RestrictedProduct.continuous_rng_of_principal.mpr
      apply continuous_pi
      intro v
      change Continuous (fun z :
        (Πʳ w : Chapter04FinitePlace L,
          [Chapter04FiniteLocalField L w,
            chapter04FiniteLocalIntegerSet L w]_[Filter.principal S]) =>
        D.finiteTrace v (fun w => z.1 w.1))
      apply (D.finiteTrace_continuous v).comp
      exact continuous_pi fun w =>
        RestrictedProduct.continuous_eval (𝓕 := Filter.principal S) w.1
    have hfactor :
        finiteMap ∘ RestrictedProduct.inclusion
            (fun w : Chapter04FinitePlace L => Chapter04FiniteLocalField L w)
            (fun w : Chapter04FinitePlace L =>
              (chapter04FiniteLocalIntegerSet L w : Set (Chapter04FiniteLocalField L w))) hS =
          RestrictedProduct.inclusion
              (fun v : Chapter04FinitePlace K => Chapter04FiniteLocalField K v)
              (fun v : Chapter04FinitePlace K =>
                (chapter04FiniteLocalIntegerSet K v : Set (Chapter04FiniteLocalField K v))) hT ∘ gS := by
      funext z
      apply RestrictedProduct.ext
      intro v
      rfl
    change Continuous (finiteMap ∘ RestrictedProduct.inclusion
      (fun w : Chapter04FinitePlace L => Chapter04FiniteLocalField L w)
      (fun w : Chapter04FinitePlace L =>
        (chapter04FiniteLocalIntegerSet L w : Set (Chapter04FiniteLocalField L w))) hS)
    rw [hfactor]
    exact (RestrictedProduct.continuous_inclusion hT).comp hgS
  have hinfinite : Continuous
      (fun y : Chapter04AdeleRing L =>
        fun v : Chapter04InfinitePlace K =>
          D.infiniteTrace v (fun w => y.1 w.1)) := by
    apply continuous_pi
    intro v
    apply (D.infiniteTrace_continuous v).comp
    exact continuous_pi fun w => (continuous_apply w.1).comp continuous_fst
  have hfinite' : Continuous (fun y : Chapter04AdeleRing L => finiteMap y.2) :=
    hfinite.comp continuous_snd
  let F : Chapter04AdeleRing L → Chapter04AdeleRing K := fun y =>
    (fun v : Chapter04InfinitePlace K =>
        D.infiniteTrace v (fun w => y.1 w.1),
      finiteMap y.2)
  have hF : Continuous F := hinfinite.prodMk hfinite'
  have hEq : (chapter04AdelicTrace D : Chapter04AdeleRing L → Chapter04AdeleRing K) = F := by
    funext y
    apply chapter04_adeleRing_ext K
    · rfl
    · apply Subtype.ext
      funext v
      rfl
  rw [hEq]
  exact hF

def chapter04AdeleBaseScalarMap
    (e : L ⊗[K] Chapter04AdeleRing K ≃ₐ[K] Chapter04AdeleRing L) :
    Chapter04AdeleRing K →+* Chapter04AdeleRing L :=
  (e.toAlgHom.comp (Algebra.TensorProduct.includeRight :
    Chapter04AdeleRing K →ₐ[K] L ⊗[K] Chapter04AdeleRing K)).toRingHom

theorem chapter04_adelic_trace_is_linear_over_the_base_adele_ring
    (D : Chapter04AdelicTraceData K L) :
    ∃ e : L ⊗[K] Chapter04AdeleRing K ≃ₐ[K] Chapter04AdeleRing L,
      ∀ (a : Chapter04AdeleRing K) (y : Chapter04AdeleRing L),
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
