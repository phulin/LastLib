import LastLib.Book04AdelesAndIdeles.Chapter05.Section01TheDiagonalEmbedding
import LastLib.Book04AdelesAndIdeles.Chapter01.Section03ArchimedeanEmbeddings
import LastLib.Book04AdelesAndIdeles.Chapter04.Section02TheFullAdeleRing

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open scoped Topology

/-! ## 5.3. Discreteness in the full adeles -/

theorem chapter05_finite_integral_is_compact_open
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Chapter04FiniteIntegralAdeleSubring K :
      Set (Chapter04FiniteAdeleRing K)) ∧
      IsOpen (Chapter04FiniteIntegralAdeleSubring K :
        Set (Chapter04FiniteAdeleRing K)) := by
  exact chapter04_finiteIntegralAdele_is_compact_open K

private theorem chapter05_nonzero_mem_of_open_infinite_completion
    (K : Type*) [Field K] [NumberField K]
    (w : Chapter04InfinitePlace K) (V : Set w.Completion)
    (hV : IsOpen V) (h0 : (0 : w.Completion) ∈ V) :
    ∃ y : w.Completion, y ∈ V ∧ y ≠ 0 := by
  rcases Metric.mem_nhds_iff.mp (hV.mem_nhds h0) with ⟨ε, hε, hεV⟩
  rcases w.isReal_or_isComplex with hw | hw
  · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    have he0 : e (0 : w.Completion) = 0 := by
      change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw 0 = 0
      simp
    let y : w.Completion := e.symm (ε / 2)
    have hyball : y ∈ Metric.ball (0 : w.Completion) ε := by
      rw [Metric.mem_ball]
      calc
        dist y 0 = dist (e y) (e 0) := (e.dist_eq y 0).symm
        _ = ε / 2 := by
          have hε0 : 0 ≤ ε := hε.le
          simp [y, he0, hε0]
        _ < ε := by linarith
    refine ⟨y, hεV hyball, ?_⟩
    intro hy
    have hzero : (ε / 2 : ℝ) = 0 := by
      have h := congrArg e hy
      simpa [y, he0] using h
    linarith
  · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
    have he0 : e (0 : w.Completion) = 0 := by
      change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw 0 = 0
      simp
    let y : w.Completion := e.symm ((ε / 2 : ℝ) : ℂ)
    have hyball : y ∈ Metric.ball (0 : w.Completion) ε := by
      rw [Metric.mem_ball]
      calc
        dist y 0 = dist (e y) (e 0) := (e.dist_eq y 0).symm
        _ = ε / 2 := by
          have hε0 : 0 ≤ ε := hε.le
          simp [y, he0, hε0]
        _ < ε := by linarith
    refine ⟨y, hεV hyball, ?_⟩
    intro hy
    have hzero : ((ε / 2 : ℝ) : ℂ) = 0 := by
      have h := congrArg e hy
      simpa [y, he0] using h
    have hzero' : ε / 2 = 0 := Complex.ofReal_eq_zero.mp hzero
    linarith

theorem chapter05_exists_small_archimedean_neighborhood
    (K : Type*) [Field K] [NumberField K] :
    ∃ Uinf : Set (chapter01MinkowskiSpace K),
      IsOpen Uinf ∧ Uinf ∈ 𝓝 (0 : chapter01MinkowskiSpace K) ∧
        Uinf ∩ (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) =
          {0} := by
  rcases (discreteTopology_subtype_iff'.mp (chapter01_integer_lattice_is_discrete K))
      (0 : chapter01MinkowskiSpace K) (by simp) with ⟨Uinf, hUinf, hEq⟩
  refine ⟨Uinf, hUinf, ?_, hEq⟩
  have hzero : (0 : chapter01MinkowskiSpace K) ∈ Uinf ∩
      (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) := by
    rw [hEq]
    simp
  exact hUinf.mem_nhds hzero.1

theorem chapter05_full_adele_is_nondiscrete_at_zero
    (K : Type*) [Field K] [NumberField K] :
    chapter05NondiscreteAtZero (G := Chapter04AdeleRing K) := by
  classical
  rw [chapter05NondiscreteAtZero]
  intro hzero
  rcases chapter04_full_adele_has_local_specification_basis K
      (0 : Chapter04AdeleRing K) ({0} : Set (Chapter04AdeleRing K)) hzero with
    ⟨S, U, hS, hmem, hsub⟩
  have hmem' := (chapter04_mem_fullBasicOpen_iff K S U
      (0 : Chapter04AdeleRing K)).mp hmem
  have hzero_local (v : Chapter04Place K) (hv : v ∈ S) :
      (0 : chapter04LocalField K v) ∈ U v := by
    cases v with
    | inl v =>
        have h := hmem'.1 (Sum.inl v) hv
        change (0 : Chapter04FiniteLocalField K v) ∈ U (Sum.inl v) at h
        exact h
    | inr v =>
        have h := hmem'.1 (Sum.inr v) hv
        change (0 : v.Completion) ∈ U (Sum.inr v) at h
        exact h
  let w₀ : Chapter04InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (Chapter04InfinitePlace K))
  obtain ⟨y, hyU, hyne⟩ :=
    chapter05_nonzero_mem_of_open_infinite_completion K w₀ (U (Sum.inr w₀))
      (hS.2.1 (Sum.inr w₀) (hS.2.2 w₀))
      (hzero_local (Sum.inr w₀) (hS.2.2 w₀))
  let zInf : Chapter04InfiniteAdeleRing K :=
    Function.update (fun w : Chapter04InfinitePlace K => (0 : w.Completion)) w₀ y
  let z : Chapter04AdeleRing K := (zInf, 0)
  have hz : z ∈ chapter04FullBasicOpen K S U := by
    rw [chapter04_mem_fullBasicOpen_iff]
    constructor
    · intro v hv
      cases v with
      | inl v =>
          dsimp [chapter04AdeleCoordinate, z, zInf, chapter04LocalField]
          change (0 : Chapter04FiniteLocalField K v) ∈ U (Sum.inl v)
          exact hzero_local (Sum.inl v) hv
      | inr w =>
          by_cases hww : w = w₀
          · subst w
            dsimp [chapter04AdeleCoordinate, z, zInf, chapter04LocalField]
            rw [Function.update_self]
            exact hyU
          · dsimp [chapter04AdeleCoordinate, z, zInf, chapter04LocalField]
            change (Function.update
              (fun w : Chapter04InfinitePlace K => (0 : w.Completion)) w₀ y) w ∈
              U (Sum.inr w)
            rw [Function.update_of_ne hww]
            exact hzero_local (Sum.inr w) hv
    · intro v _
      change (0 : v.adicCompletion K) ∈ v.adicCompletionIntegers K
      exact ValuationSubring.zero_mem _
  have hz0 : z = 0 := by
    have : z ∈ ({0} : Set (Chapter04AdeleRing K)) := hsub hz
    simpa using this
  have hy0 : y = 0 := by
    have hcoord := congrArg (fun a : Chapter04AdeleRing K => a.1 w₀) hz0
    change (Function.update (fun w : Chapter04InfinitePlace K => (0 : w.Completion)) w₀ y) w₀ =
      0 at hcoord
    rw [Function.update_self] at hcoord
    exact hcoord
  exact hyne hy0

theorem chapter05_full_zero_neighborhood_is_open
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (chapter01MinkowskiSpace K)) (hUinf : IsOpen Uinf) :
    IsOpen (chapter05FullZeroNeighborhood K Uinf) := by
  classical
  change IsOpen
    (((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' Uinf) ×ˢ
      (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)))
  have hcont : Continuous
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K :
        Chapter04InfiniteAdeleRing K → chapter01MinkowskiSpace K) := by
    let e : Chapter04InfiniteAdeleRing K ≃ₜ chapter01MinkowskiSpace K :=
      (Homeomorph.piEquivPiSubtypeProd
          (fun (v : NumberField.InfinitePlace K) =>
            NumberField.InfinitePlace.IsReal v)
          (fun (v : NumberField.InfinitePlace K) => v.Completion)).trans
        (Homeomorph.prodCongr
          (Homeomorph.piCongrRight
            (fun w : {w : NumberField.InfinitePlace K //
                NumberField.InfinitePlace.IsReal w} =>
              (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
                w.2).toHomeomorph))
          ((Homeomorph.piCongrRight
              (fun w : {w : NumberField.InfinitePlace K //
                  ¬ NumberField.InfinitePlace.IsReal w} =>
                (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
                  (NumberField.InfinitePlace.not_isReal_iff_isComplex.1 w.2)).toHomeomorph)).trans
            (Homeomorph.piCongrLeft
              (Y := fun _ : {w : NumberField.InfinitePlace K //
                  NumberField.InfinitePlace.IsComplex w} => ℂ)
              (Equiv.subtypeEquivRight
                (fun _ => NumberField.InfinitePlace.not_isReal_iff_isComplex)))))
    exact e.continuous
  have hInf : IsOpen
      ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' Uinf) := by
    have hset :
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' Uinf =
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K) ⁻¹' Uinf := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x, hx,
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply x⟩
    rw [hset]
    exact hUinf.preimage hcont
  exact hInf.prod (chapter05_finite_integral_is_compact_open K).2

theorem chapter05_full_zero_neighborhood_is_nhds
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (chapter01MinkowskiSpace K))
    (hUinf : Uinf ∈ 𝓝 (0 : chapter01MinkowskiSpace K)) :
    chapter05FullZeroNeighborhood K Uinf ∈
      𝓝 (0 : Chapter04AdeleRing K) := by
  rcases mem_nhds_iff.mp hUinf with ⟨W, hWU, hWopen, hWzero⟩
  have hWopen' : IsOpen (chapter05FullZeroNeighborhood K W) :=
    chapter05_full_zero_neighborhood_is_open K W hWopen
  have hWzero' : (0 : Chapter04AdeleRing K) ∈
      chapter05FullZeroNeighborhood K W := by
    change (0 : Chapter04InfiniteAdeleRing K) ∈
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' W ∧
      (0 : Chapter04FiniteAdeleRing K) ∈
        (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K))
    constructor
    · exact ⟨0, hWzero, by simp⟩
    · exact (Chapter04FiniteIntegralAdeleSubring K).zero_mem
  have hWnhds : chapter05FullZeroNeighborhood K W ∈
      𝓝 (0 : Chapter04AdeleRing K) := hWopen'.mem_nhds hWzero'
  apply Filter.mem_of_superset hWnhds
  change ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' W) ×ˢ
      (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)) ⊆
    ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' Uinf) ×ˢ
      (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K))
  exact Set.prod_mono (Set.image_mono hWU) subset_rfl

theorem chapter05_full_zero_neighborhood_meets_diagonal_only_at_zero
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (chapter01MinkowskiSpace K))
    (hUinf : Uinf ∩
      (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) = {0}) :
    chapter05FullZeroNeighborhood K Uinf ∩
        Set.range (chapter05Diagonal K) =
      ({0} : Set (Chapter04AdeleRing K)) := by
  classical
  ext x
  constructor
  · rintro ⟨⟨hxInf, hxFin⟩, ⟨a, rfl⟩⟩
    rcases hxInf with ⟨y, hyU, hyeq⟩
    change chapter05FiniteDiagonal K a ∈
      (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)) at hxFin
    have haInt : a ∈ chapter05RingOfIntegersSet K := by
      apply (chapter05_diagonal_integrality_iff K a).2
      intro v
      exact (chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral K
        (chapter05FiniteDiagonal K a)).mp hxFin v
    have hmix : NumberField.mixedEmbedding K a ∈ Uinf := by
      have hyeq' : y =
          NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
            (chapter05InfiniteDiagonal K a) := by
        calc
          y = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
              ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y) :=
            (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y |>.symm
          _ = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
              (chapter05InfiniteDiagonal K a) := by
            rw [hyeq]
            rfl
      rw [NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      simpa [chapter05InfiniteDiagonal] using
        (show NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
            (chapter05InfiniteDiagonal K a) ∈ Uinf by rw [← hyeq']; exact hyU)
    have hmixInt : NumberField.mixedEmbedding K a ∈
        (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) := by
      apply (chapter01_integer_lattice_mem_iff (K := K)).2
      rcases haInt with ⟨r, hr⟩
      exact ⟨r, congrArg (NumberField.mixedEmbedding K) hr⟩
    have hmem : NumberField.mixedEmbedding K a ∈ ({0} : Set (chapter01MinkowskiSpace K)) := by
      rw [← hUinf]
      exact ⟨hmix, hmixInt⟩
    have hzero : NumberField.mixedEmbedding K a = 0 :=
      Set.mem_singleton_iff.mp hmem
    have ha0 : a = 0 := by
      apply chapter01_minkowski_embedding_injective K
      simpa using hzero
    subst a
    simp
  · intro hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    have hzeroInf : (0 : chapter01MinkowskiSpace K) ∈ Uinf := by
      have hzero' : (0 : chapter01MinkowskiSpace K) ∈ Uinf ∩
          (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) := by
        rw [hUinf]
        simp
      exact hzero'.1
    constructor
    · constructor
      · exact ⟨0, hzeroInf, by
          change (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm 0 = 0
          simp⟩
      · exact (Chapter04FiniteIntegralAdeleSubring K).zero_mem
    · exact ⟨0, by simp⟩

/-!
**Theorem 5.2.** The canonical diagonal copy of `K` is a discrete subgroup of
the full adele additive group.
-/
theorem chapter05_theorem_5_2_diagonal_is_discrete
    (K : Type*) [Field K] [NumberField K]
    :
    DiscreteTopology (Set.range (chapter05Diagonal K)) := by
  classical
  rcases chapter05_exists_small_archimedean_neighborhood K with
    ⟨Uinf, hUinfOpen, hUinfNhds, hUinfInter⟩
  let U : Set (Chapter04AdeleRing K) := chapter05FullZeroNeighborhood K Uinf
  have hUopen : IsOpen U := by
    exact chapter05_full_zero_neighborhood_is_open K Uinf hUinfOpen
  have hUzero : (0 : Chapter04AdeleRing K) ∈ U := by
    exact mem_of_mem_nhds
      (chapter05_full_zero_neighborhood_is_nhds K Uinf hUinfNhds)
  have hUinter : U ∩ Set.range (chapter05Diagonal K) =
      ({0} : Set (Chapter04AdeleRing K)) := by
    exact chapter05_full_zero_neighborhood_meets_diagonal_only_at_zero K Uinf hUinfInter
  rw [discreteTopology_subtype_iff']
  intro x hx
  rcases hx with ⟨a, rfl⟩
  let V : Set (Chapter04AdeleRing K) :=
    (fun z : Chapter04AdeleRing K => z - chapter05Diagonal K a) ⁻¹' U
  refine ⟨V, hUopen.preimage (continuous_id.sub continuous_const), ?_⟩
  ext z
  constructor
  · rintro ⟨hzV, ⟨b, rfl⟩⟩
    change chapter05Diagonal K b - chapter05Diagonal K a ∈ U at hzV
    have hdiff : chapter05Diagonal K (b - a) ∈ U ∩
        Set.range (chapter05Diagonal K) := by
      constructor
      · simpa only [map_sub] using hzV
      · exact ⟨b - a, rfl⟩
    have hmem : chapter05Diagonal K (b - a) ∈ ({0} : Set (Chapter04AdeleRing K)) := by
      rw [← hUinter]
      exact hdiff
    have hzero : chapter05Diagonal K (b - a) = 0 :=
      Set.mem_singleton_iff.mp hmem
    have hba0 : b - a = 0 := chapter05_diagonal_injective K hzero
    simp [sub_eq_zero.mp hba0]
  · intro hz
    have hz' : z = chapter05Diagonal K a := Set.mem_singleton_iff.mp hz
    subst z
    constructor
    · change chapter05Diagonal K a - chapter05Diagonal K a ∈ U
      simpa using hUzero
    · exact ⟨a, rfl⟩

theorem chapter05_diagonal_full_is_closed
    (K : Type*) [Field K] [NumberField K]
    (hdisc : DiscreteTopology (Set.range (chapter05Diagonal K))) :
    IsClosed (Set.range (chapter05Diagonal K)) := by
  change IsClosed ((chapter05Diagonal K).range.toAddSubgroup : Set (Chapter04AdeleRing K))
  let _ : DiscreteTopology (chapter05Diagonal K).range.toAddSubgroup := by
    change DiscreteTopology (Set.range (chapter05Diagonal K))
    exact hdisc
  exact AddSubgroup.isClosed_of_discrete

theorem chapter05_theorem_5_2_diagonal_is_discrete_closed
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Set.range (chapter05Diagonal K)) ∧
      IsClosed (Set.range (chapter05Diagonal K)) := by
  have hdisc : DiscreteTopology (Set.range (chapter05Diagonal K)) :=
    chapter05_theorem_5_2_diagonal_is_discrete K
  exact ⟨hdisc, chapter05_diagonal_full_is_closed K hdisc⟩

theorem chapter05_finite_integral_preimage_of_diagonal
    (K : Type*) [Field K] [NumberField K] :
    (chapter05FiniteDiagonal K ⁻¹'
      (Chapter04FiniteIntegralAdeleSubring K :
        Set (Chapter04FiniteAdeleRing K))) =
      chapter05RingOfIntegersSet K := by
  sorry

theorem chapter05_finite_integral_intersection_eq_integer_image
    (K : Type*) [Field K] [NumberField K] :
    Set.range (chapter05FiniteDiagonal K) ∩
        (Chapter04FiniteIntegralAdeleSubring K :
          Set (Chapter04FiniteAdeleRing K)) =
      chapter05FiniteDiagonal K '' chapter05RingOfIntegersSet K := by
  sorry

theorem chapter05_finite_integral_intersection_is_infinite
    (K : Type*) [Field K] [NumberField K] :
    Set.Infinite
      (Set.range (chapter05FiniteDiagonal K) ∩
        (Chapter04FiniteIntegralAdeleSubring K :
          Set (Chapter04FiniteAdeleRing K))) := by
  sorry

/-! The finite-place warning from the source: the compact open integral tail
meets the canonical diagonal in all global integers. -/
theorem chapter05_finite_zero_neighborhood_meets_diagonal_in_integers
    (K : Type*) [Field K] [NumberField K] :
    Set.range (chapter05FiniteDiagonal K) ∩ chapter05FiniteZeroNeighborhood K =
        chapter05FiniteDiagonal K '' chapter05RingOfIntegersSet K ∧
      Set.Infinite
        (Set.range (chapter05FiniteDiagonal K) ∩
          chapter05FiniteZeroNeighborhood K) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
