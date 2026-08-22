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
  sorry

theorem chapter05_full_zero_neighborhood_is_nhds
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (chapter01MinkowskiSpace K))
    (hUinf : Uinf ∈ 𝓝 (0 : chapter01MinkowskiSpace K)) :
    chapter05FullZeroNeighborhood K Uinf ∈
      𝓝 (0 : Chapter04AdeleRing K) := by
  sorry

theorem chapter05_full_zero_neighborhood_meets_diagonal_only_at_zero
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (chapter01MinkowskiSpace K))
    (hUinf : Uinf ∩
      (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) = {0}) :
    chapter05FullZeroNeighborhood K Uinf ∩
        Set.range (chapter05Diagonal K) =
      ({0} : Set (Chapter04AdeleRing K)) := by
  sorry

/-!
**Theorem 5.2.** The canonical diagonal copy of `K` is a discrete subgroup of
the full adele additive group.
-/
theorem chapter05_theorem_5_2_diagonal_is_discrete
    (K : Type*) [Field K] [NumberField K]
    :
    DiscreteTopology (Set.range (chapter05Diagonal K)) := by
  sorry

theorem chapter05_diagonal_full_is_closed
    (K : Type*) [Field K] [NumberField K]
    (hdisc : DiscreteTopology (Set.range (chapter05Diagonal K))) :
    IsClosed (Set.range (chapter05Diagonal K)) := by
  sorry

theorem chapter05_theorem_5_2_diagonal_is_discrete_closed
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Set.range (chapter05Diagonal K)) ∧
      IsClosed (Set.range (chapter05Diagonal K)) := by
  sorry

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
