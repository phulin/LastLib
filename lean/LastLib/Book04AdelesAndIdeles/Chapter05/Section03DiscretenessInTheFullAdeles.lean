import LastLib.Book04AdelesAndIdeles.Chapter05.Section01TheDiagonalEmbedding

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
  sorry

theorem chapter05_exists_small_archimedean_neighborhood
    (K : Type*) [Field K] [NumberField K] :
    ∃ Uinf : Set (chapter01MinkowskiSpace K),
      IsOpen Uinf ∧ Uinf ∈ 𝓝 (0 : chapter01MinkowskiSpace K) ∧
        Uinf ∩ (NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) =
          {0} := by
  sorry

theorem chapter05_full_adele_is_nondiscrete_at_zero
    (K : Type*) [Field K] [NumberField K] :
    chapter05NondiscreteAtZero (G := Chapter04AdeleRing K) := by
  sorry

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
