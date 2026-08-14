import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section01TheFiberRelation

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-! ## 13.2. The weighted Laplacian identity -/

theorem chapter13_weighted_laplacian_identity
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a =
      -chapter13WeightedLaplacianEnergy T a := by
  sorry

theorem chapter13_weighted_laplacian_term_nonnegative
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) (i j : Fin T.r) (hij : i < j) :
    0 ≤
      (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
        (chapter13ComponentIntersection T i j : ℚ) *
          (chapter13WeightedPotential T a i -
            chapter13WeightedPotential T a j) ^ 2 := by
  sorry

theorem chapter13_weighted_laplacian_identity_expanded
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a =
      -∑ i, ∑ j ∈ Finset.Ioi i,
        (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
          (chapter13ComponentIntersection T i j : ℚ) *
            (chapter13WeightedPotential T a i -
              chapter13WeightedPotential T a j) ^ 2 := by
  simpa [chapter13WeightedLaplacianEnergy] using
    chapter13_weighted_laplacian_identity T a

theorem chapter13_vertical_self_intersection_nonpositive
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a ≤ 0 := by
  sorry

theorem chapter13_vertical_self_intersection_eq_zero_iff_edge_potentials_equal
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∀ i j, T.components_meet i j →
        chapter13WeightedPotential T a i = chapter13WeightedPotential T a j := by
  sorry

theorem chapter13_vertical_self_intersection_eq_zero_iff_off_diagonal_potentials_equal
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∀ i j, i ≠ j → chapter13ComponentIntersection T i j ≠ 0 →
        chapter13WeightedPotential T a i = chapter13WeightedPotential T a j := by
  sorry

/- The source's graph interpretation is now an API statement: the symmetric
intersection form is the negative of the conductance energy after the vertex
potential is rescaled by the fiber multiplicity. -/
theorem chapter13_intersection_form_is_negative_weighted_graph_laplacian
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    ∀ a : Fin T.r → ℚ,
      chapter13VerticalSelfIntersection T a =
        -chapter13WeightedLaplacianEnergy T a := by
  intro a
  exact chapter13_weighted_laplacian_identity T a

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
