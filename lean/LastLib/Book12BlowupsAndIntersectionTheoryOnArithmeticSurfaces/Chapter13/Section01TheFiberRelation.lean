import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-! ## 13.1. The fiber relation -/

def chapter13OffDiagonalWeightedSum
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) : ℤ :=
  ∑ j in Finset.univ.erase i,
    (T.multiplicity j : ℤ) * chapter13ComponentIntersection T i j

theorem chapter13_fiber_intersection_expands
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13FiberIntersectionWithComponent T i =
      ∑ j, (T.multiplicity j : ℤ) *
        chapter13ComponentIntersection T j i := by
  sorry

/-- The principal local equation of the fiber has zero intersection with every
proper component.  This is the book-facing form of (13.1). -/
theorem chapter13_fiber_relation
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13FiberRelation T := by
  sorry

theorem chapter13_fiber_relation_component_form
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13FiberIntersectionWithComponent T i = 0 := by
  sorry

theorem chapter13_fiber_relation_matrix_form
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    ∑ j, chapter13ComponentIntersection T i j *
        chapter13FiberMultiplicityVector T j = 0 := by
  sorry

/- The multiplicity column is in the kernel of the symmetric matrix
`M = ((Γᵢ · Γⱼ))`. -/
theorem chapter13_multiplicity_vector_in_kernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13FiberMultiplicityVector T) := by
  sorry

theorem chapter13_intersection_matrix_symmetric
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Matrix.IsSymm (chapter13IntersectionMatrix T) := by
  sorry

/-! Off-diagonal intersections are sums of local lengths weighted by residue
degrees.  The `components_meet` predicate is the support-level side of that
statement; the two equivalent forms are both exposed for later graph code. -/
theorem chapter13_off_diagonal_nonnegative
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    {i j : Fin T.r} (hij : i ≠ j) :
    0 ≤ chapter13ComponentIntersection T i j := by
  exact T.off_diagonal_nonnegative i j hij

theorem chapter13_off_diagonal_positive_iff_meet
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    {i j : Fin T.r} (hij : i ≠ j) :
    (0 < chapter13ComponentIntersection T i j ↔ T.components_meet i j) := by
  exact T.off_diagonal_positive_iff_meet i j hij

theorem chapter13_diagonal_entry_relation
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    (T.multiplicity i : ℤ) * chapter13ComponentIntersection T i i =
      -chapter13OffDiagonalWeightedSum T i := by
  sorry

theorem chapter13_diagonal_nonpositive
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13ComponentIntersection T i i ≤ 0 := by
  sorry

/-! ### Generic degree and the local-length decomposition -/

theorem chapter13_vertical_prime_intersection_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isVerticalPrime P) :
    T.intersection P.cycle T.fiber.cycle = 0 := by
  exact G.vertical_prime_intersection_zero P hP

theorem chapter13_horizontal_prime_is_finite_flat
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    G.horizontal_prime_is_finite_flat P hP := by
  sorry

theorem chapter13_horizontal_fiber_length_eq_finite_flat_rank
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    G.fiberLength P = G.finiteFlatRank P := by
  exact G.horizontal_fiber_length_eq_rank P hP

theorem chapter13_horizontal_local_length_formula
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    T.intersection P.cycle T.fiber.cycle = G.fiberLength P := by
  exact G.horizontal_local_length_formula P hP

theorem chapter13_horizontal_generic_degree_eq_rank
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    G.degreeOnGenericFiber P.toChapter13CartierDivisor = G.finiteFlatRank P := by
  exact G.horizontal_degree_eq_rank P hP

/- LOCAL_DEPENDENCY_GUESS: The earlier divisor chapters must supply the finite
prime-divisor decomposition and additive passage from the local vertical and
horizontal calculations to an arbitrary Cartier divisor. -/
theorem chapter13_cartier_intersection_with_fiber_eq_generic_degree
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A) :
    T.intersection D.cycle T.fiber.cycle = G.degreeOnGenericFiber D := by
  sorry

theorem chapter13_horizontal_section_has_generic_degree_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalSection P) :
    G.degreeOnGenericFiber P.toChapter13CartierDivisor = 1 := by
  exact G.horizontal_section_degree_one P hP

theorem chapter13_degree_zero_generic_fiber_has_zero_intersection
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A)
    (hD : chapter13DegreeZeroOnGenericFiber G D) :
    T.intersection D.cycle T.fiber.cycle = 0 := by
  sorry

theorem chapter13_fiber_intersection_zero_iff_generic_degree_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A) :
    T.intersection D.cycle T.fiber.cycle = 0 ↔
      chapter13DegreeZeroOnGenericFiber G D := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
