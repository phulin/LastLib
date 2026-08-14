import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-! ## 13.1. The fiber relation -/

def chapter13OffDiagonalWeightedSum
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) : ℤ :=
  ∑ j ∈ Finset.univ.erase i,
    (T.multiplicity j : ℤ) * chapter13ComponentIntersection T i j

theorem chapter13_fiber_intersection_expands
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13FiberIntersectionWithComponent T i =
      ∑ j, (T.multiplicity j : ℤ) *
        chapter13ComponentIntersection T j i := by
  classical
  let f : AlgebraicCycle A.carrier ℤ →+ ℤ :=
    { toFun := fun x => T.intersection x (T.component i).cycle
      map_zero' := by
        have h := T.intersection_add_left 0 0 (T.component i).cycle
        simpa using h.symm
      map_add' := by
        intro x y
        exact T.intersection_add_left x y (T.component i).cycle }
  rw [chapter13FiberIntersectionWithComponent, T.fiber_cycle_decomposition]
  change f (∑ j, (T.multiplicity j : ℤ) • (T.component j).cycle) = _
  rw [map_sum]
  change (∑ j, T.intersection ((T.multiplicity j : ℤ) • (T.component j).cycle)
      (T.component i).cycle) = _
  congr 1
  funext j
  exact T.intersection_smul_left _ _ _

/-- The principal local equation of the fiber has zero intersection with every
proper component.  This is the book-facing form of (13.1). -/
theorem chapter13_fiber_relation
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13FiberRelation T := by
  intro i
  rw [← chapter13_fiber_intersection_expands T i]
  exact T.principal_fiber_restriction i

theorem chapter13_fiber_relation_component_form
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13FiberIntersectionWithComponent T i = 0 := by
  exact T.principal_fiber_restriction i

theorem chapter13_fiber_relation_matrix_form
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    ∑ j, chapter13ComponentIntersection T i j *
        chapter13FiberMultiplicityVector T j = 0 := by
  change (∑ j, chapter13ComponentIntersection T i j *
    (T.multiplicity j : ℤ)) = 0
  calc
    (∑ j, chapter13ComponentIntersection T i j * (T.multiplicity j : ℤ)) =
        ∑ j, (T.multiplicity j : ℤ) *
          chapter13ComponentIntersection T j i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show chapter13ComponentIntersection T i j =
        chapter13ComponentIntersection T j i from T.symmetric _ _]
      exact mul_comm _ _
    _ = 0 := chapter13_fiber_relation T i

/- The multiplicity column is in the kernel of the symmetric matrix
`M = ((Γᵢ · Γⱼ))`. -/
theorem chapter13_multiplicity_vector_in_kernel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13FiberMultiplicityVector T) := by
  intro i
  change (∑ j, chapter13ComponentIntersection T i j *
    (T.multiplicity j : ℤ)) = 0
  exact chapter13_fiber_relation_matrix_form T i

theorem chapter13_intersection_matrix_symmetric
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Matrix.IsSymm (chapter13IntersectionMatrix T) := by
  change Matrix.transpose (chapter13IntersectionMatrix T) =
    chapter13IntersectionMatrix T
  funext i j
  exact (T.symmetric _ _).symm

/-! Off-diagonal intersections are sums of local lengths weighted by residue
degrees.  The `components_meet` predicate is the support-level side of that
statement; the two equivalent forms are both exposed for later graph code. -/
theorem chapter13_off_diagonal_nonnegative
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    {i j : Fin T.r} (hij : i ≠ j) :
    0 ≤ chapter13ComponentIntersection T i j := by
  exact T.off_diagonal_nonnegative i j hij

theorem chapter13_off_diagonal_positive_iff_meet
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    {i j : Fin T.r} (hij : i ≠ j) :
    (0 < chapter13ComponentIntersection T i j ↔ T.components_meet i j) := by
  exact T.off_diagonal_positive_iff_meet i j hij

theorem chapter13_diagonal_entry_relation
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    (T.multiplicity i : ℤ) * chapter13ComponentIntersection T i i =
      -chapter13OffDiagonalWeightedSum T i := by
  classical
  change (T.multiplicity i : ℤ) * chapter13ComponentIntersection T i i =
    -(∑ j ∈ Finset.univ.erase i,
      (T.multiplicity j : ℤ) * chapter13ComponentIntersection T i j)
  have h := chapter13_fiber_relation T i
  have hsum := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j : Fin T.r => (T.multiplicity j : ℤ) *
      chapter13ComponentIntersection T j i) (Finset.mem_univ i)
  rw [← hsum] at h
  have hsymm :
      (∑ j ∈ Finset.univ.erase i,
        (T.multiplicity j : ℤ) * chapter13ComponentIntersection T j i) =
      ∑ j ∈ Finset.univ.erase i,
        (T.multiplicity j : ℤ) * chapter13ComponentIntersection T i j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show chapter13ComponentIntersection T j i =
      chapter13ComponentIntersection T i j from T.symmetric _ _]
  calc
    (T.multiplicity i : ℤ) * chapter13ComponentIntersection T i i =
        -(∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℤ) * chapter13ComponentIntersection T j i) :=
      eq_neg_of_add_eq_zero_right h
    _ = -(∑ j ∈ Finset.univ.erase i,
          (T.multiplicity j : ℤ) * chapter13ComponentIntersection T i j) :=
      congrArg Neg.neg hsymm

theorem chapter13_diagonal_nonpositive
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13ComponentIntersection T i i ≤ 0 := by
  have hrel := chapter13_diagonal_entry_relation T i
  have hpos := T.multiplicity_pos i
  have hsum : 0 ≤ chapter13OffDiagonalWeightedSum T i := by
    unfold chapter13OffDiagonalWeightedSum
    apply Finset.sum_nonneg
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    apply mul_nonneg
    · exact Int.natCast_nonneg _
    · exact chapter13_off_diagonal_nonnegative T hji.symm
  have hmul : (T.multiplicity i : ℤ) *
      chapter13ComponentIntersection T i i ≤ 0 := by
    rw [hrel]
    exact neg_nonpos.mpr hsum
  have hm : (0 : ℤ) < (T.multiplicity i : ℤ) := by
    exact_mod_cast hpos
  by_contra hnot
  have hdiag : 0 < chapter13ComponentIntersection T i i := lt_of_not_ge hnot
  have hmulpos : 0 < (T.multiplicity i : ℤ) *
      chapter13ComponentIntersection T i i := mul_pos hm hdiag
  exact (not_lt_of_ge hmul) hmulpos

/-! ### Generic degree and the local-length decomposition -/

theorem chapter13_vertical_prime_intersection_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isVerticalPrime P) :
    T.intersection P.cycle T.fiber.cycle = 0 := by
  exact G.vertical_prime_intersection_zero P hP

theorem chapter13_horizontal_prime_is_finite_flat
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    chapter13FiniteFlatOverNeighborhood P s := by
  exact G.horizontal_prime_is_finite_flat P hP

theorem chapter13_horizontal_fiber_length_eq_finite_flat_rank
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    G.fiberLength P = G.finiteFlatRank P := by
  exact G.horizontal_fiber_length_eq_rank P hP

theorem chapter13_horizontal_local_length_formula
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    T.intersection P.cycle T.fiber.cycle = G.fiberLength P := by
  exact G.horizontal_local_length_formula P hP

theorem chapter13_horizontal_generic_degree_eq_rank
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalPrime P) :
    G.degreeOnGenericFiber P.toChapter13CartierDivisor = G.finiteFlatRank P := by
  exact G.horizontal_degree_eq_rank P hP

/-- The decomposition and additivity certificate in `Chapter13GenericDegreeData`
is the earlier-divisor interface needed to pass from prime divisors to an
arbitrary Cartier divisor. -/
theorem chapter13_cartier_intersection_with_fiber_eq_generic_degree
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A) :
    T.intersection D.cycle T.fiber.cycle = G.degreeOnGenericFiber D := by
  obtain ⟨n, P, a, hD⟩ := G.cartier_prime_decomposition D
  rw [G.degree_on_cartier_prime_decomposition D n P a hD]
  let f : AlgebraicCycle A.carrier ℤ →+ ℤ :=
    { toFun := fun x => T.intersection x T.fiber.cycle
      map_zero' := by
        have h := T.intersection_add_left 0 0 T.fiber.cycle
        simpa using h.symm
      map_add' := by
        intro x y
        exact T.intersection_add_left x y T.fiber.cycle }
  rw [hD]
  change f (∑ k, a k • (P k).cycle) = _
  rw [map_sum]
  change (∑ k, T.intersection (a k • (P k).cycle) T.fiber.cycle) = _
  have hprime : ∀ k, T.intersection (P k).cycle T.fiber.cycle =
      G.degreeOnGenericFiber (P k).toChapter13CartierDivisor := by
    intro k
    rcases G.prime_is_vertical_or_horizontal (P k) with hv | hh
    · exact (G.vertical_prime_intersection_zero (P k) hv).trans
        (G.vertical_prime_generic_degree_zero (P k) hv).symm
    · have hrank : (G.fiberLength (P k) : ℤ) =
          (G.finiteFlatRank (P k) : ℤ) :=
        congrArg (fun z : ℕ => (z : ℤ))
          (G.horizontal_fiber_length_eq_rank (P k) hh)
      exact (G.horizontal_local_length_formula (P k) hh).trans
        (hrank.trans (G.horizontal_degree_eq_rank (P k) hh).symm)
  apply Finset.sum_congr rfl
  intro k hk
  calc
    T.intersection (a k • (P k).cycle) T.fiber.cycle =
        a k * T.intersection (P k).cycle T.fiber.cycle :=
      T.intersection_smul_left _ _ _
    _ = a k * G.degreeOnGenericFiber (P k).toChapter13CartierDivisor := by
      rw [hprime k]

theorem chapter13_horizontal_section_has_generic_degree_one
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (P : Chapter13PrimeDivisor A)
    (hP : G.isHorizontalSection P) :
    G.degreeOnGenericFiber P.toChapter13CartierDivisor = 1 := by
  exact G.horizontal_section_degree_one P hP

theorem chapter13_degree_zero_generic_fiber_has_zero_intersection
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A)
    (hD : chapter13DegreeZeroOnGenericFiber G D) :
    T.intersection D.cycle T.fiber.cycle = 0 := by
  rw [chapter13_cartier_intersection_with_fiber_eq_generic_degree G D]
  exact hD

theorem chapter13_fiber_intersection_zero_iff_generic_degree_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A) :
    T.intersection D.cycle T.fiber.cycle = 0 ↔
      chapter13DegreeZeroOnGenericFiber G D := by
  rw [chapter13_cartier_intersection_with_fiber_eq_generic_degree G D]
  rfl

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
