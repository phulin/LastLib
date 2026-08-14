import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section02TheWeightedLaplacianIdentity

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open scoped BigOperators

/-! ## 13.3. Negativity and its exact kernel -/

/- This certificate records the standard connected-fibers route mentioned in
the source.  The actual Stein-factor/connectedness theorem belongs to the
earlier relative-surface chapters; the present chapter consumes its graph
connectedness conclusion explicitly. -/
structure Chapter13ConnectedFibersCertificate
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) where
  geometricallyConnectedGenericFiber : Prop
  pushforwardStructureSheafIsBase : Prop
  connectedFibers : chapter13GraphConnected T

theorem chapter13_graph_connected_of_connected_fibers_certificate
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (C : Chapter13ConnectedFibersCertificate T) :
    chapter13GraphConnected T := by
  exact C.connectedFibers

theorem chapter13_vertical_self_intersection_eq_zero_iff_constant_potential
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T)
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∃ c : ℚ, ∀ i, chapter13WeightedPotential T a i = c := by
  sorry

theorem chapter13_vertical_self_intersection_eq_zero_iff_multiple_of_fiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T)
    (a : Fin T.r → ℚ) :
    chapter13VerticalSelfIntersection T a = 0 ↔
      ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T := by
  sorry

theorem chapter13_rational_intersection_kernel_eq_multiplicity_line
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13RationalMatrixKernel T = chapter13MultiplicityLine T := by
  sorry

theorem chapter13_rational_matrix_kernel_iff_linear_map_kernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) :
    a ∈ chapter13RationalMatrixKernel T ↔
      a ∈ LinearMap.ker
        (chapter13RationalMatrixLinearMap
          (chapter13RationalIntersectionMatrix T)) := by
  sorry

theorem chapter13_rational_matrix_kernel_mem_iff_multiple_of_fiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T)
    (a : Fin T.r → ℚ) :
    a ∈ chapter13RationalMatrixKernel T ↔
      ∃ c : ℚ, a = c • chapter13RationalMultiplicityVector T := by
  sorry

def chapter13NegativeDefiniteModuloFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) : Prop :=
  ∀ a, a ∉ chapter13MultiplicityLine T →
    chapter13VerticalSelfIntersection T a < 0

theorem chapter13_pairing_negative_definite_on_fiber_quotient
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hconn : chapter13GraphConnected T) :
    chapter13NegativeDefiniteModuloFiber T := by
  sorry

/- The quotient notation is also exposed as a reusable membership criterion;
the quotient by the whole fiber is essential because the unreduced matrix has
the fiber in its radical. -/
theorem chapter13_unreduced_matrix_is_not_negative_definite
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    chapter13VerticalSelfIntersection T
        (chapter13RationalMultiplicityVector T) = 0 := by
  sorry

/-! ### Disconnected support -/

theorem chapter13_component_indicator_is_in_matrix_kernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (C : Set (Fin T.r))
    (hC : C.Nonempty)
    (hboundary : chapter13NoBoundaryEdges T C) :
    chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13ComponentIndicator T C) := by
  sorry

theorem chapter13_disconnected_support_supplies_component_kernel_vector
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (C : Set (Fin T.r))
    (hC : C.Nonempty)
    (hproper : C ≠ Set.univ)
    (hboundary : chapter13NoBoundaryEdges T C) :
    chapter13MatrixKernel (chapter13IntersectionMatrix T)
      (chapter13ComponentIndicator T C) ∧
      chapter13ComponentIndicator T C ≠
        chapter13FiberMultiplicityVector T := by
  sorry

/- These records make the source warnings usable by later chapters without
asserting a false global counterexample in the present statement pass. -/
structure Chapter13FiberRelationFailure where
  relation : Prop
  failure : ¬ relation
  missingProperness : Prop
  missingFlatness : Prop

structure Chapter13NonRegularComponentWarning where
  component : Type u
  notCartier : Prop
  rationalIntersectionMatrix : Matrix component component ℚ
  resolutionDependent : Prop

/-! ### Component self-intersections -/

theorem chapter13_component_self_intersection_formula
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    (chapter13ComponentIntersection T i i : ℚ) =
      -(1 / (T.multiplicity i : ℚ)) *
        ∑ j in Finset.univ.erase i,
          (T.multiplicity j : ℚ) *
            (chapter13ComponentIntersection T i j : ℚ) := by
  sorry

theorem chapter13_component_self_intersection_negative_of_meeting_rest
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r)
    (hmeet : ∃ j, i ≠ j ∧ T.components_meet i j) :
    chapter13ComponentIntersection T i i < 0 := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
