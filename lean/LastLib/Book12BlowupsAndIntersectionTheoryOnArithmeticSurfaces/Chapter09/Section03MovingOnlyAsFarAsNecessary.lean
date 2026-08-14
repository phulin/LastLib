import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Order TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 9.3. Moving only as far as necessary -/

/-- A projective regular surface over an infinite field admits the moving
representative needed to remove common prime components. -/
theorem chapter09_moving_lemma_avoids_common_components
    {k : Type u} [Field k] [Infinite k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface) :
    ∃ D' : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface,
      chapter09LinearlyEquivalent D D' ∧
        chapter09NoCommonPrimeComponents D' E := by
  sorry

theorem chapter09_moving_lemma_preserves_linear_equivalence
    {k : Type u} [Field k] [Infinite k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface) :
    ∃ D', chapter09LinearlyEquivalent D D' ∧
      chapter09NoCommonPrimeComponents D' E := by
  exact chapter09_moving_lemma_avoids_common_components X D E

/-- For a moved pair, the local-length package returns the degree of the
residue-weighted intersection zero-cycle. -/
theorem chapter09_local_length_intersection_is_zeroCycle_degree
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (h : chapter09NoCommonPrimeComponents D E) :
    chapter09LocalLengthIntersection X D E h =
      chapter09ZeroCycleDegree X.structureMap
        (T.localIntersectionCycle D E h) := by
  rfl

theorem chapter09_local_length_intersection_is_symmetric
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (hDE : chapter09NoCommonPrimeComponents D E)
    (hED : chapter09NoCommonPrimeComponents E D) :
    chapter09LocalLengthIntersection X D E hDE =
      chapter09LocalLengthIntersection X E D hED := by
  sorry

/-- Independence of the local-length definition from the chosen moved
representative is the degree-zero principal-divisor argument on proper curves. -/
theorem chapter09_local_length_independent_of_moving_representative
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [T : Chapter09LocalLengthIntersectionTheory X] :
    T.independent_of_moving_representative := by
  exact T.independent_of_moving_representative

/-- The local-length definition agrees with the line-bundle definition when
the divisors have no common component. -/
theorem chapter09_local_length_recovers_lineBundle_definition
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [T : Chapter09LocalLengthIntersectionTheory X] :
    T.recovers_lineBundle_intersection := by
  exact T.recovers_lineBundle_intersection

/-! ### The three controlled cases -/

/-- The data used by the arithmetic-surface calculations: proper local
lengths, restriction to a vertical curve, or a bilinear vertical pairing. -/
inductive Chapter09ControlledIntersectionInput
    (X : Chapter09RegularNoetherianIntegralSurface)
  | noCommonComponents
      (D E : Chapter09WeilDivisor X)
      (proper : chapter09NoCommonPrimeComponents D E)
  | divisorAgainstVerticalCurve
      (D : Chapter09CartierPresentation X) (C : Chapter09VerticalCurve X)
  | verticalDivisors
      (D E : Chapter09WeilDivisor X)
      (verticalD : chapter09IsVerticalDivisor D)
      (verticalE : chapter09IsVerticalDivisor E)

theorem chapter09_controlled_intersection_case_noCommonComponents
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D E : Chapter09WeilDivisor X)
    (h : chapter09NoCommonPrimeComponents D E) :
    Nonempty (Chapter09ControlledIntersectionInput X) := by
  exact ⟨.noCommonComponents D E h⟩

theorem chapter09_controlled_intersection_case_divisor_against_vertical_curve
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D : Chapter09CartierPresentation X) (C : Chapter09VerticalCurve X) :
    Nonempty (Chapter09ControlledIntersectionInput X) := by
  exact ⟨.divisorAgainstVerticalCurve D C⟩

theorem chapter09_controlled_intersection_case_vertical_divisors
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D E : Chapter09WeilDivisor X)
    (hD : chapter09IsVerticalDivisor D)
    (hE : chapter09IsVerticalDivisor E) :
    Nonempty (Chapter09ControlledIntersectionInput X) := by
  exact ⟨.verticalDivisors D E hD hE⟩

/-- The controlled cases are exactly the interfaces required by the chapter's
later exceptional-curve, fiber-matrix, adjunction, and correction arguments. -/
def chapter09ControlledIntersectionProtocol : Prop :=
  ∀ {X : Chapter09RegularNoetherianIntegralSurface},
    (∀ D E : Chapter09WeilDivisor X,
      chapter09NoCommonPrimeComponents D E →
        Nonempty (Chapter09ControlledIntersectionInput X)) ∧
    (∀ D : Chapter09CartierPresentation X, ∀ C : Chapter09VerticalCurve X,
      Nonempty (Chapter09ControlledIntersectionInput X)) ∧
    (∀ D E : Chapter09WeilDivisor X,
      chapter09IsVerticalDivisor D → chapter09IsVerticalDivisor E →
        Nonempty (Chapter09ControlledIntersectionInput X))

theorem chapter09_controlled_intersection_protocol :
    chapter09ControlledIntersectionProtocol := by
  intro X
  refine ⟨?_, ?_, ?_⟩
  · intro D E h
    exact chapter09_controlled_intersection_case_noCommonComponents D E h
  · intro D C
    exact chapter09_controlled_intersection_case_divisor_against_vertical_curve D C
  · intro D E hD hE
    exact chapter09_controlled_intersection_case_vertical_divisors D E hD hE

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09
