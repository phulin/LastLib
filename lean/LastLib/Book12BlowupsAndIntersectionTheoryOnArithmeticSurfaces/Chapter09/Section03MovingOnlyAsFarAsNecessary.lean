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
    [M : Chapter09MovingLemmaTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface) :
    ∃ D' : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface,
      chapter09LinearlyEquivalent D D' ∧
        chapter09NoCommonPrimeComponents D' E := by
  exact M.avoids_common_components D E

theorem chapter09_moving_lemma_preserves_linear_equivalence
    {k : Type u} [Field k] [Infinite k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [M : Chapter09MovingLemmaTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface) :
    ∃ D', chapter09LinearlyEquivalent D D' ∧
      chapter09NoCommonPrimeComponents D' E := by
  exact chapter09_moving_lemma_avoids_common_components X D E

/-- The effective form supplies exactly the extra hypothesis required by the
local-length witnesses after moving. -/
theorem chapter09_moving_lemma_avoids_common_components_preserving_effectivity
    {k : Type u} [Field k] [Infinite k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [M : Chapter09MovingLemmaTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E) :
    ∃ D' : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface,
      chapter09LinearlyEquivalent D D' ∧
        chapter09NoCommonPrimeComponents D' E ∧
          chapter09IsEffectiveWeilDivisor D' := by
  sorry

/-- For a moved pair, the local-length package returns the degree of the
residue-weighted intersection zero-cycle. -/
theorem chapter09_local_length_intersection_is_zeroCycle_degree
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E) :
    chapter09LocalLengthIntersection X D E h hD hE =
      chapter09ZeroCycleDegree X.structureMap
        (T.localIntersectionCycle D E h hD hE)
        (T.localIntersectionCycle_residueDegrees_finite D E h hD hE) := by
  sorry

theorem chapter09_local_length_cycle_support_iff_nonzero_length
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E)
    (x : Chapter09ClosedPoint X.carrier) :
    x ∈ (T.localIntersectionCycle D E h hD hE).support ↔
      (T.localLengthWitness D E h hD hE x).length ≠ 0 := by
  sorry

theorem chapter09_local_length_intersection_is_symmetric
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [T : Chapter09LocalLengthIntersectionTheory X]
    (D E : Chapter09WeilDivisor X.toChapter09RegularNoetherianIntegralSurface)
    (hDE : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E) :
    chapter09LocalLengthIntersection X D E hDE hD hE =
      chapter09LocalLengthIntersection X E D
        (chapter09_noCommonPrimeComponents_symm hDE) hE hD := by
  sorry

/-- Independence of the local-length definition from the chosen moved
representative is the degree-zero principal-divisor argument on proper curves. -/
theorem chapter09_local_length_independent_of_moving_representative
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [T : Chapter09LocalLengthIntersectionTheory X] :
    ∀ D D₂ E
      (hD : chapter09NoCommonPrimeComponents D E)
      (hD₂ : chapter09NoCommonPrimeComponents D₂ E)
      (hEffD : chapter09IsEffectiveWeilDivisor D)
      (hEffD₂ : chapter09IsEffectiveWeilDivisor D₂)
      (hEffE : chapter09IsEffectiveWeilDivisor E),
      chapter09LinearlyEquivalent D D₂ →
        chapter09ZeroCycleDegree X.structureMap
              (T.localIntersectionCycle D E hD hEffD hEffE)
              (T.localIntersectionCycle_residueDegrees_finite D E hD hEffD hEffE) =
          chapter09ZeroCycleDegree X.structureMap
              (T.localIntersectionCycle D₂ E hD₂ hEffD₂ hEffE)
              (T.localIntersectionCycle_residueDegrees_finite D₂ E hD₂ hEffD₂ hEffE) := by
  sorry

/-- The local-length definition agrees with the line-bundle definition when
the divisors have no common component. -/
theorem chapter09_local_length_recovers_lineBundle_definition
    {k : Type u} [Field k]
    (X : Chapter09ProjectiveRegularSurfaceOverField k)
    [P : Chapter09PrincipalDivisorTheory X.toChapter09RegularNoetherianIntegralSurface]
    [T : Chapter09LocalLengthIntersectionTheory X] :
  ∀ D E (h : chapter09NoCommonPrimeComponents D E)
      (hD : chapter09IsEffectiveWeilDivisor D)
      (hE : chapter09IsEffectiveWeilDivisor E),
      T.lineBundleIntersection D E =
        chapter09ZeroCycleDegree X.structureMap (T.localIntersectionCycle D E h hD hE)
          (T.localIntersectionCycle_residueDegrees_finite D E h hD hE) := by
  sorry

/-! ### The three controlled cases -/

/-- The data used by the arithmetic-surface calculations: proper local
lengths, restriction to a vertical curve, or a bilinear vertical pairing. -/
inductive Chapter09ControlledIntersectionInput
    (X : Chapter09RegularNoetherianIntegralSurface)
  | noCommonComponents
      (D E : Chapter09WeilDivisor X)
      (proper : chapter09NoCommonPrimeComponents D E)
      (effectiveD : chapter09IsEffectiveWeilDivisor D)
      (effectiveE : chapter09IsEffectiveWeilDivisor E)
  | divisorAgainstVerticalCurve
      (_D : Chapter09CartierPresentation X) (_C : Chapter09VerticalCurve X)
  | verticalDivisors
      (D E : Chapter09WeilDivisor X)
      (verticalD : chapter09IsVerticalDivisor D)
      (verticalE : chapter09IsVerticalDivisor E)

theorem chapter09_controlled_intersection_case_noCommonComponents
    {X : Chapter09RegularNoetherianIntegralSurface}
    (D E : Chapter09WeilDivisor X)
    (h : chapter09NoCommonPrimeComponents D E)
    (hD : chapter09IsEffectiveWeilDivisor D)
    (hE : chapter09IsEffectiveWeilDivisor E) :
    Nonempty (Chapter09ControlledIntersectionInput X) := by
  exact ⟨.noCommonComponents D E h hD hE⟩

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

/- The inductive input and its three constructors are the protocol: actual
local-length, restriction-degree, and vertical-pairing theories remain extra
data rather than a proposition asserted for every abstract surface. -/

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09
