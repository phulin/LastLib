import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Length

import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Section03NormalSurfacesNeedNotBeRegular
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section04LocalityAndProjectivity
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section05Examples
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Section02GeneratorsRelationsAndSymmetricAlgebra
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Section04BaseChangeAndItsLimits
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05.Section03NumericalRecognitionOfInversePointBlowups
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Section01WhatResolutionMustPreserve
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Section02ThicknessSingularities
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Section03EmbeddedResolutionOfSpecialFibersAndSections
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Section04WhatBlowupsDoNotAccomplish
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Section01LengthOfAProperIntersection
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Section04HomologicalIntersectionAndSelfIntersection
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter08.Section04HorizontalSelfIntersectionAndTheBase
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09.Section02IntersectionWithPrincipalDivisors
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter10.Section04FiniteMapsAndDegree
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter11.Section02IntersectionsOfStrictTransforms
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12.Section04ExceptionalCurves
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section03NegativityAndTheExactKernel
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Section03TheCorrectedLocalPairing

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory Set
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
open scoped BigOperators

universe u v

/-! ## Shared vocabulary -/

abbrev Chapter15CoherentIdeal (X : Scheme.{u}) :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07CoherentIdeal X

abbrev Chapter15Blowup {X : Scheme.{u}} (I : Chapter15CoherentIdeal X) :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07Blowup I

def chapter15NonzeroCoherentIdeal {X : Scheme.{u}}
    (I : Chapter15CoherentIdeal X) : Prop :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07IsNonzeroIdeal I

noncomputable def chapter15BlowupOfIdeal {X : Scheme.{u}}
    (I : Chapter15CoherentIdeal X) : Chapter15Blowup I :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07Blowup I

def chapter15BlowupIsRelativeProj {X : Scheme.{u}}
    {I : Chapter15CoherentIdeal X} (B : Chapter15Blowup I) : Prop :=
  B.rees_presentation

def chapter15BlowupUniversalProperty {X : Scheme.{u}}
    {I : Chapter15CoherentIdeal X} (B : Chapter15Blowup I) : Prop :=
  ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07IsInvertibleIdeal
        (I.ideal.comap g) →
      ∃! u : Y ⟶ B.carrier, u ≫ B.projection = g

def chapter15BlowupIsLocalOnTarget {X : Scheme.{u}}
    (I : Chapter15CoherentIdeal X) (B : Chapter15Blowup I) (U : X.Opens) : Prop :=
  Nonempty
    (LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07BlowupLocalityWitness
      I B U)

def chapter15BlowupCommutesWithFlatBaseChange
    {X Y : Scheme.{u}} {I : Chapter15CoherentIdeal X}
    (B : Chapter15Blowup I) (f : Y ⟶ X) : Prop :=
  Flat f ∧
    Nonempty
      (LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07BlowupBaseChangeWitness
        B f)

abbrev Chapter15ArithmeticSurface :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter12.Chapter12ArithmeticSurface

def chapter15ArithmeticSurfaceHypotheses (X : Chapter15ArithmeticSurface) : Prop :=
  X.base_excellent ∧ X.base_connected ∧ X.base_dedekind ∧ X.integral ∧ X.regular ∧
    X.proper ∧ X.flat ∧ X.relativeDimensionOne ∧ X.genericFiberSmooth ∧
      X.genericFiberGeometricallyConnected

/-! ## Local lengths and residue-degree weighting -/

abbrev Chapter15LocalEffectiveCartierCurve (A : Type u) [CommRing A] :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Chapter07LocalEffectiveCartierCurve A

def chapter15LocalIntersectionLength {A : Type u} [CommRing A]
    (C D : Chapter15LocalEffectiveCartierCurve A) : ℕ∞ :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Chapter07LocalIntersectionMultiplicity C D

def chapter15ProperLocalIntersectionContribution {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter15LocalEffectiveCartierCurve A)
    (_hproper : Chapter07ProperIntersectionAt C D) (residueDegree : ℕ) : ℤ :=
  (Chapter07LocalIntersectionNumber C D : ℤ) * (residueDegree : ℤ)

def chapter15ResidueWeightedLocalLength (length residueDegree : ℕ) : ℤ :=
  (length : ℤ) * (residueDegree : ℤ)

/-! ## Component matrices and corrections -/

abbrev Chapter15SpecialFiberIntersectionData :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Chapter13SpecialFiberIntersectionData

def chapter15ComponentMatrix
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter15SpecialFiberIntersectionData (A := A) (s := s)) :
    Matrix (Fin T.r) (Fin T.r) ℤ :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.chapter13IntersectionMatrix T

def chapter15RationalComponentMatrix
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter15SpecialFiberIntersectionData (A := A) (s := s)) :
    Matrix (Fin T.r) (Fin T.r) ℚ :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.chapter13RationalIntersectionMatrix T

def chapter15MultiplicityKernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter15SpecialFiberIntersectionData (A := A) (s := s)) :
    Set (Fin T.r → ℚ) :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.chapter13RationalMatrixKernel T

def chapter15FiberLine
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter15SpecialFiberIntersectionData (A := A) (s := s)) :
    Set (Fin T.r → ℚ) :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.chapter13MultiplicityLine T

def chapter15NegativeDefiniteModuloFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter15SpecialFiberIntersectionData (A := A) (s := s)) : Prop :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.chapter13NegativeDefiniteModuloFiber T

abbrev Chapter15FiberMatrix :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14FiberMatrix

abbrev Chapter15HorizontalDivisor :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14HorizontalDivisor

abbrev Chapter15RationalVerticalDivisor :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14RationalVerticalDivisor

def chapter15Balanced {r : ℕ}
    {F : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14FiberMatrix r}
    (d : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14RationalVector r)
    (v : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14RationalVerticalDivisor F) : Prop :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.chapter14Balanced F d v

def chapter15ComponentEnergy {r : ℕ}
    (F : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14FiberMatrix r)
    (v : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14RationalVerticalDivisor F) : ℚ :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.chapter14ComponentEnergy F v

def chapter15CorrectedLocalPairing {r : ℕ}
    {F : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14FiberMatrix r}
    (I : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14LocalIntersectionData F)
    (D G : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14RationalVerticalDivisor F) : ℚ :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.chapter14CorrectedLocalPairing I D G hgeneric v

def chapter15FullyCorrectedLocalPairing {r : ℕ}
    {F : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14FiberMatrix r}
    (I : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14LocalIntersectionData F)
    (D G : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14HorizontalDivisor F)
    (hgeneric : I.genericDisjoint D G)
    (v w : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Chapter14RationalVerticalDivisor F) : ℚ :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.chapter14FullyCorrectedLocalPairing I D G hgeneric v w

/-! ## Precise warning predicates used in §15.3 -/

def chapter15ChartIsFreePolynomialPresentation
    (A C : Type u) [CommRing A] [CommRing C] : Prop :=
  ∃ n : ℕ, Nonempty (C ≃+* MvPolynomial (Fin n) A)

def chapter15ChartNeedNotBeFreePolynomialPresentation
    (A C : Type u) [CommRing A] [CommRing C] : Prop :=
  ¬ chapter15ChartIsFreePolynomialPresentation A C

def chapter15AffineBlowupChart
    (A : Type u) [CommRing A] (a b : A) :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07RatioSubalgebra A a b

def chapter15AffineBlowupChartNeedNotBePolynomial
    (A : Type u) [CommRing A] (a b : A) : Prop :=
  chapter15ChartNeedNotBeFreePolynomialPresentation A
    (chapter15AffineBlowupChart A a b)

/- LOCAL_DEPENDENCY_GUESS: the preceding chart API identifies the affine chart
as a localization subalgebra but does not yet expose a concrete non-polynomial
chart witness.  This predicate keeps the source warning available without
pretending that every chart has a polynomial presentation. -/
def chapter15ThereExistsANonPolynomialBlowupChart : Prop :=
  ∃ (A : Type u) (inst : CommRing A) (a b : A),
    @chapter15AffineBlowupChartNeedNotBePolynomial A inst a b

def chapter15SymmetricToReesMayHaveKernel
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Chapter02SymmetricToReesMayHaveKernel I

def chapter15ArbitraryBaseChangeMayHavePowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Chapter03ArbitraryBaseChangeMayHavePowerTorsion I

def chapter15StrictTransformRemovesExceptionalComponents
    {Z Y X : Scheme.{u}} {z : Z ⟶ X} {f : Y ⟶ X}
    (T : LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07StrictTransformData z f) : Prop :=
  ∀ E : LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07ExceptionalDivisor f,
    ¬ E.divisor.support ⊆ Set.range T.inclusion

def chapter15NormalSurfaceCanBeSingular
    (k : Type u) [CommRing k] : Prop :=
  LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Chapter04QuadraticConeNormal k

def chapter15NormalizedBlowupMayNeedFurtherBlowups
    (R : Type u) [CommRing R] (π : R) (m : ℕ) : Prop :=
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Chapter08ArithmeticCuspSurfaceCanRemainNormalSingular
      R π m

/- LOCAL_DEPENDENCY_GUESS: the resolution interface in Chapter 6 records a
supported regular projective modification, while the source names its stages
as normalized blowups.  This wrapper retains that stage label explicitly. -/
structure Chapter15NormalizedBlowupResolution
    {X : Scheme.{u}} (hX : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Chapter06NormalExcellentSurface X) where
  resolution : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Chapter06SurfaceResolution hX
  stagesAreNormalizedBlowups : Prop
  stagesAreNormalizedBlowupsEvidence : stagesAreNormalizedBlowups

def chapter15NormalizedBlowupResolutionIsSupportedOnSingularLocus
    {X : Scheme.{u}} {hX : LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.Chapter06NormalExcellentSurface X}
    (R : Chapter15NormalizedBlowupResolution hX) : Prop :=
  R.resolution.center ⊆
    LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter06.chapter06SingularLocus hX

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter15
