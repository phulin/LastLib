import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section04ClosedSubschemesFromHomogeneousIdeals
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section02RationalSectionsRecoverDivisors
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07.Section01KaehlerDifferentialsAndLocalParameters

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04

noncomputable section

universe u

/- Chapter 4 uses its own line-bundle wrapper.  The underlying module is the
   same; the invertibility bridge is the only missing compatibility proof. -/
noncomputable def chapter07AsChapter04LineBundle {X : Scheme.{u}}
    (L : Chapter07LineBundle X) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04LineBundle X :=
  { sheaf := L.module
    isInvertible := by sorry }

noncomputable def chapter07OfChapter04LineBundle {X : Scheme.{u}}
    (L : LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04LineBundle X) :
    Chapter07LineBundle X :=
  { module := L.sheaf
    isInvertible := by sorry }

abbrev Chapter07RationalDifferential {X : Scheme.{u}} [IsIntegral X]
    (L : Chapter07LineBundle X) :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalSection
    (chapter07AsChapter04LineBundle L)

/- Scalar multiplication is the generic-fiber scalar action on a rational
   section.  The generator proof is the usual one-dimensional vector-space
   calculation and is left as a proof placeholder. -/
noncomputable def chapter07RationalDifferentialScalarMultiply
    {X : Scheme.{u}} [IsIntegral X] (L : Chapter07LineBundle X)
    (a : X.functionField) (η : Chapter07RationalDifferential L) :
    Chapter07RationalDifferential L := by
  letI := LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04GenericFiberModule
    (chapter07AsChapter04LineBundle L)
  refine { value := a • η.value, isGenerator := ?_ }
  sorry

/-!
## 7.2 Canonical divisors on smooth curves
-/

noncomputable def chapter07CanonicalBundle
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] : Chapter07LineBundle X :=
  chapter07RelativeDifferentialLineBundle f

noncomputable def chapter07CanonicalBundleOfCurve
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)}
    (C : Chapter07SmoothProperGeometricallyConnectedCurve k X f) :
    Chapter07LineBundle X := by
  letI : SmoothOfRelativeDimension 1 f := C.smooth
  exact chapter07CanonicalBundle f

/- The order-of-vanishing API and the finite-support packaging come from the
   earlier codimension-one cycle chapter. -/
structure Chapter07PrincipalDivisorData
    {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Chapter03Normal X]
    (f : X.functionField) where
  divisor : Chapter07WeilDivisor X
  coefficient_eq_order : ∀ P : Chapter03PrimeDivisor X,
    divisor P = Scheme.ord f P.genericPoint

theorem chapter07_canonical_bundle_is_relative_differential_bundle
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] :
    (chapter07CanonicalBundle f).module =
      (chapter07RelativeDifferentialLineBundle f).module := by
  rfl

/- The Chapter 3 principal-cycle construction supplies the finite-support
   divisor; this wrapper keeps the Chapter 7 naming and coefficient formula. -/
theorem chapter07_principal_divisor_exists
    {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Chapter03Normal X]
    (f : X.functionField) : Nonempty (Chapter07PrincipalDivisorData f) := by
  exact ⟨{
    divisor := chapter03PrincipalWeilDivisor f
    coefficient_eq_order := by
      intro P
      simpa [chapter03OrderOfVanishing] using
        (chapter03_principalWeilDivisor_coeff f P)
  }⟩

noncomputable def chapter07PrincipalDivisorData
    {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Chapter03Normal X]
    (f : X.functionField) : Chapter07PrincipalDivisorData f :=
  {
    divisor := chapter03PrincipalWeilDivisor f
    coefficient_eq_order := by
      intro P
      simpa [chapter03OrderOfVanishing] using
        (chapter03_principalWeilDivisor_coeff f P)
  }

noncomputable def chapter07PrincipalDivisor
    {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Chapter03Normal X]
    (f : X.functionField) : Chapter07WeilDivisor X :=
  chapter03PrincipalWeilDivisor f

theorem chapter07_principal_divisor_apply
    {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Chapter03Normal X]
    (f : X.functionField) (P : Chapter03PrimeDivisor X) :
    chapter07PrincipalDivisor f P = Scheme.ord f P.genericPoint := by
  simpa [chapter07PrincipalDivisor, chapter03OrderOfVanishing] using
    (chapter03_principalWeilDivisor_coeff f P)

theorem chapter07_principal_divisor_mul
    {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Chapter03Normal X]
    (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    chapter07PrincipalDivisor (f * g) =
      chapter07PrincipalDivisor f + chapter07PrincipalDivisor g := by
  simpa [chapter07PrincipalDivisor] using
    (chapter03_principalWeilDivisor_mul f g hf hg)

noncomputable def chapter07PointDivisor {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) :
    Chapter07WeilDivisor X := by
  exact chapter03PrimeDivisorCycle P 1

/- The canonical divisor is the actual Cartier divisor attached by Chapter 4
   to a rational section of the differential line bundle.  Its data retains
   the local equations and bundle comparison supplied by that construction. -/
abbrev Chapter07CanonicalDivisorData
    {X : Scheme.{u}} [IsIntegral X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter07LineBundle X)
    (η : Chapter07RationalDifferential L) :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04DivisorOfRationalSectionData
    (chapter07AsChapter04LineBundle L) η

theorem chapter07_canonical_divisor_data_exists
    {X : Scheme.{u}} [IsIntegral X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter07LineBundle X)
    (η : Chapter07RationalDifferential L) :
    Nonempty (Chapter07CanonicalDivisorData L η) := by
  sorry

noncomputable def chapter07CanonicalDivisorData
    {X : Scheme.{u}} [IsIntegral X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter07LineBundle X)
    (η : Chapter07RationalDifferential L) : Chapter07CanonicalDivisorData L η :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04DivisorOfRationalSectionData
    (chapter07AsChapter04LineBundle L) η

noncomputable def chapter07CanonicalDivisor
    {X : Scheme.{u}} [IsIntegral X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter07LineBundle X)
    (η : Chapter07RationalDifferential L) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04CartierDivisor X :=
  (chapter07CanonicalDivisorData L η).divisor

def chapter07CanonicalDivisorClass
    {X : Scheme.{u}} [IsIntegral X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter07LineBundle X) : Set
      (LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04CartierDivisor X) :=
  {D | ∃ η, chapter07CanonicalDivisor L η = D}

theorem chapter07_canonical_divisor_is_attached_to_rational_section
    {X : Scheme.{u}} [IsIntegral X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI X]
    (L : Chapter07LineBundle X)
    (η : Chapter07RationalDifferential L) :
    chapter07CanonicalDivisor L η =
      LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04DivisorOfRationalSection
        (chapter07AsChapter04LineBundle L) η := by
  sorry

class Chapter07DegreeTheory (X : Scheme.{u}) where
  degree : Chapter07LineBundle X → ℤ

def chapter07LineBundleDegree {X : Scheme.{u}} [Chapter07DegreeTheory X]
    (L : Chapter07LineBundle X) : ℤ :=
  Chapter07DegreeTheory.degree L

class Chapter07GenusTheory
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)}
    (C : Chapter07SmoothProperGeometricallyConnectedCurve k X f) where
  genus : ℕ

/- This is the book-facing degree/genus statement. Its proof belongs to the
later Riemann--Roch and duality chapters, so Chapter 7 records the target
proposition without asserting it under arbitrary placeholder theories. -/
def chapter07CanonicalBundleDegreeFormula
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)}
    (C : Chapter07SmoothProperGeometricallyConnectedCurve k X f)
    [Chapter07DegreeTheory X]
    [Chapter07GenusTheory C] :
    Prop :=
    chapter07LineBundleDegree (chapter07CanonicalBundleOfCurve C) =
      (2 : ℤ) * Chapter07GenusTheory.genus C - 2

/- The Chapter 2 twisting line is the actual `𝒪(1)` on projective space.  The
integer twist below uses tensor powers for nonnegative exponents and the
actual Chapter 4 dual line bundle for negative exponents. -/
noncomputable def chapter07ProjectiveSpaceOOneChapter04
    (k : Type u) [Field k] (r : ℕ) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04LineBundle
      (chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of k)) r) :=
  { sheaf :=
      (chapter02ProjectiveSpaceTwistingLine
        (AlgebraicGeometry.Spec (CommRingCat.of k)) r).carrier
    isInvertible := by sorry }

noncomputable def chapter07ProjectiveSpaceTwistChapter04
    (k : Type u) [Field k] (r : ℕ) (m : ℤ) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04LineBundle
      (chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of k)) r) :=
  if _h : 0 ≤ m then
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04LineBundleTensorPower
      (chapter07ProjectiveSpaceOOneChapter04 k r) m.toNat
  else
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04DualLineBundle
      (LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04LineBundleTensorPower
        (chapter07ProjectiveSpaceOOneChapter04 k r) (-m).toNat)

noncomputable def chapter07ProjectiveLineOminusTwo
    (k : Type u) [Field k] : Chapter07LineBundle (chapter04ProjectiveLine k) :=
  chapter07OfChapter04LineBundle
    (chapter07ProjectiveSpaceTwistChapter04 k 1 (-2 : ℤ))

theorem chapter07_projective_line_differential_divisor
    (k : Type u) [Field k]
    [IsIntegral (chapter04ProjectiveLine k)]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI
      (chapter04ProjectiveLine k)]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04RationalFunctionLocalValueAPI
      (chapter04ProjectiveLine k)]
    (η : Chapter07RationalDifferential (chapter07ProjectiveLineOminusTwo k)) :
    chapter07CanonicalDivisor (chapter07ProjectiveLineOminusTwo k) η =
      LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04DivisorOfRationalSection
        (chapter07AsChapter04LineBundle (chapter07ProjectiveLineOminusTwo k)) η := by
  sorry

structure Chapter07ProjectiveLineCoordinateChangeData
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  t : K
  u : K
  dt : V
  du : V
  u_mul_t : u * t = 1
  differential_formula : dt = -(u⁻¹) ^ 2 • du

theorem chapter07_projective_line_affine_coordinate_change
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (P : Chapter07ProjectiveLineCoordinateChangeData K V) :
    P.dt = -(P.u⁻¹) ^ 2 • P.du :=
  P.differential_formula

theorem chapter07_projective_line_differential_formula_at_infinity
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (P : Chapter07ProjectiveLineCoordinateChangeData K V) :
    P.dt = -(P.u⁻¹) ^ 2 • P.du :=
  P.differential_formula

theorem chapter07_projective_line_canonical_bundle_is_minus_two
    (k : Type u) [Field k]
    [SmoothOfRelativeDimension 1 (chapter04ProjectiveLineStructureMap k)] :
    chapter09LineBundleIsomorphic
      (chapter07CanonicalBundle (chapter04ProjectiveLineStructureMap k))
      (chapter07ProjectiveLineOminusTwo k) := by
  sorry

structure Chapter07SmoothPlaneCurve
    (k : Type u) [Field k] (n : ℕ) where
  curve : Scheme.{u}
  structureMap : curve ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)
  embedding : curve ⟶ chapter02ProjectiveSpace (AlgebraicGeometry.Spec (CommRingCat.of k)) 2
  embedding_over :
    embedding ≫ chapter02ProjectiveSpaceProjection
        (AlgebraicGeometry.Spec (CommRingCat.of k)) 2 = structureMap
  embedding_closedImmersion : IsClosedImmersion embedding
  equation : MvPolynomial (Fin 3) k
  equation_homogeneous : equation.IsHomogeneous n
  equationIdealData : Chapter02HomogeneousIdealData
    (chapter02PolynomialGradedAlgebra k 2)
  equationIdeal_eq : equationIdealData.ideal = Ideal.span {equation}
  curve_is_equation_locus :
    Nonempty (curve ≅ chapter02VPlus equationIdealData)
  equationDegree : ℕ
  equationDegree_eq : equationDegree = n
  smooth : SmoothOfRelativeDimension 1 structureMap

theorem chapter07_smooth_plane_curve_is_geometrically_a_curve
    (k : Type u) [Field k] (n : ℕ)
    (C : Chapter07SmoothPlaneCurve k n) :
    SmoothOfRelativeDimension 1 C.structureMap :=
  C.smooth

noncomputable def chapter07PlaneCurveCanonicalBundle
    (k : Type u) [Field k] {n : ℕ} (C : Chapter07SmoothPlaneCurve k n) :
    Chapter07LineBundle C.curve := by
  letI : SmoothOfRelativeDimension 1 C.structureMap := C.smooth
  exact chapter07CanonicalBundle C.structureMap

noncomputable def chapter07PlaneCurveTwist
    (k : Type u) [Field k] {n : ℕ} (C : Chapter07SmoothPlaneCurve k n)
    (m : ℤ) : Chapter07LineBundle C.curve :=
  chapter07OfChapter04LineBundle
    (LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04PullbackLineBundle C.embedding
      (chapter07ProjectiveSpaceTwistChapter04 k 2 m))

structure Chapter07PlaneCurveAdjunctionData
    (k : Type u) [Field k] (n : ℕ)
    (C : Chapter07SmoothPlaneCurve k n) where
  canonical : Chapter07LineBundle C.curve
  canonical_iso_differential :
    chapter09LineBundleIsomorphic canonical (chapter07PlaneCurveCanonicalBundle k C)
  adjunction_iso :
    chapter09LineBundleIsomorphic canonical
      (chapter07PlaneCurveTwist k C ((n : ℤ) - 3))
  twist_zero_iso : n = 3 →
    chapter09LineBundleIsomorphic
      (chapter07PlaneCurveTwist k C ((n : ℤ) - 3))
      (chapter09StructureSheafLineBundle C.curve)

theorem chapter07_smooth_plane_curve_adjunction
    (k : Type u) [Field k] (n : ℕ)
    (C : Chapter07SmoothPlaneCurve k n) :
    Nonempty (Chapter07PlaneCurveAdjunctionData k n C) := by
  sorry

theorem chapter07_smooth_cubic_has_trivial_canonical_bundle
    (k : Type u) [Field k]
    (C : Chapter07SmoothPlaneCurve k 3)
    :
    Nonempty (Chapter09LineBundleIso
      (chapter07PlaneCurveCanonicalBundle k C)
      (chapter09StructureSheafLineBundle C.curve)) := by
  let D := chapter07_smooth_plane_curve_adjunction k 3 C
  obtain ⟨D⟩ := D
  obtain ⟨c⟩ := D.canonical_iso_differential
  obtain ⟨e⟩ := D.adjunction_iso
  obtain ⟨z⟩ := D.twist_zero_iso rfl
  exact ⟨{ hom := c.hom.symm ≪≫ e.hom ≪≫ z.hom }⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
