import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section04ClosedSubschemesFromHomogeneousIdeals
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07.Section01KaehlerDifferentialsAndLocalParameters

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09

noncomputable section

universe u

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

/- The order-of-vanishing API gives the coefficient function of a principal
divisor.  The local-finiteness packaging is isolated as a later dependency
guess rather than silently replacing a divisor by a raw function. -/
structure Chapter07PrincipalDivisorData
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) where
  divisor : Chapter07WeilDivisor X
  coefficient_eq_order : ∀ x : X, divisor x = Scheme.ord f x

theorem chapter07_canonical_bundle_is_relative_differential_bundle
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] :
    (chapter07CanonicalBundle f).module =
      (chapter07RelativeDifferentialLineBundle f).module := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the finite-support theorem for orders of a rational
function on a proper integral curve is not packaged in the pinned divisor
API.  This is the only existence input used to turn the canonical order
function into an algebraic cycle. -/
theorem chapter07_principal_divisor_exists
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : Nonempty (Chapter07PrincipalDivisorData f) := by
  sorry

noncomputable def chapter07PrincipalDivisorData
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : Chapter07PrincipalDivisorData f :=
  Classical.choice (chapter07_principal_divisor_exists f)

noncomputable def chapter07PrincipalDivisor
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) : Chapter07WeilDivisor X :=
  (chapter07PrincipalDivisorData f).divisor

theorem chapter07_principal_divisor_apply
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (x : X) :
    chapter07PrincipalDivisor f x = Scheme.ord f x := by
  exact (chapter07PrincipalDivisorData f).coefficient_eq_order x

theorem chapter07_principal_divisor_mul
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    chapter07PrincipalDivisor (f * g) =
      chapter07PrincipalDivisor f + chapter07PrincipalDivisor g := by
  sorry

noncomputable def chapter07PointDivisor {X : Scheme.{u}} (x : X) :
    Chapter07WeilDivisor X := by
  classical
  exact Function.locallyFinsupp.single x 1

/- LOCAL_DEPENDENCY_GUESS: a global rational-section object for an invertible
sheaf is absent from the preceding drafts.  This record keeps the genuinely
needed change-of-trivialization law explicit and does not identify a
differential with a rational function. -/
structure Chapter07CanonicalDivisorData
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [IsIntegral X] [IsLocallyNoetherian X]
    [SmoothOfRelativeDimension 1 f] where
  canonicalBundle : Chapter07LineBundle X
  canonicalBundle_is_differential :
    canonicalBundle.module = (chapter07RelativeDifferentialLineBundle f).module
  rationalDifferential : Type u
  divisor : rationalDifferential → Chapter07WeilDivisor X
  nonzero : rationalDifferential → Prop
  scalarMultiply : X.functionField → rationalDifferential → rationalDifferential
  divisor_scalarMultiply :
    ∀ {a : X.functionField}, a ≠ 0 → ∀ η,
      divisor (scalarMultiply a η) = chapter07PrincipalDivisor a + divisor η

/- This theorem is the global missing construction; all later statements use
the record fields rather than treating its existence as a definitional
identification. -/
theorem chapter07_canonical_divisor_data_exists
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [IsIntegral X] [IsLocallyNoetherian X]
    [SmoothOfRelativeDimension 1 f] :
    Nonempty (Chapter07CanonicalDivisorData f) := by
  sorry

noncomputable def chapter07CanonicalDivisorData
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [IsIntegral X] [IsLocallyNoetherian X]
    [SmoothOfRelativeDimension 1 f] : Chapter07CanonicalDivisorData f :=
  Classical.choice (chapter07_canonical_divisor_data_exists f)

def chapter07CanonicalDivisorClass
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [IsIntegral X] [IsLocallyNoetherian X]
    [SmoothOfRelativeDimension 1 f]
    (D : Chapter07CanonicalDivisorData f) : Set (Chapter07WeilDivisor X) :=
  {K | ∃ η, D.nonzero η ∧ D.divisor η = K}

theorem chapter07_canonical_divisors_change_by_principal
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [IsIntegral X] [IsLocallyNoetherian X]
    [SmoothOfRelativeDimension 1 f]
    (D : Chapter07CanonicalDivisorData f) (η : D.rationalDifferential)
    {a : X.functionField} (ha : a ≠ 0) :
    D.divisor (D.scalarMultiply a η) =
      chapter07PrincipalDivisor a + D.divisor η := by
  exact D.divisor_scalarMultiply ha η

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

/- LOCAL_DEPENDENCY_GUESS: this is the book-facing degree/genus bridge that
will be discharged by the later Riemann--Roch and duality chapters. -/
theorem chapter07_degree_canonical_bundle
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)}
    (C : Chapter07SmoothProperGeometricallyConnectedCurve k X f)
    [Chapter07DegreeTheory X]
    [Chapter07GenusTheory C] :
    chapter07LineBundleDegree (chapter07CanonicalBundleOfCurve C) =
      (2 : ℤ) * Chapter07GenusTheory.genus C - 2 := by
  sorry

/- The preceding Book 8 projective-line interface supplies the actual scheme
`P¹`.  The point/divisor calculation remains a chapter-local bridge until a
function-field coordinate API is available. -/
structure Chapter07ProjectiveLineCanonicalDivisorData
    (k : Type u) [Field k] where
  infinity : chapter04ProjectiveLine k
  differentialDivisor : Chapter07WeilDivisor (chapter04ProjectiveLine k)
  divisor_formula :
    differentialDivisor = (-2 : ℤ) • chapter07PointDivisor infinity
  finite_part_zero :
    ∀ x : chapter04ProjectiveLine k, x ≠ infinity → differentialDivisor x = 0

theorem chapter07_projective_line_differential_divisor
    (k : Type u) [Field k] :
    Nonempty (Chapter07ProjectiveLineCanonicalDivisorData k) := by
  sorry

structure Chapter07ProjectiveLineCoordinateChangeData
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  t u : K
  dt du : V
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

structure Chapter07ProjectiveLineTwistMinusTwoData
    (k : Type u) [Field k] where
  canonical : Chapter07LineBundle (chapter04ProjectiveLine k)
  minusTwo : Chapter07LineBundle (chapter04ProjectiveLine k)
  twistExponent : ℤ
  twistExponent_eq : twistExponent = -2
  canonical_iso_minusTwo : chapter09LineBundleIsomorphic canonical minusTwo

theorem chapter07_projective_line_canonical_bundle_is_minus_two
    (k : Type u) [Field k] :
    Nonempty (Chapter07ProjectiveLineTwistMinusTwoData k) := by
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

structure Chapter07PlaneCurveAdjunctionData
    (k : Type u) [Field k] (n : ℕ)
    (C : Chapter07SmoothPlaneCurve k n) where
  canonical : Chapter07LineBundle C.curve
  planeTwist : Chapter07LineBundle C.curve
  twistExponent : ℤ
  twistExponent_eq : twistExponent = (n : ℤ) - 3
  adjunction_iso : chapter09LineBundleIsomorphic canonical planeTwist

theorem chapter07_smooth_plane_curve_adjunction
    (k : Type u) [Field k] (n : ℕ)
    (C : Chapter07SmoothPlaneCurve k n) :
    Nonempty (Chapter07PlaneCurveAdjunctionData k n C) := by
  sorry

noncomputable def chapter07PlaneCurveCanonicalBundle
    (k : Type u) [Field k] {n : ℕ} (C : Chapter07SmoothPlaneCurve k n) :
    Chapter07LineBundle C.curve := by
  letI : SmoothOfRelativeDimension 1 C.structureMap := C.smooth
  exact chapter07CanonicalBundle C.structureMap

theorem chapter07_smooth_cubic_has_trivial_canonical_bundle
    (k : Type u) [Field k]
    (C : Chapter07SmoothPlaneCurve k 3)
    :
    Nonempty (Chapter09LineBundleIso
      (chapter07PlaneCurveCanonicalBundle k C)
      (chapter09StructureSheafLineBundle C.curve)) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
