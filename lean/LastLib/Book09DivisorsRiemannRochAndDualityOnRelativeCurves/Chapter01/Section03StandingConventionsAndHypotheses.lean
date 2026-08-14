import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Length
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section04UniversalDivisorOnASmoothCurve
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section02DimensionOneAsAMeetingPoint

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ### Standing conventions and hypotheses -/

def chapter01StructureSheaf {X : Scheme.{u}} : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def chapter01StructureSheafCohomologyDimensionData
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier) : Prop :=
  chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)

def chapter01GlobalFunctions {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) : Type u :=
  Γ(C.carrier, ⊤)

structure Chapter01GeometricallyConnectedReducedCurve
    (k : Type u) [Field k] (C : Chapter01ProperCurveOverField k) where
  geometricallyConnected : GeometricallyConnected C.structureMap
  geometricallyReduced : GeometricallyReduced C.structureMap

theorem chapter01_globalFunctions_eq_baseField
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (H : Chapter01GeometricallyConnectedReducedCurve k C) :
    Nonempty (chapter01GlobalFunctions C ≃+* k) := by
  sorry

theorem chapter01_h0_structureSheaf_eq_one
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules))
    (H : Chapter01GeometricallyConnectedReducedCurve k C) :
    chapter01h0 D chapter01StructureSheaf hO = 1 := by
  sorry

def chapter01ArithmeticGenus {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)) : ℤ :=
  1 - chapter01Chi D chapter01StructureSheaf hO

def chapter01ArithmeticGenusAsH1 {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)) : ℕ :=
  chapter01h1 D chapter01StructureSheaf hO

theorem chapter01_arithmeticGenus_eq_h1
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules))
    (hH0 : chapter01h0 D chapter01StructureSheaf hO = 1) :
    chapter01ArithmeticGenus C D hO = chapter01ArithmeticGenusAsH1 C D hO := by
  sorry

/- No algebraic closure is built into the definition of a curve.  Residue-field
  degrees are part of the degree convention. -/
def chapter01ClosedPointDegree {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) (x : C.carrier) : ℕ := by
  letI : Algebra k (C.carrier.residueField x) :=
    (C.structureMap.residueFieldMap x).hom.toAlgebra
  exact Module.finrank k (C.carrier.residueField x)

def chapter01DegreeWithResidueFieldFactors {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) (E : Finset C.carrier) : ℕ :=
  ∑ x in E, chapter01ClosedPointDegree C x

structure Chapter01NoetherianRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    extends Chapter01RelativeCurve f : Prop where
  baseLocallyNoetherian : IsLocallyNoetherian S

structure Chapter01ProjectiveRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    extends Chapter01NoetherianRelativeCurve f : Prop where
  projective : Chapter08IsProjective f

def chapter01RelativeFinitenessHypotheses {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01RelativeCurve f ∧ IsLocallyNoetherian S

def chapter01ProjectiveRelativeHypothesis {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter08IsProjective f

/-! Book 8's numerical and Hilbert-polynomial APIs are the canonical inputs for the
  later relative statements.  The aliases below keep the dependency visible at the
  chapter boundary without re-defining those constructions. -/
abbrev Chapter01Book08NumericalPolynomial := Chapter08NumericalPolynomial
abbrev Chapter01Book08ProjectiveFamily := Chapter08ProjectiveFamily
abbrev Chapter01Book08RelativeScheme := RelativeScheme
abbrev Chapter01Book08RelativeEffectiveCartierDivisor := RelativeEffectiveCartierDivisor

abbrev Chapter01Book08UniversalDivisorRepresentation
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :=
  Chapter11UniversalDivisorRepresentingData C d

structure Chapter01Book08ProjectiveInput {X S : Scheme.{u}} (f : X ⟶ S) where
  projective : Chapter08IsProjective f
  locallyNoetherian : IsLocallyNoetherian S

def chapter01Book08EulerConstancyInput {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01Book08ProjectiveInput f

def chapter01Book08UniversalDivisorInput (S : Scheme.{u}) : Prop :=
  ∀ (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C],
    Chapter11FiniteLocallyFreeOfRank
      ((universalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d

noncomputable def chapter01Book08UniversalDivisor
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    EffectiveCartierDivisor (curveSymmetricAmbient C d) :=
  universalDivisor C d

noncomputable def chapter01Book08UniversalDivisorRepresentation
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter01Book08UniversalDivisorRepresentation C d :=
  universalDivisorRepresentingData C d

theorem chapter01_book08_universalDivisor_has_constant_length
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11FiniteLocallyFreeOfRank
      ((universalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d := by
  exact universalDivisor_finiteLocallyFree C d

/-! The normalization and length conventions are named explicitly for use by the
  divisor and exact-sequence chapters. -/
structure Chapter01NormalizedValuation (R : Type u) [CommRing R] where
  valuation : R → ℤ
  valuation_zero : valuation 0 = 0
  valuation_mul : ∀ a b, valuation (a * b) = valuation a + valuation b
  uniformizer_value : ∀ t, chapter01LocalParameter t → valuation t = 1

def chapter01ModuleLength {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R M

theorem chapter01_length_is_module_length {R M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] : chapter01ModuleLength = Module.length R M := by
  rfl

theorem chapter01_normal_local_domain_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  exact chapter01_normal_oneDimensional_local_isDVR hnormal hdim

theorem chapter01_regular_local_is_factorial
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by
  exact chapter01_regular_local_ring_is_factorial

/-! A cohomology profile records exactly the finiteness and dimension-one vanishing
  used in the definition of ``h^i`` and ``χ``. -/
structure Chapter01ProperCurveFinitenessProfile
    (k : Type u) [Field k] (C : Chapter01ProperCurveOverField k) where
  dimensions : Chapter01CohomologyDimensions k C.carrier
  coherentStructureSheaf :
    chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)
  vanishingAboveOne :
    chapter01CohomologyVanishesAboveOne (chapter01StructureSheaf : C.carrier.Modules)

theorem chapter01_proper_curve_coherent_cohomology_is_finite_dimensional
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveFinitenessProfile k C)
    (F : C.carrier.Modules) (hF : chapter04FiniteTypeQuasiCoherent F) (i : ℕ) :
    ∃ V : Type u, ∃ (_ : AddCommGroup V) (_ : Module k V),
      FiniteDimensional k V ∧
        Nonempty (V ≃+ chapter01CohomologyGroup F i) := by
  let R := H.dimensions.realization F hF i
  letI := R.addCommGroup
  letI := R.module
  exact ⟨R.V, inferInstance, inferInstance, R.finite, ⟨R.addEquiv⟩⟩

theorem chapter01_proper_curve_coherent_cohomology_vanishes_above_one
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveFinitenessProfile k C) :
    chapter01CohomologyVanishesAboveOne
      (chapter01StructureSheaf : C.carrier.Modules) := by
  exact H.vanishingAboveOne

/-! The relative two-term presentation has two independent numerical behaviours:
  kernel and cokernel ranks may vary, while the index is locally constant under the
  projective/flat hypotheses supplied by the preceding book. -/
structure Chapter01RelativeCohomologyIndexProfile (S : Type u) where
  h₀ h₁ : S → ℕ
  χ : S → ℤ
  chi_formula : ∀ s, χ s = (h₀ s : ℤ) - h₁ s
  h₀MayJump : chapter01RankFunctionMayJump h₀
  h₁MayJump : chapter01RankFunctionMayJump h₁
  chiLocallyConstant : IsLocallyConstant χ

theorem chapter01_relative_euler_characteristic_is_locally_constant
    {S : Type u} (P : Chapter01RelativeCohomologyIndexProfile S) :
    IsLocallyConstant P.χ := by
  exact P.chiLocallyConstant

/-! These are the exact theorem-level hypotheses used whenever properness is upgraded
  to projectivity in the relative arguments. -/
structure Chapter01RelativeRiemannRochHypotheses {X S : Scheme.{u}} (f : X ⟶ S) where
  relativeCurve : Chapter01RelativeCurve f
  baseLocallyNoetherian : IsLocallyNoetherian S
  projectiveWhenRequired : Chapter08IsProjective f

def chapter01RelativeStatementNeedsProjectivity {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter08IsProjective f

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
