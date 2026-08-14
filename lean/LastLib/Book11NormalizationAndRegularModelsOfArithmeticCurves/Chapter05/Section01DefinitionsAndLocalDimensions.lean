import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

/-! ### 5.1 Definitions and local dimensions -/

theorem chapter05_excellentDedekind_affine_is_universallyCatenary
    {S : Scheme.{u}} (hS : Chapter05ExcellentDedekindScheme S)
    (U : S.affineOpens) :
    Chapter05UniversallyCatenary Γ(S, U) := by
  exact (hS.affine_isExcellent U).2.1

theorem chapter05_excellentDedekind_affine_is_catenary
    {S : Scheme.{u}} (hS : Chapter05ExcellentDedekindScheme S)
    (U : S.affineOpens) :
    Chapter05Catenary Γ(S, U) := by
  sorry

theorem chapter05_arithmeticSurface_finiteType
    {S X : Scheme.{u}} {f : X ⟶ S}
    (hX : Chapter05ArithmeticSurface S X f) :
    Chapter05FiniteTypeMorphism f :=
  hX.finiteType

theorem chapter05_arithmeticSurface_flat
    {S X : Scheme.{u}} {f : X ⟶ S}
    (hX : Chapter05ArithmeticSurface S X f) :
    Flat f :=
  hX.flat

theorem chapter05_arithmeticSurface_normal
    {S X : Scheme.{u}} {f : X ⟶ S}
    (hX : Chapter05ArithmeticSurface S X f) :
    Chapter05NormalScheme X :=
  hX.normal

theorem chapter05_arithmeticSurface_locallyNoetherian
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f) :
    IsLocallyNoetherian X := by
  sorry

/-! The dimension profile in the source is stratified by the generic point,
codimension-one points, and closed points over closed points. -/

theorem chapter05_genericPoint_localDimension_zero
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (x : X) (hx : Chapter05GenericPoint X x) :
    chapter05LocalDimension X x = (0 : WithBot ℕ∞) := by
  sorry

theorem chapter05_horizontalPrimeDivisor_localDimension_one
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (D : Chapter05PrimeDivisor X)
    (hD : chapter05PrimeDivisorHorizontal f D) :
    chapter05LocalDimension X D.point = (1 : WithBot ℕ∞) := by
  sorry

theorem chapter05_verticalFiberComponent_localDimension_one
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (x : X) (hx : Chapter05VerticalFiberComponentPoint f x) :
    chapter05LocalDimension X x = (1 : WithBot ℕ∞) := by
  sorry

theorem chapter05_closedPointOverClosedBase_localDimension_two
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (x : X) (hx : Chapter05ClosedPointOverClosedBasePoint f x) :
    chapter05LocalDimension X x = (2 : WithBot ℕ∞) := by
  sorry

theorem chapter05_normal_codimension_one_local_is_DVR
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (x : X) (hx : Chapter05PrimeDivisorPoint X x) :
    Chapter05IsDVRLocalRing (Chapter05LocalRing X x) := by
  sorry

/-! Orders of rational functions use Mathlib's canonical order of vanishing. -/

abbrev chapter05OrderAlongPrimeDivisor
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) (D : Chapter05PrimeDivisor X) : ℤ :=
  AlgebraicGeometry.Scheme.ord g D.point

theorem chapter05_orderAlongPrimeDivisor_eq_scheme_ord
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : X.functionField) (D : Chapter05PrimeDivisor X) :
    chapter05OrderAlongPrimeDivisor g D =
      AlgebraicGeometry.Scheme.ord g D.point :=
  rfl

theorem chapter05_orderAlongPrimeDivisor_mul
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (g h : X.functionField) (hg : g ≠ 0) (hh : h ≠ 0)
    (D : Chapter05PrimeDivisor X) :
    chapter05OrderAlongPrimeDivisor (g * h) D =
      chapter05OrderAlongPrimeDivisor g D + chapter05OrderAlongPrimeDivisor h D := by
  exact AlgebraicGeometry.Scheme.ord_mul hg hh

/-! Regularity is the extra two-parameter condition at closed surface points. -/

def Chapter05RegularArithmeticSurface
    {S X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter05RegularAtClosedPoints f

theorem chapter05_regularArithmeticSurface_iff_closedPoint_parameters
    {S X : Scheme.{u}} (f : X ⟶ S) :
    Chapter05RegularArithmeticSurface f ↔ Chapter05RegularAtClosedPoints f :=
  Iff.rfl

theorem chapter05_expected_dimension_chain_lengths_are_invariant
    (A : Type u) [CommRing A] (hA : Chapter05ExpectedDimensionProfile A)
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    (c d : Chapter03SaturatedPrimeChain A p q) :
    c.length = d.length := by
  exact chapter05_catenary_saturated_chain_length_unique A hA p q hpq c d

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05
