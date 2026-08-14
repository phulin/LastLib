import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped BigOperators

noncomputable section

/-! §5.1. Degree over a field. -/

theorem chapter05_principal_divisor_degree_zero
    (C : Chapter05ProperRegularIntegralCurve k)
    (g : C.carrier.functionField)
    (P : Chapter05PrincipalDivisorData g) :
    chapter05Degree C.structureMap P.divisor = 0 := by
  sorry

/-! The proof through a finite map to `ℙ¹` uses the common length of the zero
and pole fibers.  The pullback squares make the two fibers genuine scheme
fibers, while the divisor fields retain the Weil-divisor comparison used by
the degree calculation. -/

structure Chapter05RationalFunctionFiberLengthData
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField)
    (W : Chapter05RationalFunctionMapData C g)
    (P : Chapter05PrincipalDivisorData g) where
  zeroPoint : Spec (.of k) ⟶ chapter04ProjectiveLine k
  polePoint : Spec (.of k) ⟶ chapter04ProjectiveLine k
  zeroFiber : Scheme
  zeroFiberInclusion : zeroFiber ⟶ C.carrier
  zeroFiberMap : zeroFiber ⟶ Spec (.of k)
  zeroFiberPullback :
    IsPullback zeroFiberInclusion zeroFiberMap W.map zeroPoint
  poleFiber : Scheme
  poleFiberInclusion : poleFiber ⟶ C.carrier
  poleFiberMap : poleFiber ⟶ Spec (.of k)
  poleFiberPullback :
    IsPullback poleFiberInclusion poleFiberMap W.map polePoint
  fiberRank : ℕ
  zeroFiberFiniteLocallyFree :
    Chapter05FiniteLocallyFreeProfile zeroFiberMap fiberRank
  poleFiberFiniteLocallyFree :
    Chapter05FiniteLocallyFreeProfile poleFiberMap fiberRank
  zeroDivisor : Chapter05Divisor C.carrier
  poleDivisor : Chapter05Divisor C.carrier
  principal_as_zero_minus_pole :
    P.divisor.coeff = zeroDivisor.coeff - poleDivisor.coeff
  zero_degree_eq_fiber_rank :
    chapter05Degree C.structureMap zeroDivisor = fiberRank
  pole_degree_eq_fiber_rank :
    chapter05Degree C.structureMap poleDivisor = fiberRank

theorem chapter05_finite_rational_function_map_is_flat
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField)
    (W : Chapter05RationalFunctionMapData C g) :
    Flat W.map := by
  sorry

theorem chapter05_torsion_free_module_over_dvr_is_flat
    {A M : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [AddCommMonoid M] [Module A M]
    (htorsionFree : NoZeroSMulDivisors A M) :
    Module.Flat A M := by
  sorry

theorem chapter05_zero_and_pole_fiber_lengths_agree
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField)
    (W : Chapter05RationalFunctionMapData C g)
    (P : Chapter05PrincipalDivisorData g)
    (H : Chapter05RationalFunctionFiberLengthData C g W P) :
    Chapter10FiberLength H.zeroFiberMap (IsLocalRing.closedPoint k) =
      Chapter10FiberLength H.poleFiberMap (IsLocalRing.closedPoint k) := by
  sorry

theorem chapter05_principal_degree_from_zero_and_pole_fibers
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (g : C.carrier.functionField)
    (W : Chapter05RationalFunctionMapData C g)
    (P : Chapter05PrincipalDivisorData g)
    (H : Chapter05RationalFunctionFiberLengthData C g W P) :
    chapter05Degree C.structureMap P.divisor = 0 := by
  sorry

theorem chapter05_constant_principal_divisor_degree_zero
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05FunctionFieldBaseAlgebra C]
    (a : k)
    (P : Chapter05PrincipalDivisorData
      (algebraMap k C.carrier.functionField a)) :
    chapter05Degree C.structureMap P.divisor = 0 := by
  sorry

def chapter05LineBundleEquivalent {X : Scheme}
    (L M : Chapter05LineBundle X) : Prop :=
  Nonempty (Chapter05LineBundleIso L M)

theorem chapter05_lineBundleEquivalent_refl {X : Scheme}
    (L : Chapter05LineBundle X) : chapter05LineBundleEquivalent L L := by
  exact ⟨chapter10_lineBundleIso_refl L⟩

theorem chapter05_lineBundleEquivalent_symm {X : Scheme}
    {L M : Chapter05LineBundle X} :
    chapter05LineBundleEquivalent L M → chapter05LineBundleEquivalent M L := by
  rintro ⟨h⟩
  exact ⟨chapter10_lineBundleIso_symm h⟩

theorem chapter05_lineBundleEquivalent_trans {X : Scheme}
    {L M N : Chapter05LineBundle X} :
    chapter05LineBundleEquivalent L M →
      chapter05LineBundleEquivalent M N →
        chapter05LineBundleEquivalent L N := by
  rintro ⟨hLM⟩ ⟨hMN⟩
  exact ⟨chapter10_lineBundleIso_trans hLM hMN⟩

def chapter05LineBundleEquivalenceSetoid (X : Scheme) :
    Setoid (Chapter05LineBundle X) :=
  { r := chapter05LineBundleEquivalent
    iseqv :=
      { refl := chapter05_lineBundleEquivalent_refl
        symm := chapter05_lineBundleEquivalent_symm
        trans := chapter05_lineBundleEquivalent_trans } }

abbrev Chapter05LineBundlePicard (X : Scheme) :=
  Quotient (chapter05LineBundleEquivalenceSetoid X)

theorem chapter05_lineBundleDegree_respects_isomorphism
    {X : Scheme} [Chapter05EulerCharacteristicTheory X]
    {L M : Chapter05LineBundle X}
    (hLM : chapter05LineBundleEquivalent L M) :
    chapter05LineBundleDegree L = chapter05LineBundleDegree M := by
  sorry

noncomputable def chapter05LineBundleDegreeOnPicard
    {X : Scheme} [Chapter05EulerCharacteristicTheory X] :
    Chapter05LineBundlePicard X → ℤ :=
  Quotient.lift chapter05LineBundleDegree (by
    intro L M hLM
    exact chapter05_lineBundleDegree_respects_isomorphism hLM)

theorem chapter05_lineBundleDegreeOnPicard_mk
    {X : Scheme} [Chapter05EulerCharacteristicTheory X]
    (L : Chapter05LineBundle X) :
    chapter05LineBundleDegreeOnPicard (Quotient.mk' L) =
      chapter05LineBundleDegree L := by
  rfl

/-! Degree is invariant under principal modification, hence it factors through
the divisor quotient used here as the book-facing Picard quotient. -/

theorem chapter05_degree_respects_linear_equivalence
    (C : Chapter05ProperRegularIntegralCurve k)
    (D E : Chapter05Divisor C.carrier)
    (hDE : chapter05LinearlyEquivalent D E) :
    chapter05Degree C.structureMap D = chapter05Degree C.structureMap E := by
  sorry

noncomputable def chapter05DegreeOnPicard
    (C : Chapter05ProperRegularIntegralCurve k) :
    Chapter05PicardQuotient C → ℤ :=
  Quotient.lift
    (fun D : Chapter05Divisor C.carrier => chapter05Degree C.structureMap D)
    (by
      intro D E hDE
      exact chapter05_degree_respects_linear_equivalence C D E hDE)

theorem chapter05_degreeOnPicard_mk
    (C : Chapter05ProperRegularIntegralCurve k)
    (D : Chapter05Divisor C.carrier) :
    chapter05DegreeOnPicard C (Quotient.mk' D) =
      chapter05Degree C.structureMap D := by
  rfl

/-! Formula (5.2) is the total degree on a possibly singular proper curve;
the regular integral divisor presentation identifies it with (5.1). -/

theorem chapter05_regular_divisor_degree_eq_euler_degree
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05EulerCharacteristicTheory C.carrier]
    (L : Chapter05LineBundle C.carrier)
    (P : Chapter05DivisorPresentation L) :
    chapter05LineBundleDegree L =
      chapter05Degree C.structureMap P.divisor := by
  sorry

theorem chapter05_total_degree_formula
    {X : Scheme} [Chapter05EulerCharacteristicTheory X]
    (L : Chapter05LineBundle X) :
    chapter05LineBundleDegree L =
      chapter05EulerCharacteristic L.module -
        chapter05EulerCharacteristic
          (chapter09StructureSheafLineBundle X).module := by
  rfl

structure Chapter05LineBundleMultidegreeProfile
    {X : Scheme} [Chapter05EulerCharacteristicTheory X]
    (L : Chapter05LineBundle X) (I : Type v) [Fintype I] where
  componentDegree : I → ℤ
  total_degree : ∑ i, componentDegree i = chapter05LineBundleDegree L

theorem chapter05_total_degree_is_sum_of_multidegrees
    {X : Scheme} [Chapter05EulerCharacteristicTheory X]
    (L : Chapter05LineBundle X) (I : Type v) [Fintype I]
    (H : Chapter05LineBundleMultidegreeProfile L I) :
    ∑ i, H.componentDegree i = chapter05LineBundleDegree L :=
  H.total_degree

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
