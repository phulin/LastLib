import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section05CurvesHilbertSchemeEqualsSymmetricPower

/-!
## 13.4 A boundary checklist

The declarations here keep the four distinctions in the source visible at the
type level: ordered tuples versus cycles versus embedded subschemes, a functor
versus its representing scheme and universal family, flatness versus geometric
fiber lengths, and a Hilbert polynomial together with its polarization.

-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

/-! ### Ordered tuples, cycles, and embedded finite subschemes -/

abbrev chapter13OrderedTupleParameter (X : Type*) (d : ℕ) :=
  chapter13OrderedTuple X d

abbrev chapter13CycleParameter (X : Type*) (d : ℕ) :=
  chapter13SymmetricPower X d

abbrev chapter13EmbeddedFiniteSubschemeParameter {S : Scheme}
    (X T : Chapter13RelativeScheme S) (d : ℕ) :=
  Chapter13FiniteLengthSubscheme X T d

abbrev chapter13EffectiveDivisorParameter {S : Scheme}
    (X T : Chapter13RelativeScheme S) (d : ℕ) :=
  Chapter13EffectiveDivisorFamily X T d

theorem chapter13_cycle_parameter_is_a_quotient (X : Type*) (d : ℕ) :
    chapter13CycleParameter X d = chapter13SymmetricPower X d := rfl

theorem chapter13_ordered_tuple_parameter_is_ordered_tuple (X : Type*) (d : ℕ) :
    chapter13OrderedTupleParameter X d = chapter13OrderedTuple X d := rfl

/-!
On a smooth curve the effective-divisor/symmetric-power functor agrees with
the finite-subscheme Hilbert functor.  The comparison is stated only with the
smooth proper curve hypothesis below; no such identification is asserted for
an arbitrary ambient scheme.
-/

structure Chapter13SmoothProperCurveData {S : Scheme}
    (X : Chapter13RelativeScheme S) where
  smooth : Smooth X.toBase
  proper : IsProper X.toBase
  relativeDimensionOne : SmoothOfRelativeDimension 1 X.toBase

structure Chapter13HilbertFiniteSubschemeData {S : Scheme}
    (X : Chapter13RelativeScheme S) (d : ℕ) where
  functor : Chapter13RelativePresheaf S
  familyPullback : {T U : Chapter13RelativeScheme S} →
    Chapter13RelativeMap T U →
      Chapter13FiniteLengthSubscheme X U d →
        Chapter13FiniteLengthSubscheme X T d
  familyPullback_id : ∀ {T : Chapter13RelativeScheme S}
    (x : Chapter13FiniteLengthSubscheme X T d),
    familyPullback (chapter13RelativeMapId T) x = x
  familyPullback_comp : ∀ {T U V : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (g : Chapter13RelativeMap U V)
    (x : Chapter13FiniteLengthSubscheme X V d),
    familyPullback f (familyPullback g x) =
      familyPullback (chapter13RelativeMapComp f g) x
  classifies : ∀ T : Chapter13RelativeScheme S,
    functor.obj T ≃ Chapter13FiniteLengthSubscheme X T d
  classifies_naturality : ∀ {T U : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (x : functor.obj U),
    classifies T (functor.map f x) =
      familyPullback f (classifies U x)
  represented : Chapter13RepresentedRelativePresheaf functor

/-- The natural comparison supplied by the smooth-curve divisor/Hilbert identification. -/
structure Chapter13SmoothCurvePresheafComparison {S : Scheme}
    (F G : Chapter13RelativePresheaf S) where
  comparison : ∀ T : Chapter13RelativeScheme S, F.obj T ≃ G.obj T
  naturality : ∀ {T U : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (x : F.obj U),
    comparison T (F.map f x) = G.map f (comparison U x)

/-- Yoneda's representative-isomorphism bridge for a natural presheaf comparison. -/
structure Chapter13CompatibleRepresentedPresheafComparison {S : Scheme}
    {F G : Chapter13RelativePresheaf S}
    (e : Chapter13SmoothCurvePresheafComparison F G)
    (RF : Chapter13RepresentedRelativePresheaf F)
    (RG : Chapter13RepresentedRelativePresheaf G) where
  representative_iso : Chapter13RelativeIso
    RF.representative RG.representative
  compatibility : ∀ (T : Chapter13RelativeScheme S) (x : F.obj T),
    RG.equiv T (e.comparison T x) =
      chapter13RelativeMapComp (RF.equiv T x) representative_iso.hom

theorem chapter13_smooth_curve_presheaf_comparison_has_representative_iso
    {S : Scheme} {F G : Chapter13RelativePresheaf S}
    (e : Chapter13SmoothCurvePresheafComparison F G)
    (RF : Chapter13RepresentedRelativePresheaf F)
    (RG : Chapter13RepresentedRelativePresheaf G) :
    Nonempty (Chapter13CompatibleRepresentedPresheafComparison e RF RG) := by
  sorry

def chapter13HilbertFiniteSubschemeParameterSpace {S : Scheme}
    {X : Chapter13RelativeScheme S} {d : ℕ}
    (H : Chapter13HilbertFiniteSubschemeData X d) :
    Chapter13RelativeScheme S :=
  H.represented.representative

def chapter13HilbertFiniteSubschemeUniversalFamily {S : Scheme}
    {X : Chapter13RelativeScheme S} {d : ℕ}
    (H : Chapter13HilbertFiniteSubschemeData X d) :
    Chapter13FiniteLengthSubscheme X H.represented.representative d :=
  H.classifies _ ((H.represented.equiv _).symm (chapter13RelativeMapId _))

structure Chapter13SmoothCurveSymmetricHilbertComparison {S : Scheme}
    (X : Chapter13RelativeScheme S) (d : ℕ) where
  curve : Chapter13SmoothProperCurveData X
  symmetric : Chapter13RelativeSymmetricPowerData X d
  hilbert : Chapter13HilbertFiniteSubschemeData X d
  comparison : ∀ T : Chapter13RelativeScheme S,
    symmetric.functor.obj T ≃ hilbert.functor.obj T
  comparison_naturality : ∀ {T U : Chapter13RelativeScheme S}
    (f : Chapter13RelativeMap T U) (x : symmetric.functor.obj U),
    comparison T (symmetric.functor.map f x) =
      hilbert.functor.map f (comparison U x)
  representative_iso : Chapter13RelativeIso
    symmetric.represented.representative hilbert.represented.representative
  representative_iso_compatibility : ∀ (T : Chapter13RelativeScheme S)
    (x : symmetric.functor.obj T),
    hilbert.represented.equiv T (comparison T x) =
      chapter13RelativeMapComp (symmetric.represented.equiv T x)
        representative_iso.hom

theorem chapter13_package_smooth_curve_symmetric_hilbert_comparison
    {S : Scheme} (X : Chapter13RelativeScheme S) (d : ℕ)
    (curve : Chapter13SmoothProperCurveData X)
    (symmetric : Chapter13RelativeSymmetricPowerData X d)
    (hilbert : Chapter13HilbertFiniteSubschemeData X d)
    (comparison : Chapter13SmoothCurvePresheafComparison
      symmetric.functor hilbert.functor) :
    Nonempty (Chapter13SmoothCurveSymmetricHilbertComparison X d) := by
  let e := Classical.choice
    (chapter13_smooth_curve_presheaf_comparison_has_representative_iso
      comparison symmetric.represented hilbert.represented)
  exact ⟨{
    curve := curve
    symmetric := symmetric
    hilbert := hilbert
    comparison := comparison.comparison
    comparison_naturality := comparison.naturality
    representative_iso := e.representative_iso
    representative_iso_compatibility := e.compatibility
  }⟩

/-! The canonical Chapter 12 construction supplies the actual comparison used
by the source theorem.  The custom records above are a packaging layer for the
Chapter 13 boundary checklist, while the theorem below exposes the earlier
representability result without assuming its conclusion as an argument. -/

theorem chapter13_smooth_curve_hilbert_equals_symmetric_power
    (C : Chapter12SmoothQuasiProjectiveCurve) (d : ℕ) :
    Nonempty (Chapter12RepresentingOverIso
      (chapter12CurveHilbertSchemeData C d).structureMap
      (chapter12SymmetricPowerMap C d)) := by
  exact chapter12_curve_hilbert_scheme_eq_symmetric_power C d

/-! ### Functor, representing scheme, and universal family -/

def chapter13HilbertPoint {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P)
    (T : Chapter13RelativeScheme S) : Type :=
  H.functor.obj T

def chapter13_hilbert_point_is_a_family {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P)
    (T : Chapter13RelativeScheme S)
    (z : chapter13HilbertPoint H T) :
    Chapter13FlatClosedFamily xS L P T := by
  exact H.classifies T z

def chapter13HilbertRepresentingScheme {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P) : Scheme :=
  chapter13HilbertScheme H

def chapter13HilbertUniversalFamily {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization xS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P) :
    Chapter13FlatClosedFamily xS L P H.represented.representative :=
  chapter13UniversalHilbertFamily H

def chapter13_hilbert_representing_scheme_has_universal_family
    {S X : Scheme} {xS : X ⟶ S} {L : Chapter13Polarization xS}
    {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData xS L P) :
    Chapter13FlatClosedFamily xS L P H.represented.representative := by
  exact chapter13HilbertUniversalFamily H

/-! ### Geometric fiber lengths versus flat families -/

/-- Constant finite rank data; flatness is deliberately not part of this predicate. -/
def chapter13GeometricFiberLengthOnly {Z T : Scheme}
    (p : Z ⟶ T) (d : ℕ) [IsFinite p] : Prop :=
  ∀ t : T, p.finrank t = d

/-- The family data needed in addition to geometric fiber lengths. -/
structure Chapter13FlatFinitePresentationFamily {Z T : Scheme}
    (p : Z ⟶ T) (d : ℕ) where
  [finite : IsFinite p]
  [flat : Flat p]
  fiberLength_eq : chapter13GeometricFiberLengthOnly p d
  finitePresentation : LocallyOfFinitePresentation p

theorem chapter13_flat_family_certificate_records_flatness_separately
    {Z T : Scheme} {p : Z ⟶ T} {d : ℕ}
    (F : Chapter13FlatFinitePresentationFamily p d) :
    Flat p ∧ LocallyOfFinitePresentation p := by
  exact ⟨F.flat, F.finitePresentation⟩

/-
SOURCE_NOTE: the warning that geometric fiber lengths do not detect nilpotent
base directions is mathematically about the failure of an implication.  The API
uses Mathlib's finite-flat rank for the length condition and keeps flatness and
finite presentation as explicit fields, rather than asserting a converse from
fiber data alone.
-/

/-! ### Polarization dependence -/

def chapter13PolarizedHilbertProblem {X S : Scheme} {f : X ⟶ S}
    (L : Chapter13Polarization f) (P : Chapter13NumericalPolynomial) :
    Chapter13PolarizedHilbertProblem f where
  polarization := L
  polynomial := P

theorem chapter13_polarized_hilbert_problem_remembers_polarization
    {X S : Scheme} {f : X ⟶ S} (L : Chapter13Polarization f)
    (P : Chapter13NumericalPolynomial) :
    (chapter13PolarizedHilbertProblem L P).polarization = L := rfl

theorem chapter13_polarized_hilbert_problem_remembers_polynomial
    {X S : Scheme} {f : X ⟶ S} (L : Chapter13Polarization f)
    (P : Chapter13NumericalPolynomial) :
    (chapter13PolarizedHilbertProblem L P).polynomial = P := rfl

/-
SOURCE_NOTE: the sentence that changing the polarization changes the moduli
problem is a warning about the input data, not a claim that two arbitrary
polarizations always yield unequal polynomials.  The record above makes the
polarization part of the problem and leaves comparison to later hypotheses.
-/

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
