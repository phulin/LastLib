import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13.Dependencies

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
  classifies : ∀ T : Chapter13RelativeScheme S,
    functor.obj T ≃ Chapter13FiniteLengthSubscheme X T d
  represented : Chapter13RepresentedRelativePresheaf functor

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

theorem chapter13_smooth_curve_symmetric_power_agrees_with_hilbert
    {S : Scheme} (X : Chapter13RelativeScheme S) (d : ℕ)
    (curve : Chapter13SmoothProperCurveData X)
    (symmetric : Chapter13RelativeSymmetricPowerData X d)
    (hilbert : Chapter13HilbertFiniteSubschemeData X d) :
    Nonempty (Chapter13SmoothCurveSymmetricHilbertComparison X d) := by
  sorry

/-! ### Functor, representing scheme, and universal family -/

def chapter13HilbertPoint {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization X} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData xS L P)
    (T : Chapter13RelativeScheme S) : Type :=
  H.functor.obj T

theorem chapter13_hilbert_point_is_a_family {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization X} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData xS L P)
    (T : Chapter13RelativeScheme S)
    (z : chapter13HilbertPoint H T) :
    Nonempty (Chapter13FlatClosedFamily xS L P T) := by
  exact ⟨H.classifies T z⟩

def chapter13HilbertRepresentingScheme {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization X} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData xS L P) : Scheme :=
  chapter13HilbertScheme H

def chapter13HilbertUniversalFamily {S X : Scheme} {xS : X ⟶ S}
    {L : Chapter13Polarization X} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData xS L P) :
    Chapter13FlatClosedFamily xS L P H.represented.representative :=
  chapter13UniversalHilbertFamily H

theorem chapter13_hilbert_representing_scheme_has_universal_family
    {S X : Scheme} {xS : X ⟶ S} {L : Chapter13Polarization X} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData xS L P) :
    Nonempty (Chapter13FlatClosedFamily xS L P H.represented.representative) := by
  exact ⟨chapter13HilbertUniversalFamily H⟩

/-! ### Geometric fiber lengths versus flat families -/

/-- A bare constant geometric-fiber-length assertion. -/
def chapter13GeometricFiberLengthOnly {Z T : Scheme}
    (_p : Z ⟶ T) (d : ℕ) (fiberLength : T → ℕ) : Prop :=
  ∀ t : T, fiberLength t = d

/-- The family data needed in addition to geometric fiber lengths. -/
structure Chapter13FlatFinitePresentationFamily {Z T : Scheme}
    (p : Z ⟶ T) (d : ℕ) where
  fiberLength : T → ℕ
  fiberLength_eq : chapter13GeometricFiberLengthOnly p d fiberLength
  flat : Flat p
  finitePresentation : LocallyOfFinitePresentation p

theorem chapter13_flat_family_certificate_records_flatness_separately
    {Z T : Scheme} {p : Z ⟶ T} {d : ℕ}
    (F : Chapter13FlatFinitePresentationFamily p d) :
    Flat p ∧ LocallyOfFinitePresentation p := by
  exact ⟨F.flat, F.finitePresentation⟩

/-
SOURCE_NOTE: the warning that geometric fiber lengths do not detect nilpotent
base directions is mathematically about the failure of an implication, not a
universal equality.  The API therefore keeps `chapter13GeometricFiberLengthOnly`
and `Chapter13FlatFinitePresentationFamily` as separate certificates instead
of asserting a false converse.
-/

/-! ### Polarization dependence -/

def chapter13PolarizedHilbertProblem {X : Scheme}
    (L : Chapter13Polarization X) (P : Polynomial ℤ) :
    Chapter13PolarizedHilbertProblem X where
  polarization := L
  polynomial := P

theorem chapter13_polarized_hilbert_problem_remembers_polarization
    {X : Scheme} (L : Chapter13Polarization X) (P : Polynomial ℤ) :
    (chapter13PolarizedHilbertProblem L P).polarization = L := rfl

theorem chapter13_polarized_hilbert_problem_remembers_polynomial
    {X : Scheme} (L : Chapter13Polarization X) (P : Polynomial ℤ) :
    (chapter13PolarizedHilbertProblem L P).polynomial = P := rfl

/-
SOURCE_NOTE: the sentence that changing the polarization changes the moduli
problem is a warning about the input data, not a claim that two arbitrary
polarizations always yield unequal polynomials.  The record above makes the
polarization part of the problem and leaves comparison to later hypotheses.
-/

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
