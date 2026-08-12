import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13.Dependencies

/-!
## 13.3 Projective parameter spaces for curve families

This section packages the fixed linear Hilbert polynomial, the universal
family, the open smooth/connected loci, the relative symmetric power for
marked divisors, and the bounded Hilbert setup for abelian families.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

/-- The polynomial `P(n) = e n + c` used for embedded curves. -/
def chapter13LinearHilbertPolynomial (e c : ℤ) : Polynomial ℤ :=
  Polynomial.C e * Polynomial.X + Polynomial.C c

theorem chapter13LinearHilbertPolynomial_eval (e c : ℤ) (n : ℕ) :
    (chapter13LinearHilbertPolynomial e c).eval (n : ℤ) = e * (n : ℤ) + c := by
  simp [chapter13LinearHilbertPolynomial, add_comm]

/-! ### Relative projective space and the Hilbert family -/

/-
LOCAL_DEPENDENCY_GUESS: `RelativeProjectiveSpaceData` supplies the missing
relative `\mathbf P^r_S` object and `hyperplane_is_ample` records the chosen
polarization normalization.  These fields are the intended replacement points
for the canonical projective-space API when it is available.
-/

structure Chapter13ProjectiveSpaceWithPolarization (S : Scheme) (r : ℕ) where
  projectiveSpace : Chapter13RelativeProjectiveSpaceData S r
  polarization : Chapter13Polarization projectiveSpace.scheme
  hyperplane_is_ample : Prop

structure Chapter13CurveHilbertSetup (S : Scheme) (r : ℕ) (e c : ℤ) where
  projective : Chapter13ProjectiveSpaceWithPolarization S r
  hilbert : Chapter13HilbertSchemeData
    projective.projectiveSpace.toBase projective.polarization
    (chapter13LinearHilbertPolynomial e c)

def chapter13CurveHilbertPolynomial (_D : Chapter13CurveHilbertSetup S r e c) :
    Polynomial ℤ :=
  chapter13LinearHilbertPolynomial e c

def chapter13CurveUniversalFamily (D : Chapter13CurveHilbertSetup S r e c) :
    Chapter13FlatClosedFamily
      D.projective.projectiveSpace.toBase D.projective.polarization
      (chapter13CurveHilbertPolynomial D)
      D.hilbert.represented.representative :=
  chapter13UniversalHilbertFamily D.hilbert

theorem chapter13_curve_hilbert_family_is_flat
    (D : Chapter13CurveHilbertSetup S r e c) :
    Flat (chapter13CurveUniversalFamily D).projection := by
  exact (chapter13CurveUniversalFamily D).flat

theorem chapter13_curve_hilbert_family_is_projective
    (D : Chapter13CurveHilbertSetup S r e c) :
    Chapter13ProjectiveMorphism (chapter13CurveUniversalFamily D).projection := by
  exact (chapter13CurveUniversalFamily D).projective

theorem chapter13_curve_hilbert_family_is_proper
    (D : Chapter13CurveHilbertSetup S r e c) :
    IsProper (chapter13CurveUniversalFamily D).projection := by
  exact (chapter13CurveUniversalFamily D).proper

/-! ### Smooth pure one-dimensional fibers -/

/-- The canonical relative-dimension-one formulation of smooth pure curve fibers. -/
def chapter13SmoothPureOneDimensionalFibers {Z T : Scheme} (p : Z ⟶ T) : Prop :=
  SmoothOfRelativeDimension 1 p

theorem chapter13SmoothPureOneDimensionalFibers_smooth {Z T : Scheme}
    {p : Z ⟶ T} (h : chapter13SmoothPureOneDimensionalFibers p) :
    Smooth p := by
  exact @SmoothOfRelativeDimension.smooth 1 Z T p h

def chapter13CurveHilbertFamilyAt {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) :
    Chapter13FlatClosedFamily aS L P T :=
  H.classifies T ((H.represented.equiv T).symm t)

def chapter13CurveHilbertFamilyIsSmoothCurve {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  chapter13SmoothPureOneDimensionalFibers
    (chapter13CurveHilbertFamilyAt H T t).projection

structure Chapter13SmoothCurveLocusData {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P) where
  locus : (chapter13HilbertScheme H).Opens
  represents : ∀ (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative),
    chapter13CurveHilbertFamilyIsSmoothCurve H T t ↔
      ∃ q : Chapter13RelativeMap T
          (chapter13OpenRelativeScheme H.represented.representative locus),
        q.map ≫ locus.ι = t.map

theorem chapter13_smooth_curve_locus_is_open {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P) :
    Nonempty (Chapter13SmoothCurveLocusData H) := by
  sorry

/-! ### Geometric connectedness -/

def chapter13CurveHilbertFamilyIsGeometricallyConnected {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  GeometricallyConnected (chapter13CurveHilbertFamilyAt H T t).projection

def chapter13GeometricallyConnectedCurveCondition {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  chapter13CurveHilbertFamilyIsSmoothCurve H T t ∧
    chapter13CurveHilbertFamilyIsGeometricallyConnected H T t

def chapter13GeometricallyConnectedCurveLocusCondition {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Scheme) (t : T ⟶ chapter13HilbertScheme H) : Prop :=
  chapter13GeometricallyConnectedCurveCondition H
    ⟨T, t ≫ chapter13HilbertSchemeToBase H⟩ ⟨t, rfl⟩

theorem chapter13_geometrically_connected_curve_locus_is_open {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P)
    (smooth : Chapter13SmoothCurveLocusData H) :
    Nonempty (Chapter13OpenLocusData (chapter13HilbertScheme H)
      (fun T t => chapter13GeometricallyConnectedCurveLocusCondition H T t)) := by
  sorry

/-! ### Marked effective divisors -/

/-- The universal curve viewed as a relative scheme over its Hilbert parameter scheme. -/
def chapter13UniversalCurveOverHilbertParameter {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P) :
    Chapter13RelativeScheme (chapter13HilbertScheme H) where
  scheme := (chapter13UniversalHilbertFamily H).scheme
  toBase := (chapter13UniversalHilbertFamily H).projection

/-- A symmetric-power parameter for marked effective divisors of degree `d`. -/
structure Chapter13MarkedEffectiveDivisorData {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    (H : Chapter13HilbertSchemeData aS L P) (d : ℕ) where
  symmetricPower : Chapter13RelativeSymmetricPowerData
    (chapter13UniversalCurveOverHilbertParameter H) d

def chapter13MarkedEffectiveDivisorParameterSpace {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    {H : Chapter13HilbertSchemeData aS L P} {d : ℕ}
    (D : Chapter13MarkedEffectiveDivisorData H d) :
    Chapter13RelativeScheme (chapter13HilbertScheme H) :=
  chapter13RelativeSymmetricPower D.symmetricPower

def chapter13_marked_effective_divisor_classifies_length_d
    {S A : Scheme} {aS : A ⟶ S} {L : Chapter13Polarization A} {P : Polynomial ℤ}
    {H : Chapter13HilbertSchemeData aS L P} {d : ℕ}
    (D : Chapter13MarkedEffectiveDivisorData H d)
    (T : Chapter13RelativeScheme (chapter13HilbertScheme H)) :
    D.symmetricPower.functor.obj T ≃
      Chapter13EffectiveDivisorFamily
        (chapter13UniversalCurveOverHilbertParameter H) T d :=
  D.symmetricPower.classifies T

/-! ### Abelian families in bounded Hilbert loci -/

/-- The group-law maps and their bounded graph/equation conditions. -/
structure Chapter13AbelianGroupLawData {H A : Scheme} (p : A ⟶ H) where
  multiplication : pullback p p ⟶ A
  multiplication_over : multiplication ≫ p = pullback.snd p p ≫ p
  identity : H ⟶ A
  identity_over : identity ≫ p = 𝟙 H
  graph_polynomial : Polynomial ℤ
  graph_is_bounded : Prop
  identity_equations_are_closed : Prop
  associativity_equations_are_closed : Prop

/-
LOCAL_DEPENDENCY_GUESS: the preceding chapters are expected to identify a
relatively very ample tensor power and the precise group-law equation loci.
The fields below retain those hypotheses without pretending that a missing
moduli functor is already available in Mathlib.
-/

structure Chapter13AbelianHilbertSetup {S A : Scheme} (aS : A ⟶ S) where
  polarization : Chapter13Polarization A
  power : ℕ
  power_positive : 0 < power
  power_is_relatively_very_ample : Prop
  polynomial : Polynomial ℤ
  hilbert : Chapter13HilbertSchemeData aS polarization polynomial
  group_law : Chapter13AbelianGroupLawData aS

theorem chapter13_abelian_graphs_and_equations_are_bounded_or_closed
    {S A : Scheme} {aS : A ⟶ S}
    (D : Chapter13AbelianHilbertSetup aS) :
    D.group_law.graph_is_bounded ∧
      D.group_law.identity_equations_are_closed ∧
      D.group_law.associativity_equations_are_closed := by
  sorry

/-- Further descent and rigidity inputs required for a full abelian moduli problem. -/
structure Chapter13FurtherAbelianModuliInput where
  descent : Prop
  rigidity : Prop

/-!
The preceding structure is intentionally not bundled into the Hilbert
parameter space: the source only claims that descent and rigidity are further
requirements, not that they follow from the bounded graph construction.
-/

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
