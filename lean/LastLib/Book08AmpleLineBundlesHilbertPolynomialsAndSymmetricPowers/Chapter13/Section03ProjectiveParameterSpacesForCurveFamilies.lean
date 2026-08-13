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
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-- The polynomial `P(n) = e n + c` used for embedded curves. -/
def chapter13LinearHilbertPolynomial (e c : ℤ) : Chapter13NumericalPolynomial :=
  { polynomial := Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)
    integer_valued := by
      intro n
      refine ⟨e * (n : ℤ) + c, ?_⟩
      simp
    integer_valued_on_integers := by
      intro n
      refine ⟨e * n + c, ?_⟩
      simp }

theorem chapter13LinearHilbertPolynomial_eval (e c : ℤ) (n : ℕ) :
    (chapter13LinearHilbertPolynomial e c).polynomial.eval (n : ℚ) =
      (e : ℚ) * (n : ℚ) + c := by
  simp [chapter13LinearHilbertPolynomial, add_comm]

/-! ### Relative projective space and the Hilbert family -/

/-
The projective-space record carries an over-base identification with the
canonical `\mathbf P^r_S`; the polarization is relative to that same map.
-/

structure Chapter13ProjectiveSpaceWithPolarization (S : Scheme) (r : ℕ) where
  projectiveSpace : Chapter13RelativeProjectiveSpaceData S r
  polarization : Chapter13Polarization projectiveSpace.toBase
  hyperplane_iso :
    polarization.lineBundle.sheaf ≅ projectiveSpace.bundle.tautological

structure Chapter13CurveHilbertSetup (S : Scheme) (r : ℕ) (e c : ℤ) where
  projective : Chapter13ProjectiveSpaceWithPolarization S r
  hilbert : Chapter13HilbertSchemeData
    projective.projectiveSpace.toBase projective.polarization
    (chapter13LinearHilbertPolynomial e c)

def chapter13CurveHilbertPolynomial (_D : Chapter13CurveHilbertSetup S r e c) :
    Chapter13NumericalPolynomial :=
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
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) :
    Chapter13FlatClosedFamily aS L P T :=
  H.classifies T ((H.represented.equiv T).symm t)

def chapter13CurveHilbertFamilyIsSmoothCurve {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  chapter13SmoothPureOneDimensionalFibers
    (chapter13CurveHilbertFamilyAt H T t).projection

structure Chapter13SmoothCurveLocusData {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P) where
  locus : (chapter13HilbertScheme H).Opens
  represents : ∀ (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative),
    chapter13CurveHilbertFamilyIsSmoothCurve H T t ↔
      ∃ q : Chapter13RelativeMap T
          (chapter13OpenRelativeScheme H.represented.representative locus),
        q.map ≫ locus.ι = t.map

theorem chapter13_smooth_curve_locus_is_open {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P) :
    Nonempty (Chapter13SmoothCurveLocusData H) := by
  sorry

/-! ### Geometric connectedness -/

def chapter13CurveHilbertFamilyIsGeometricallyConnected {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  GeometricallyConnected (chapter13CurveHilbertFamilyAt H T t).projection

def chapter13GeometricallyConnectedCurveCondition {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  chapter13CurveHilbertFamilyIsSmoothCurve H T t ∧
    chapter13CurveHilbertFamilyIsGeometricallyConnected H T t

def chapter13GeometricallyConnectedCurveLocusCondition {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Scheme) (t : T ⟶ chapter13HilbertScheme H) : Prop :=
  chapter13GeometricallyConnectedCurveCondition H
    ⟨T, t ≫ chapter13HilbertSchemeToBase H⟩ ⟨t, rfl⟩

theorem chapter13_geometrically_connected_curve_locus_is_open {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (smooth : Chapter13SmoothCurveLocusData H) :
    Nonempty (Chapter13OpenLocusData (chapter13HilbertScheme H)
      (fun T t => chapter13GeometricallyConnectedCurveLocusCondition H T t)) := by
  sorry

/-! ### Marked effective divisors -/

/-- The universal curve viewed as a relative scheme over its Hilbert parameter scheme. -/
def chapter13UniversalCurveOverHilbertParameter {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P) :
    Chapter13RelativeScheme (chapter13HilbertScheme H) where
  scheme := (chapter13UniversalHilbertFamily H).scheme
  toBase := (chapter13UniversalHilbertFamily H).projection

/-! Marked divisors are formed after restricting to the smooth-curve locus. -/

def chapter13UniversalCurveOverSmoothCurveLocus {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (smooth : Chapter13SmoothCurveLocusData H) :
    Chapter13RelativeScheme smooth.locus.toScheme where
  scheme := chapter13BaseChange
    (chapter13UniversalHilbertFamily H).projection smooth.locus.ι
  toBase := chapter13BaseChangeToTest
    (chapter13UniversalHilbertFamily H).projection smooth.locus.ι

/-- A symmetric-power parameter for marked effective divisors of degree `d`. -/
structure Chapter13MarkedEffectiveDivisorData {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (smooth : Chapter13SmoothCurveLocusData H) (d : ℕ) where
  symmetricPower : Chapter13RelativeSymmetricPowerData
    (chapter13UniversalCurveOverSmoothCurveLocus H smooth) d

def chapter13MarkedEffectiveDivisorParameterSpace {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData aS L P}
    {smooth : Chapter13SmoothCurveLocusData H} {d : ℕ}
    (D : Chapter13MarkedEffectiveDivisorData H smooth d) :
    Chapter13RelativeScheme smooth.locus.toScheme :=
  chapter13RelativeSymmetricPower D.symmetricPower

def chapter13_marked_effective_divisor_classifies_length_d
    {S A : Scheme} {aS : A ⟶ S} {L : Chapter13Polarization aS}
    {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData aS L P}
    {smooth : Chapter13SmoothCurveLocusData H} {d : ℕ}
    (D : Chapter13MarkedEffectiveDivisorData H smooth d)
    (T : Chapter13RelativeScheme smooth.locus.toScheme) :
    D.symmetricPower.functor.obj T ≃
      Chapter13EffectiveDivisorFamily
        (chapter13UniversalCurveOverSmoothCurveLocus H smooth) T d :=
  D.symmetricPower.classifies T

/-! ### Abelian families in bounded Hilbert loci -/

/-- The group-law maps and their bounded graph/equation conditions. -/
structure Chapter13AbelianGroupLawData {H A : Scheme} (p : A ⟶ H) where
  multiplication : pullback p p ⟶ A
  multiplication_over : multiplication ≫ p = pullback.snd p p ≫ p
  inverse : A ⟶ A
  inverse_over : inverse ≫ p = p
  identity : H ⟶ A
  identity_over : identity ≫ p = 𝟙 H
  graph_polynomial : Chapter13NumericalPolynomial
  graph_is_bounded : Prop
  graph_is_bounded_holds : graph_is_bounded
  inverse_graph_polynomial : Chapter13NumericalPolynomial
  inverse_graph_is_bounded : Prop
  inverse_graph_is_bounded_holds : inverse_graph_is_bounded
  identity_graph_polynomial : Chapter13NumericalPolynomial
  identity_graph_is_bounded : Prop
  identity_graph_is_bounded_holds : identity_graph_is_bounded
  identity_equations_are_closed : Prop
  identity_equations_are_closed_holds : identity_equations_are_closed
  inverse_equations_are_closed : Prop
  inverse_equations_are_closed_holds : inverse_equations_are_closed
  associativity_equations_are_closed : Prop
  associativity_equations_are_closed_holds : associativity_equations_are_closed
  commutativity_equations_are_closed : Prop
  commutativity_equations_are_closed_holds : commutativity_equations_are_closed

/-
The canonical very-ampleness predicate is used for the chosen tensor power.
The bounded graph and closed-equation loci remain explicit inputs because the
full abelian moduli functor is outside this chapter's interface.
-/

structure Chapter13AbelianHilbertSetup {S A : Scheme} (aS : A ⟶ S) where
  smooth : Smooth aS
  proper : IsProper aS
  geometricallyConnected : GeometricallyConnected aS
  polarization : Chapter13Polarization aS
  power : ℕ
  power_positive : 0 < power
  power_is_relatively_very_ample :
    chapter04VeryAmple aS
      (chapter04LineBundleTensorPower polarization.lineBundle power)
  polynomial : Chapter13NumericalPolynomial
  hilbert : Chapter13HilbertSchemeData aS polarization polynomial
  /-- The classifying point of the abelian family in the bounded Hilbert problem. -/
  hilbert_parameter : Chapter13RelativeMap
    ({ scheme := S, toBase := 𝟙 S } : Chapter13RelativeScheme S)
    hilbert.represented.representative
  hilbert_family_is_above_A :
    let T : Chapter13RelativeScheme S :=
      { scheme := S, toBase := 𝟙 S }
    let F := hilbert.classifies T ((hilbert.represented.equiv T).symm hilbert_parameter)
    ∃ e : F.scheme ≅ A, e.hom ≫ aS = F.projection
  group_law : Chapter13AbelianGroupLawData aS
  polarization_compatibility_equations_are_closed : Prop
  polarization_compatibility_equations_are_closed_holds :
    polarization_compatibility_equations_are_closed

theorem chapter13_abelian_graphs_and_equations_are_bounded_or_closed
    {S A : Scheme} {aS : A ⟶ S}
    (D : Chapter13AbelianHilbertSetup aS) :
    D.group_law.graph_is_bounded ∧ D.group_law.inverse_graph_is_bounded ∧
      D.group_law.identity_graph_is_bounded ∧
      D.group_law.identity_equations_are_closed ∧
      D.group_law.inverse_equations_are_closed ∧
      D.group_law.associativity_equations_are_closed ∧
      D.group_law.commutativity_equations_are_closed ∧
      D.polarization_compatibility_equations_are_closed := by
  exact ⟨D.group_law.graph_is_bounded_holds,
    D.group_law.inverse_graph_is_bounded_holds,
    D.group_law.identity_graph_is_bounded_holds,
    D.group_law.identity_equations_are_closed_holds,
    D.group_law.inverse_equations_are_closed_holds,
    D.group_law.associativity_equations_are_closed_holds,
    D.group_law.commutativity_equations_are_closed_holds,
    D.polarization_compatibility_equations_are_closed_holds⟩

/-- Further descent and rigidity inputs required for a full abelian moduli problem. -/
structure Chapter13FurtherAbelianModuliInput where
  descent : Prop
  descent_holds : descent
  rigidity : Prop
  rigidity_holds : rigidity

/-!
The preceding structure is intentionally not bundled into the Hilbert
parameter space: the source only claims that descent and rigidity are further
requirements, not that they follow from the bounded graph construction.
-/

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
