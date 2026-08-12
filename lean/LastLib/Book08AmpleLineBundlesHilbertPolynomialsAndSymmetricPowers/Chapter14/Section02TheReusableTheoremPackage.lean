import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Section01TheThreeDictionaries

/-!
# Book 8, Chapter 14, §14.2: the reusable theorem package

The declarations here collect the compatibility, representability, and
parameter-space statements that the synthesis paragraph makes available to
later chapters.  Relative Proj, cohomology, and Hilbert-scheme constructions
are kept as named interfaces until the preceding Book08 leaves are reconciled.
-/

noncomputable section

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

/-! ## Relative Proj and finite graded presentations -/

/-- A comparison datum for relative Proj after a base change `T ⟶ S`. -/
structure Chapter14RelativeProjBaseChangeData {S T P PT : Scheme}
    (p : P ⟶ S) (g : T ⟶ S) where
  baseChangedProj : PT ⟶ T
  comparison : PT ⟶ Limits.pullback p g
  comparisonOverBase : comparison ≫ Limits.pullback.snd p g = baseChangedProj
  /- LOCAL_DEPENDENCY_GUESS: this predicate identifies `PT` with the relative Proj
     of the degreewise pullback of the graded algebra. -/
  isRelativeProjOfBaseChange : Prop
  twistingOnPullback : Chapter14LineBundle (Limits.pullback p g)
  twistingOnBaseChanged : Chapter14LineBundle PT

/- LOCAL_DEPENDENCY_GUESS: the chart calculation in §1.4 should prove both fields below
for the relative Proj construction, with no flatness assumption on `g`. -/
theorem chapter14_relative_proj_commutes_with_arbitrary_base_change
    {S T P PT : Scheme} {p : P ⟶ S} {g : T ⟶ S}
    (D : Chapter14RelativeProjBaseChangeData (PT := PT) p g) :
    IsIso D.comparison := by
  sorry

theorem chapter14_relative_proj_twisting_sheaf_base_change
    {S T P PT : Scheme} {p : P ⟶ S} {g : T ⟶ S}
    (D : Chapter14RelativeProjBaseChangeData (PT := PT) p g) :
    Nonempty ((Scheme.Modules.pullback D.comparison).obj D.twistingOnPullback.sheaf ≅
      D.twistingOnBaseChanged.sheaf) := by
  sorry

/-- A finite graded presentation together with its candidate projective embedding. -/
structure Chapter14FiniteGradedPresentationData {X S : Scheme} (f : X ⟶ S) where
  finitePresentation : Prop
  generatedInDegreeOne : Prop
  ambient : Scheme
  ambientToBase : ambient ⟶ S
  embedding : X ⟶ ambient
  overBase : embedding ≫ ambientToBase = f
  /- The ambient is the projective bundle attached to the finite generating module. -/
  ambientIsProjectiveBundle : Prop

/- LOCAL_DEPENDENCY_GUESS: this is the finite-presentation-to-projective-embedding bridge;
the saturation convention is part of the preceding Proj API. -/
theorem chapter14_finite_graded_presentation_gives_projective_embedding
    {X S : Scheme} {f : X ⟶ S}
    (D : Chapter14FiniteGradedPresentationData f) :
    IsClosedImmersion D.embedding := by
  sorry

/-! ## Positivity, pullback, and fpqc descent -/

theorem chapter14_ample_iff_affine_nonvanishing
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) :
    O.ample L ↔ O.affineNonvanishing L := by
  sorry

def chapter14PullbackPreservesAmple
    {X Y : Scheme} (f : X ⟶ Y)
    (OX : Chapter14PositivityOperations X) (OY : Chapter14PositivityOperations Y)
    (L : Chapter14LineBundle Y) : Prop :=
  OY.ample L → OX.ample (chapter14PullbackLineBundle f L)

/- LOCAL_DEPENDENCY_GUESS: pullback of the affine-open and eventual-generation
formulations is unconditional in the base change. -/
theorem chapter14_ample_pullback_under_arbitrary_base_change
    {X Y : Scheme} (f : X ⟶ Y)
    (OX : Chapter14PositivityOperations X) (OY : Chapter14PositivityOperations Y)
    (L : Chapter14LineBundle Y) :
    chapter14PullbackPreservesAmple f OX OY L := by
  sorry

/-- The finiteness and polarization hypotheses needed for faithful-flat descent. -/
structure Chapter14FpqcPositivityDescentHypotheses where
  coverIsFpqc : Prop
  baseIsQuasiCompact : Prop
  polarizationDescends : Prop

def chapter14VeryAmplenessDescendsAlongFpqc
    {X Y : Scheme} (f : X ⟶ Y)
    (OX : Chapter14PositivityOperations X) (OY : Chapter14PositivityOperations Y)
    (L : Chapter14LineBundle Y) (H : Chapter14FpqcPositivityDescentHypotheses) : Prop :=
  H.coverIsFpqc ∧ H.baseIsQuasiCompact ∧ H.polarizationDescends →
    OX.veryAmple (chapter14PullbackLineBundle f L) → OY.veryAmple L

/- LOCAL_DEPENDENCY_GUESS: the descent theorem uses exactly the quasi-compactness and
polarization hypotheses recorded in `H`; no stronger characteristic assumption is intended. -/
theorem chapter14_very_ampleness_descends_fpqc
    {X Y : Scheme} (f : X ⟶ Y)
    (OX : Chapter14PositivityOperations X) (OY : Chapter14PositivityOperations Y)
    (L : Chapter14LineBundle Y) (H : Chapter14FpqcPositivityDescentHypotheses) :
    chapter14VeryAmplenessDescendsAlongFpqc f OX OY L H := by
  sorry

/-! ## High twists and fiberwise Hilbert polynomials -/

/-- The high-degree pushforward data needed for relative finiteness and base change. -/
structure Chapter14TwistedPushforwardData {X S : Scheme} (f : X ⟶ S) where
  family : Chapter14ProjectiveFlatFamilyData f
  coefficientSheaf : Chapter14CoherentSheaf X
  coefficientFlatOverBase : Prop
  polarization : Chapter14LineBundle X
  twist : ℕ → Chapter14CoherentSheaf X
  pushforwardLocallyFree : ℕ → Prop
  pushforwardCommutesWithBaseChange : ℕ → Prop

/- LOCAL_DEPENDENCY_GUESS: relative Serre vanishing and cohomology-and-base-change
provide the threshold for both conclusions. -/
theorem chapter14_high_twists_have_locally_free_pushforwards_and_base_change
    {X S : Scheme} {f : X ⟶ S} (D : Chapter14TwistedPushforwardData f) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      D.pushforwardLocallyFree n ∧ D.pushforwardCommutesWithBaseChange n := by
  sorry

/-! ## Hilbert representability and the universal family -/

/-- The functor, polarization, and parameter object for a fixed Hilbert polynomial. -/
structure Chapter14HilbertRepresentabilityContext {X S : Scheme} (f : X ⟶ S)
    (P : Polynomial ℚ) where
  family : Chapter14ProjectiveFlatFamilyData f
  polarization : Chapter14LineBundle X
  relativelyVeryAmple : Prop
  functor : Chapter14RelativeFunctor S
  parameter : Over S

def chapter14ProjectiveOverBase {S : Scheme} (Y : Over S) : Prop :=
  Nonempty (Chapter14ProjectiveMorphismData Y.hom)

def chapter14FinitePresentationOverBase {S : Scheme} (Y : Over S) : Prop :=
  LocallyOfFinitePresentation Y.hom

/- LOCAL_DEPENDENCY_GUESS: the Grassmannian/regularity construction from §12.2--§12.3
supplies this representer and its flat finitely presented universal closed family. -/
theorem chapter14_fixed_polynomial_hilbert_representability
    {X S : Scheme} {f : X ⟶ S} {P : Polynomial ℚ}
    (H : Chapter14HilbertRepresentabilityContext f P) :
    chapter14ProjectiveOverBase H.parameter ∧
      chapter14FinitePresentationOverBase H.parameter ∧
        chapter14RepresentedBy H.functor H.parameter ∧
          ∃ Z : Scheme,
            Nonempty (Chapter14UniversalFamilyData (Z := Z) f H.parameter.hom) := by
  sorry

/- The universal family is not the representing scheme; this is a separate object. -/
def chapter14HilbertRepresenterAndUniversalFamilyAreDistinct
    {X S : Scheme} {f : X ⟶ S} {P : Polynomial ℚ}
    (H : Chapter14HilbertRepresentabilityContext f P) : Prop :=
  ∃ Z : Scheme, Nonempty (Chapter14UniversalFamilyData (Z := Z) f H.parameter.hom)

/-- The finite-length specialization of the fixed-polynomial functor. -/
structure Chapter14FiniteLengthHilbertContext {X S : Scheme} (f : X ⟶ S) (d : ℕ)
    extends Chapter14HilbertRepresentabilityContext f (chapter14ConstantHilbertPolynomial d) where
  functorIsFiniteLength : Prop
  polynomialIsConstantLength : Prop

/- LOCAL_DEPENDENCY_GUESS: constant polynomial `d` identifies precisely the finite locally
free length-`d` families, independently of the chosen projective embedding. -/
theorem chapter14_constant_hilbert_polynomial_is_intrinsic_length_d
    {X S : Scheme} {f : X ⟶ S} (d : ℕ)
    (H : Chapter14FiniteLengthHilbertContext f d) :
    ∃ Z : Scheme, ∃ D : Chapter14FiniteFlatFamilyData (Z := Z) f H.parameter.hom,
      D.rank = d := by
  sorry

theorem chapter14_representing_objects_for_the_same_hilbert_functor_are_isomorphic
    {S : Scheme.{u}} (F : Chapter14RelativeFunctor S) (Y Z : Over S)
    (hY : chapter14RepresentedBy F Y) (hZ : chapter14RepresentedBy F Z) :
    Nonempty (Y ≅ Z) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: for a quasi-projective `X`, the finite-length parameter is the
open locus in a projective compactification whose universal family lies in `X`. -/
structure Chapter14QuasiProjectiveLengthLocusData {X S : Scheme} (f : X ⟶ S) (d : ℕ) where
  compactification : Scheme
  compactificationToBase : compactification ⟶ S
  compactificationParameter : Scheme
  compactificationParameterToBase : compactificationParameter ⟶ S
  lengthLocus : Scheme
  lengthLocusToCompactificationParameter : lengthLocus ⟶ compactificationParameter
  liesInsideQuasiProjectiveOpen : Prop

theorem chapter14_quasi_projective_length_parameter_is_an_open_locus
    {X S : Scheme} {f : X ⟶ S} (d : ℕ)
    (D : Chapter14QuasiProjectiveLengthLocusData f d) :
    IsOpenImmersion D.lengthLocusToCompactificationParameter := by
  sorry

/-! ## Smooth curves, symmetric powers, and configurations -/

/-- Data for the reduced, collision-free open of a symmetric power. -/
structure Chapter14ConfigurationSpaceData {C S : Scheme} (f : C ⟶ S) (d : ℕ) where
  symmetricPower : Scheme
  symmetricPowerToBase : symmetricPower ⟶ S
  reducedOpen : Scheme
  reducedOpenToSymmetricPower : reducedOpen ⟶ symmetricPower
  reducedOpenToBase : reducedOpen ⟶ S
  reducedOpenOverBase : reducedOpenToSymmetricPower ≫ symmetricPowerToBase = reducedOpenToBase
  orderedConfiguration : Scheme
  /- The reduced open is the unordered configuration space. -/
  orderedToUnordered : orderedConfiguration ⟶ reducedOpen
  orderedToBase : orderedConfiguration ⟶ S
  quotientOverBase : orderedToUnordered ≫ reducedOpenToBase = orderedToBase
  universalFamily : Scheme
  universalFamilyToParameter : universalFamily ⟶ reducedOpen
  universalFamilyToCurve : universalFamily ⟶ C
  universalFamilyOverBase : universalFamilyToParameter ≫ reducedOpenToBase =
    universalFamilyToCurve ≫ f
  quotientDegree : ℕ

/- LOCAL_DEPENDENCY_GUESS: smoothness, the big-diagonal open, and the finite étale
permutation torsor are the curve calculations in §§11.3--11.4. -/
theorem chapter14_configuration_open_is_smooth_and_finite_etale
    {C S : Scheme} {f : C ⟶ S} (curve : Chapter14SmoothRelativeCurveData f)
    (d : ℕ) (D : Chapter14ConfigurationSpaceData f d) :
    SmoothOfRelativeDimension d D.symmetricPowerToBase ∧
      SmoothOfRelativeDimension d
        (D.reducedOpenToSymmetricPower ≫ D.symmetricPowerToBase) ∧
        IsOpenImmersion D.reducedOpenToSymmetricPower ∧
          IsFinite D.orderedToUnordered ∧
            Etale D.orderedToUnordered ∧
              Surjective D.orderedToUnordered ∧
                IsFinite D.universalFamilyToParameter ∧
                  Flat D.universalFamilyToParameter ∧ D.quotientDegree = Nat.factorial d := by
  sorry

/-! ## Hilbert scheme equals symmetric power on a smooth curve -/

structure Chapter14SmoothCurveHilbertContext {C S : Scheme} (f : C ⟶ S) (d : ℕ) where
  curve : Chapter14SmoothRelativeCurveData f
  hilbertFunctor : Chapter14RelativeFunctor S
  hilbertParameter : Over S
  symmetricPowerFunctor : Chapter14RelativeFunctor S
  symmetricPowerParameter : Over S
  effectiveCartierDivisorFunctor : Chapter14RelativeFunctor S

def chapter14SmoothCurveHilbertEqualsSymmetricPowerStatement
    {C S : Scheme} {f : C ⟶ S} (d : ℕ)
    (H : Chapter14SmoothCurveHilbertContext f d) : Prop :=
  Nonempty (H.hilbertParameter ≅ H.symmetricPowerParameter) ∧
      SmoothOfRelativeDimension d H.symmetricPowerParameter.hom ∧
      chapter14RepresentedBy H.symmetricPowerFunctor H.symmetricPowerParameter ∧
      chapter14RepresentedBy H.effectiveCartierDivisorFunctor H.symmetricPowerParameter ∧
        ∃ Z : Scheme,
          ∃ D : Chapter14FiniteFlatFamilyData (Z := Z) f H.symmetricPowerParameter.hom,
            D.rank = d

/- LOCAL_DEPENDENCY_GUESS: the monic-polynomial chart argument supplies the following
functorial identification, including collisions and every residue characteristic. -/
theorem chapter14_smooth_curve_hilbert_equals_symmetric_power
    {C S : Scheme} {f : C ⟶ S} (d : ℕ)
    (H : Chapter14SmoothCurveHilbertContext f d) :
    chapter14SmoothCurveHilbertEqualsSymmetricPowerStatement d H := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding equivalence is represented by the same monic
polynomial construction after any base change `T ⟶ S`.  The statement below exposes
the base-changed curve and its representing objects instead of accepting the desired
base-change proposition as an input. -/
def chapter14SmoothCurveBaseChangeStatement
    {C S : Scheme} {f : C ⟶ S} (d : ℕ)
    (H : Chapter14SmoothCurveHilbertContext f d) : Prop :=
  chapter14SmoothCurveHilbertEqualsSymmetricPowerStatement d H ∧
    ∀ (T : Scheme) (g : T ⟶ S),
      ∃ (CT : Scheme) (fT : CT ⟶ T),
        Nonempty (Over.mk fT ≅
          Over.mk (Limits.pullback.snd f g)) ∧
          ∃ HT : Chapter14SmoothCurveHilbertContext fT d,
            Nonempty (HT.hilbertParameter ≅ HT.symmetricPowerParameter) ∧
              SmoothOfRelativeDimension d HT.symmetricPowerParameter.hom ∧
              chapter14RepresentedBy HT.symmetricPowerFunctor HT.symmetricPowerParameter ∧
                chapter14RepresentedBy HT.effectiveCartierDivisorFunctor
                  HT.symmetricPowerParameter ∧
                  ∃ Z : Scheme,
                    ∃ D : Chapter14FiniteFlatFamilyData (Z := Z) fT
                      HT.symmetricPowerParameter.hom,
                      D.rank = d

theorem chapter14_smooth_curve_parameter_constructions_commute_with_arbitrary_base_change
    {C S : Scheme} {f : C ⟶ S} (d : ℕ)
    (H : Chapter14SmoothCurveHilbertContext f d) :
    chapter14SmoothCurveBaseChangeStatement d H := by
  sorry

/-! ## Projective curves and polarized abelian schemes -/

/- A projective curve context carrying the line bundle used for the embedding. -/
structure Chapter14ProjectiveCurveEmbeddingContext {C S : Scheme} (f : C ⟶ S) where
  projective : Prop
  positivity : Chapter14PositivityOperations C
  lineBundle : Chapter14LineBundle C
  ample : positivity.ample lineBundle

/- LOCAL_DEPENDENCY_GUESS: a high tensor power of an ample line bundle on a projective
curve supplies a closed immersion into the corresponding projective bundle over `S`. -/
theorem chapter14_ample_projective_curve_has_high_power_embedding
    {C S : Scheme} {f : C ⟶ S}
    (D : Chapter14ProjectiveCurveEmbeddingContext f) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      D.positivity.veryAmple (D.positivity.tensorPower D.lineBundle n) ∧
        ∃ (P : Scheme) (p : P ⟶ S) (embedding : C ⟶ P),
          IsClosedImmersion embedding ∧ embedding ≫ p = f := by
  sorry

/- A relatively ample line bundle on an abelian scheme. -/
structure Chapter14PolarizedAbelianSchemeData {A S : Scheme} (f : A ⟶ S) where
  abelianScheme : Prop
  positivity : Chapter14PositivityOperations A
  polarization : Chapter14LineBundle A
  relativelyAmple : Prop

/- LOCAL_DEPENDENCY_GUESS: the theorem of the cube and the relative polarization
construction identify the third tensor power as very ample. -/
theorem chapter14_abelian_scheme_polarization_cube_is_very_ample
    {A S : Scheme} {f : A ⟶ S}
    (D : Chapter14PolarizedAbelianSchemeData f) :
    D.positivity.veryAmple (D.positivity.tensorPower D.polarization 3) := by
  sorry

/-- The two functorial controls supplied by the theorem of the cube. -/
structure Chapter14TheoremOfCubeConclusion {A S : Scheme} {f : A ⟶ S}
    (D : Chapter14PolarizedAbelianSchemeData f) where
  controlsTranslations : Prop
  controlsArbitraryBaseChange : Prop

/- LOCAL_DEPENDENCY_GUESS: this conclusion packages the translation and arbitrary
base-change compatibilities used by the polarized abelian-scheme construction. -/
theorem chapter14_theorem_of_cube_controls_translation_and_base_change
    {A S : Scheme} {f : A ⟶ S}
    (D : Chapter14PolarizedAbelianSchemeData f) :
    Nonempty (Chapter14TheoremOfCubeConclusion D) := by
  sorry

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
