import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Section01TheThreeDictionaries
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section05SymmetricPowersAndBaseChange

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
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01

/-! ## Relative Proj and finite graded presentations -/

/- The preceding Chapter 1 interface already exposes the relative Proj and its
   arbitrary base-change comparison.  Keep this synthesis theorem in that
   canonical form instead of taking the desired isomorphism as a predicate. -/
theorem chapter14_relative_proj_commutes_with_arbitrary_base_change
    {S T : Scheme} (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S) :
    ∃ e : Limits.pullback (chapter01RelativeProj 𝒜).projection g ⟶
        (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).scheme,
        IsIso e ∧
          e ≫ (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).projection =
            Limits.pullback.snd (chapter01RelativeProj 𝒜).projection g := by
  exact chapter01_relative_proj_base_change 𝒜 g

theorem chapter14_relative_proj_twisting_sheaf_base_change
    {S T : Scheme} (𝒜 : Chapter01RelativeGradedAlgebra S) (g : T ⟶ S)
    (n : ℤ) :
    ∃ e : Limits.pullback (chapter01RelativeProj 𝒜).projection g ⟶
        (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).scheme,
        IsIso e ∧
          e ≫ (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)).projection =
            Limits.pullback.snd (chapter01RelativeProj 𝒜).projection g ∧
          Nonempty ((Scheme.Modules.pullback e).obj
              (chapter01RelativeTwistingSheaf (chapter01RelativePullback 𝒜 g)
                (chapter01RelativeProj (chapter01RelativePullback 𝒜 g)) n) ≅
            (Scheme.Modules.pullback (Limits.pullback.fst
              (chapter01RelativeProj 𝒜).projection g)).obj
              (chapter01RelativeTwistingSheaf 𝒜 (chapter01RelativeProj 𝒜) n)) := by
  sorry

/-- A finite graded presentation whose projective embedding is derived from the
genuine degree-one relative-Proj presentation. -/
structure Chapter14FiniteGradedPresentationData {X S : Scheme} (f : X ⟶ S) where
  finitePresentation : LocallyOfFinitePresentation f
  gradedPresentation : Chapter01RelativeDegreeOneGradedPresentation f

/- LOCAL_DEPENDENCY_GUESS: this is the finite-presentation-to-projective-embedding bridge;
the saturation convention is part of the preceding Proj API. -/
theorem chapter14_finite_graded_presentation_gives_projective_embedding
    {X S : Scheme} {f : X ⟶ S}
    (D : Chapter14FiniteGradedPresentationData f) :
    Nonempty (Chapter01RelativeProjectiveEmbeddingData f) := by
  exact chapter01_relative_degree_one_presentation_gives_projective_embedding
    D.gradedPresentation

/-! ## Positivity, pullback, and fpqc descent -/

theorem chapter14_ample_iff_affine_nonvanishing
    {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) :
    O.ample L ↔ O.affineNonvanishing L := by
  rfl

def chapter14PullbackPreservesAmple
    {Y S T : Scheme} (family : Y ⟶ S) (baseChange : T ⟶ S)
    (OX : Chapter14PositivityOperations (Limits.pullback family baseChange))
    (OY : Chapter14PositivityOperations Y) (L : Chapter14LineBundle Y)
    (baseCompatibility : OY.base ≅ S)
    (_familyCompatibility : OY.family ≫ baseCompatibility.hom = family)
    (baseChangeCompatibility : OX.base ≅ T)
    (_pullbackFamilyCompatibility : OX.family ≫ baseChangeCompatibility.hom =
      Limits.pullback.snd family baseChange) : Prop :=
  OY.ample L →
    OX.ample (chapter14PullbackLineBundle (Limits.pullback.fst family baseChange) L)

/- LOCAL_DEPENDENCY_GUESS: pullback of the affine-open and eventual-generation
formulations is unconditional in the base change. -/
theorem chapter14_ample_pullback_under_arbitrary_base_change
    {Y S T : Scheme} (family : Y ⟶ S) (baseChange : T ⟶ S)
    (OX : Chapter14PositivityOperations (Limits.pullback family baseChange))
    (OY : Chapter14PositivityOperations Y) (L : Chapter14LineBundle Y)
    (baseCompatibility : OY.base ≅ S)
    (familyCompatibility : OY.family ≫ baseCompatibility.hom = family)
    (baseChangeCompatibility : OX.base ≅ T)
    (pullbackFamilyCompatibility : OX.family ≫ baseChangeCompatibility.hom =
      Limits.pullback.snd family baseChange) :
    chapter14PullbackPreservesAmple family baseChange OX OY L baseCompatibility
      familyCompatibility baseChangeCompatibility pullbackFamilyCompatibility := by
  sorry

/-- The finiteness and polarization hypotheses needed for faithful-flat descent. -/
structure Chapter14FpqcPositivityDescentHypotheses
    {X S S' : Scheme} (family : X ⟶ S) (cover : S' ⟶ S) where
  coverIsFpqc : Chapter14FpqcCoverData cover
  familyQuasiCompact : QuasiCompact family
  familyQuasiSeparated : QuasiSeparated family
  familyFinitePresentation : LocallyOfFinitePresentation family

def chapter14AmplenessDescendsAlongFpqc
    {X S S' : Scheme} (family : X ⟶ S) (cover : S' ⟶ S)
    (OX : Chapter14PositivityOperations (Limits.pullback family cover))
    (OY : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X)
    (_H : Chapter14FpqcPositivityDescentHypotheses family cover)
    (baseDownstairs : OY.base ≅ S)
    (_familyDownstairs : OY.family ≫ baseDownstairs.hom = family)
    (baseCompatibility : OX.base ≅ S')
    (_familyCompatibility : OX.family ≫ baseCompatibility.hom =
      Limits.pullback.snd family cover) : Prop :=
  OX.ample (chapter14PullbackLineBundle (Limits.pullback.fst family cover) L) →
    OY.ample L

/- LOCAL_DEPENDENCY_GUESS: relative ampleness is local for the fpqc topology on the
base under the same quasi-compactness and finite-presentation hypotheses. -/
theorem chapter14_ampleness_descends_fpqc
    {X S S' : Scheme} (family : X ⟶ S) (cover : S' ⟶ S)
    (OX : Chapter14PositivityOperations (Limits.pullback family cover))
    (OY : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X)
    (H : Chapter14FpqcPositivityDescentHypotheses family cover)
    (baseDownstairs : OY.base ≅ S)
    (familyDownstairs : OY.family ≫ baseDownstairs.hom = family)
    (baseCompatibility : OX.base ≅ S')
    (familyCompatibility : OX.family ≫ baseCompatibility.hom =
      Limits.pullback.snd family cover) :
    chapter14AmplenessDescendsAlongFpqc family cover OX OY L H baseDownstairs
      familyDownstairs baseCompatibility familyCompatibility := by
  sorry

def chapter14VeryAmplenessDescendsAlongFpqc
    {X S S' : Scheme} (family : X ⟶ S) (cover : S' ⟶ S)
    (OX : Chapter14PositivityOperations (Limits.pullback family cover))
    (OY : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X)
    (_H : Chapter14FpqcPositivityDescentHypotheses family cover)
    (baseDownstairs : OY.base ≅ S)
    (_familyDownstairs : OY.family ≫ baseDownstairs.hom = family)
    (baseCompatibility : OX.base ≅ S')
    (_familyCompatibility : OX.family ≫ baseCompatibility.hom =
      Limits.pullback.snd family cover) : Prop :=
  OX.veryAmple
      (chapter14PullbackLineBundle (Limits.pullback.fst family cover) L) →
    OY.veryAmple L

/- LOCAL_DEPENDENCY_GUESS: the descent theorem uses the fpqc cover and the
quasi-compact, quasi-separated, finite-presentation hypotheses recorded in `H`.
The line bundle is already defined downstairs, so no separate polarization-descent
datum is needed. -/
theorem chapter14_very_ampleness_descends_fpqc
    {X S S' : Scheme} (family : X ⟶ S) (cover : S' ⟶ S)
    (OX : Chapter14PositivityOperations (Limits.pullback family cover))
    (OY : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X)
    (H : Chapter14FpqcPositivityDescentHypotheses family cover)
    (baseDownstairs : OY.base ≅ S)
    (familyDownstairs : OY.family ≫ baseDownstairs.hom = family)
    (baseCompatibility : OX.base ≅ S')
    (familyCompatibility : OX.family ≫ baseCompatibility.hom =
      Limits.pullback.snd family cover) :
    chapter14VeryAmplenessDescendsAlongFpqc family cover OX OY L H baseDownstairs
      familyDownstairs baseCompatibility familyCompatibility := by
  sorry

/- The polarized projectivity statement records both parts of the source
   argument: fpqc descent of the already chosen line bundle, followed by the
   proper-family passage from ampleness to a closed projective embedding. -/
theorem chapter14_projectivity_descends_with_polarization
    {X S S' : Scheme} (family : X ⟶ S) (cover : S' ⟶ S)
    (L : Chapter14LineBundle X)
    (H : Chapter14FpqcPositivityDescentHypotheses family cover)
    (baseQuasiCompact : QuasiCompact (𝟙 S))
    (proper : IsProper family)
    (pullbackAmple :
      chapter04Ample (Limits.pullback.snd family cover)
        (chapter04PullbackLineBundle (Limits.pullback.fst family cover) L)) :
    chapter04Ample family L ∧ chapter04Projective family := by
  sorry

/-! ## High twists and fiberwise Hilbert polynomials -/

/-- The high-degree pushforward data needed for relative finiteness and base change. -/
structure Chapter14TwistedPushforwardData {X S : Scheme} (f : X ⟶ S) where
  family : Chapter14ProjectiveFlatFamilyData f
  /-- A single global high-twist bound requires quasi-compactness of the base. -/
  baseQuasiCompact : QuasiCompact (𝟙 S)
  coefficientSheaf : Chapter14CoherentSheaf X
  coefficientFlatOverBase :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08FlatOver
      f coefficientSheaf.sheaf
  polarization : Chapter14LineBundle X
  polarizationAmple : chapter04Ample f polarization
  twist : ℕ → Chapter14CoherentSheaf X
  twist_eq : ∀ n, (twist n).sheaf =
    chapter04TwistedModule coefficientSheaf.sheaf polarization n

/- LOCAL_DEPENDENCY_GUESS: relative Serre vanishing and cohomology-and-base-change
provide the threshold for both conclusions. -/
theorem chapter14_high_twists_have_locally_free_pushforwards_and_base_change
    {X S : Scheme} {f : X ⟶ S} (D : Chapter14TwistedPushforwardData f) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      SheafOfModules.IsLocallyFree
          ((Scheme.Modules.pushforward f).obj (D.twist n).sheaf) ∧
        SheafOfModules.IsFiniteType
          ((Scheme.Modules.pushforward f).obj (D.twist n).sheaf) ∧
        ∀ (T : Scheme) (g : T ⟶ S),
          Nonempty ((Scheme.Modules.pullback g).obj
              ((Scheme.Modules.pushforward f).obj (D.twist n).sheaf) ≅
            (Scheme.Modules.pushforward (Limits.pullback.snd f g)).obj
              ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj
                (D.twist n).sheaf)) := by
  sorry

/-! ## Hilbert representability and the universal family -/

/-- The functor, polarization, and parameter object for a fixed Hilbert polynomial. -/
structure Chapter14HilbertRepresentabilityContext {X S : Scheme} (f : X ⟶ S)
    (P : Chapter14NumericalPolynomial) where
  family : Chapter14ProjectiveFlatFamilyData f
  /-- Hilbert representability is stated over a noetherian (hence
      quasi-compact) base, not merely a locally noetherian one. -/
  baseNoetherian : IsNoetherian S
  polarization : Chapter14LineBundle X
  relativelyVeryAmple :
    Nonempty (Chapter14VeryAmpleEmbeddingData (f := f) polarization)

def chapter14ProjectiveOverBase {S : Scheme} (Y : Over S) : Prop :=
  Nonempty (Chapter14ProjectiveMorphismData Y.hom)

def chapter14FinitePresentationOverBase {S : Scheme} (Y : Over S) : Prop :=
  LocallyOfFinitePresentation Y.hom

/- LOCAL_DEPENDENCY_GUESS: the Grassmannian/regularity construction from §12.2--§12.3
supplies this representer and its flat finitely presented universal closed family. -/
theorem chapter14_fixed_polynomial_hilbert_representability
    {X S : Scheme} {f : X ⟶ S} {P : Chapter14NumericalPolynomial}
    (H : Chapter14HilbertRepresentabilityContext f P) :
    ∃ parameter : Over S,
      chapter14ProjectiveOverBase parameter ∧
        chapter14FinitePresentationOverBase parameter ∧
          chapter14RepresentedBy
              (chapter14FixedPolynomialHilbertFunctor (Over.mk f) H.polarization P) parameter ∧
            ∃ Z : Scheme,
              Nonempty (Chapter14UniversalFamilyData (Z := Z) f parameter.hom) := by
  sorry

/- The universal family is not the representing scheme; this records the two
   objects separately without asserting that their underlying schemes cannot
   be isomorphic. -/
def chapter14HilbertRepresenterAndUniversalFamilyExist
    {X S : Scheme} {f : X ⟶ S} {P : Chapter14NumericalPolynomial}
    (H : Chapter14HilbertRepresentabilityContext f P) : Prop :=
  ∃ parameter : Over S,
    chapter14RepresentedBy
        (chapter14FixedPolynomialHilbertFunctor (Over.mk f) H.polarization P)
        parameter ∧
      ∃ Z : Scheme, Nonempty (Chapter14UniversalFamilyData (Z := Z) f parameter.hom)

/-- The finite-length specialization of the fixed-polynomial functor. -/
abbrev Chapter14FiniteLengthHilbertContext {X S : Scheme} (f : X ⟶ S) (d : ℕ) :=
  Chapter14HilbertRepresentabilityContext f (chapter14ConstantHilbertPolynomial d)

/- LOCAL_DEPENDENCY_GUESS: constant polynomial `d` identifies precisely the finite locally
free length-`d` families, independently of the chosen projective embedding. -/
theorem chapter14_constant_hilbert_polynomial_is_intrinsic_length_d
    {X S : Scheme} {f : X ⟶ S} (d : ℕ)
    (H : Chapter14FiniteLengthHilbertContext f d) :
    ∃ parameter : Over S,
      chapter14RepresentedBy
          (chapter14FiniteLengthHilbertFunctor (Over.mk f) d) parameter ∧
        ∃ Z : Scheme, ∃ D : Chapter14FiniteFlatFamilyData (Z := Z) f parameter.hom,
          D.rank = d := by
  sorry

theorem chapter14_representing_objects_for_the_same_hilbert_functor_are_isomorphic
    {S : Scheme.{u}} (F : Chapter14RelativeFunctor S) (Y Z : Over S)
    (hY : chapter14RepresentedBy F Y) (hZ : chapter14RepresentedBy F Z) :
    Nonempty (Y ≅ Z) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: for a quasi-projective `X`, the finite-length parameter is the
open locus in a projective compactification whose canonical universal family has empty
image in the compactification boundary. -/
structure Chapter14QuasiProjectiveLengthLocusData {X S : Scheme} (f : X ⟶ S) (d : ℕ) where
  compactification : Scheme
  compactificationToBase : compactification ⟶ S
  compactificationProjective : chapter04Projective compactificationToBase
  quasiProjectiveOpen : compactification.Opens
  quasiProjectiveEmbedding : X ⟶ compactification
  quasiProjectiveEmbedding_isOpen : IsOpenImmersion quasiProjectiveEmbedding
  quasiProjectiveEmbedding_overBase :
    quasiProjectiveEmbedding ≫ compactificationToBase = f
  quasiProjectiveEmbedding_image :
    Set.range quasiProjectiveEmbedding = (quasiProjectiveOpen : Set compactification)
  compactificationParameter : Scheme
  compactificationParameterToBase : compactificationParameter ⟶ S
  compactificationParameterProjective : chapter04Projective compactificationParameterToBase
  universalFamily : Scheme
  universalFamilyData :
    Chapter14FiniteFlatFamilyData (X := compactification)
      (Z := universalFamily) compactificationToBase compactificationParameterToBase
  universalFamilyRank : universalFamilyData.rank = d
  boundaryImage : Set compactificationParameter
  boundaryImage_spec :
    boundaryImage =
      {p | ∃ z : universalFamily,
        universalFamilyData.familyToParameter z = p ∧
          universalFamilyData.familyToAmbient z ∉ quasiProjectiveOpen}
  boundaryImage_closed : IsClosed boundaryImage
  lengthLocus : compactificationParameter.Opens
  lengthLocus_spec : ∀ p, p ∈ lengthLocus ↔ p ∉ boundaryImage
  represents :
    chapter14RepresentedBy
      (chapter14FiniteLengthHilbertFunctor (Over.mk f) d)
      (Over.mk (lengthLocus.ι ≫ compactificationParameterToBase))

def chapter14QuasiProjectiveLengthLocusMap
    {X S : Scheme} {f : X ⟶ S} (d : ℕ)
    (D : Chapter14QuasiProjectiveLengthLocusData f d) :
    D.lengthLocus.toScheme ⟶ D.compactificationParameter :=
  D.lengthLocus.ι

theorem chapter14_quasi_projective_length_parameter_is_an_open_locus
    {X S : Scheme} {f : X ⟶ S} (d : ℕ)
    (D : Chapter14QuasiProjectiveLengthLocusData f d) :
    IsOpenImmersion (chapter14QuasiProjectiveLengthLocusMap d D) := by
  change IsOpenImmersion D.lengthLocus.ι
  infer_instance

/-! ## Smooth curves, symmetric powers, and configurations -/

/- A raw scheme family is viewed in the canonical relative-scheme API used by
Chapter 11. -/
abbrev chapter14RelativeCurve {C S : Scheme} (f : C ⟶ S) :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.RelativeScheme S :=
  { carrier := C, structuralMap := f }

noncomputable def chapter14SymmetricPower {C S : Scheme} (f : C ⟶ S) (d : ℕ)
    (Q : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11QuasiProjectiveOver
      (chapter14RelativeCurve f)) :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.RelativeScheme S := by
  letI := Q
  exact LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.symmetricPower
    (chapter14RelativeCurve f) d

/-- The collision-free configuration package imported from Chapter 11.

The canonical field contains the big-diagonal complement, the free permutation
action, the quotient universal property, and the classifying universal family;
the open-to-symmetric-power map below is derived from that quotient data. -/
structure Chapter14ConfigurationSpaceData {C S : Scheme} (f : C ⟶ S) (d : ℕ)
    [Q :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11QuasiProjectiveOver
      (chapter14RelativeCurve f)] where
  smooth : SmoothOfRelativeDimension 1 f
  canonical :
    @LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11ConfigurationSpaceData
      S (chapter14RelativeCurve f) d Q

/- The quotient universal property of `canonical` supplies the map from the
collision-free quotient to the full symmetric power. -/
noncomputable def chapter14ConfigurationOpenToSymmetricPower
    {C S : Scheme} {f : C ⟶ S}
    [Q : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11QuasiProjectiveOver
      (chapter14RelativeCurve f)] (d : ℕ)
    (D : Chapter14ConfigurationSpaceData f d) :
    D.canonical.quotient.carrier.carrier ⟶
      (chapter14SymmetricPower f d Q).carrier := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the canonical Chapter 11 configuration package supplies
the diagonal complement, free permutation quotient, and universal finite étale family;
the smoothness statements use the relative curve and symmetric-power interfaces. -/
theorem chapter14_configuration_open_is_smooth_and_finite_etale
    {C S : Scheme} {f : C ⟶ S}
    [Q : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11QuasiProjectiveOver
      (chapter14RelativeCurve f)] (curve : Chapter14SmoothRelativeCurveData f)
    (d : ℕ) (D : Chapter14ConfigurationSpaceData f d) :
    SmoothOfRelativeDimension d
        (chapter14SymmetricPower f d Q).structuralMap ∧
      SmoothOfRelativeDimension d D.canonical.quotient.carrier.structuralMap ∧
      IsOpenImmersion (chapter14ConfigurationOpenToSymmetricPower d D) ∧
      chapter14ConfigurationOpenToSymmetricPower d D ≫
          (chapter14SymmetricPower f d Q).structuralMap =
        D.canonical.quotient.carrier.structuralMap ∧
                IsFinite D.canonical.quotient.quotientMap.hom ∧
                  Flat D.canonical.quotient.quotientMap.hom ∧
                      Etale D.canonical.quotient.quotientMap.hom ∧
                IsFinite D.canonical.universalFamily.mapToBase ∧
                  Flat D.canonical.universalFamily.mapToBase ∧
                    Etale D.canonical.universalFamily.mapToBase := by
  sorry

/-! ## Hilbert scheme equals symmetric power on a smooth curve -/

structure Chapter14SmoothCurveHilbertContext {C S : Scheme} (f : C ⟶ S) (d : ℕ) where
  curve : Chapter14SmoothRelativeCurveData f
  quasiProjective :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11QuasiProjectiveOver
      (chapter14RelativeCurve f)

structure Chapter14SmoothCurveHilbertSymmetricRepresentation
    {C S : Scheme} (f : C ⟶ S) (d : ℕ) where
  curve : Chapter14SmoothRelativeCurveData f
  hilbertParameter : Over S
  symmetricPowerParameter : Over S
  hilbertRepresents :
    chapter14RepresentedBy
      (chapter14FiniteLengthHilbertFunctor (Over.mk f) d) hilbertParameter
  symmetricPowerQuasiProjective :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Chapter11QuasiProjectiveOver
      (chapter14RelativeCurve f)
  parameterIso : Nonempty (hilbertParameter ≅ symmetricPowerParameter)
  symmetricPowerIsCanonical :
    Nonempty (symmetricPowerParameter ≅
      Over.mk (chapter14SymmetricPower f d symmetricPowerQuasiProjective).structuralMap)
  symmetricPowerSmooth : SmoothOfRelativeDimension d symmetricPowerParameter.hom
  symmetricPowerRepresents :
    chapter14RepresentedBy
      (chapter14PermutationQuotientFunctor (Over.mk f) d) symmetricPowerParameter
  divisorRepresents :
    chapter14RepresentedBy
      (chapter14EffectiveCartierDivisorFunctor (Over.mk f) d) symmetricPowerParameter
  universalFamily : ∃ Z : Scheme,
    ∃ D : Chapter14FiniteFlatFamilyData (Z := Z) f symmetricPowerParameter.hom,
      D.rank = d

def chapter14SmoothCurveHilbertEqualsSymmetricPowerStatement
    {C S : Scheme} {f : C ⟶ S} (d : ℕ)
    (H : Chapter14SmoothCurveHilbertContext f d) : Prop :=
  ∃ R : Chapter14SmoothCurveHilbertSymmetricRepresentation f d,
    R.curve = H.curve

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
  ∃ R : Chapter14SmoothCurveHilbertSymmetricRepresentation f d,
    R.curve = H.curve ∧
      ∀ (T : Scheme) (g : T ⟶ S),
        ∃ RT : Chapter14SmoothCurveHilbertSymmetricRepresentation
            (Limits.pullback.snd f g) d,
          Nonempty (RT.hilbertParameter ≅
            Over.mk (Limits.pullback.snd R.hilbertParameter.hom g)) ∧
            Nonempty (RT.symmetricPowerParameter ≅
              Over.mk (Limits.pullback.snd R.symmetricPowerParameter.hom g))

theorem chapter14_smooth_curve_parameter_constructions_commute_with_arbitrary_base_change
    {C S : Scheme} {f : C ⟶ S} (d : ℕ)
    (H : Chapter14SmoothCurveHilbertContext f d) :
    chapter14SmoothCurveBaseChangeStatement d H := by
  sorry

/-! ## Projective curves and polarized abelian schemes -/

/- A projective curve context carrying the line bundle used for the embedding. -/
structure Chapter14ProjectiveCurveEmbeddingContext {C S : Scheme} (f : C ⟶ S) where
  projective : Chapter14ProjectiveMorphismData f
  proper : IsProper f
  baseLocallyNoetherian : IsLocallyNoetherian S
  baseQuasiCompact : QuasiCompact (𝟙 S)
  familyQuasiCompact : QuasiCompact f
  familyFinitePresentation : LocallyOfFinitePresentation f
  positivity : Chapter14PositivityOperations C
  positivityBase : positivity.base ≅ S
  positivityFamily : positivity.family ≫ positivityBase.hom = f
  lineBundle : Chapter14LineBundle C
  ample : positivity.ample lineBundle

/- LOCAL_DEPENDENCY_GUESS: a high tensor power of an ample line bundle on a projective
curve supplies a closed immersion into the corresponding projective bundle over `S`. -/
theorem chapter14_ample_projective_curve_has_high_power_embedding
    {C S : Scheme} {f : C ⟶ S}
    (D : Chapter14ProjectiveCurveEmbeddingContext f) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      D.positivity.veryAmple (D.positivity.tensorPower D.lineBundle n) ∧
        ∃ W : Chapter14VeryAmpleEmbeddingData (f := f)
            (D.positivity.tensorPower D.lineBundle n),
          IsClosedImmersion W.embedding := by
  sorry

/- A relatively ample line bundle on an abelian scheme. -/
structure Chapter14PolarizedAbelianSchemeData {A S : Scheme} (f : A ⟶ S) where
  abelianScheme : Chapter14AbelianSchemeCore f
  baseLocallyNoetherian : IsLocallyNoetherian S
  baseQuasiCompact : QuasiCompact (𝟙 S)
  positivity : Chapter14PositivityOperations A
  positivityBase : positivity.base ≅ S
  positivityFamily : positivity.family ≫ positivityBase.hom = f
  polarization : Chapter14LineBundle A
  relativelyAmple : positivity.ample polarization

structure Chapter14HighPowerSectionEmbeddingData
    {A S : Scheme} {f : A ⟶ S} (L : Chapter14LineBundle A) (n : ℕ) where
  sections : S.Modules
  sections_eq : sections = (Scheme.Modules.pushforward f).obj
    (chapter04LineBundleTensorPower L n).sheaf
  sectionsLocallyFree :
    SheafOfModules.IsLocallyFree sections ∧ SheafOfModules.IsFiniteType sections
  commutesWithBaseChange :
    ∀ (T : Scheme) (g : T ⟶ S),
      Nonempty ((Scheme.Modules.pullback g).obj sections ≅
        (Scheme.Modules.pushforward (Limits.pullback.snd f g)).obj
          (chapter04LineBundleTensorPower
            (chapter04PullbackLineBundle (Limits.pullback.fst f g) L) n).sheaf)
  veryAmple : chapter04VeryAmple f (chapter04LineBundleTensorPower L n)
  embedding : Chapter14VeryAmpleEmbeddingData (f := f)
    (chapter04LineBundleTensorPower L n)
  closedEmbedding : IsClosedImmersion embedding.embedding

/- LOCAL_DEPENDENCY_GUESS: relative Serre vanishing and uniform very ampleness
    supply the high-power bound.  No sharp exponent is used by the source synthesis. -/
theorem chapter14_abelian_scheme_polarization_has_high_very_ample_power
    {A S : Scheme} {f : A ⟶ S}
    (D : Chapter14PolarizedAbelianSchemeData f) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Nonempty (Chapter14HighPowerSectionEmbeddingData (f := f) D.polarization n) := by
  sorry

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
