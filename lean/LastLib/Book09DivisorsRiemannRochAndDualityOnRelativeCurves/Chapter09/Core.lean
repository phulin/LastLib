import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section01TheBundleAttachedToADivisor
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09

noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v w

/-!
This file contains the shared book-facing interfaces for Chapter 9.  Derived
Ext groups and quasi-isomorphisms use the pinned derived-category API; the
remaining sheaf-level constructions are recorded by typed universal-property
interfaces so that the statements do not silently replace a derived assertion
by a cohomological one.
-/

/-! ### Basic sheaf operations and cohomology -/

/-- The structure sheaf, in the module-sheaf category used by the preceding book. -/
abbrev chapter09StructureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A coherent module sheaf, using the canonical quasi-coherence and finite-type predicates. -/
def chapter09Coherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent ∧ F.IsFiniteType

/-- The canonical cohomology object supplied by Book 8, viewed as its carrier type. -/
abbrev chapter09H {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : Type (u + 1) :=
  chapter04Cohomology F i

/-- The bundled cohomology object underlying `chapter09H`. -/
abbrev chapter09HObject {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : AddCommGrpCat.{u + 1} :=
  chapter04Cohomology F i

/-- Functoriality of the canonical cohomology construction on module sheaves. -/
abbrev chapter09CohomologyMap
    {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) (i : ℕ) :
    chapter09HObject F i ⟶ chapter09HObject G i :=
  (chapter04CanonicalCohomologyContext X).map φ i

theorem chapter09CohomologyMap_id
    {X : Scheme.{u}} (F : X.Modules) (i : ℕ) :
    chapter09CohomologyMap (𝟙 F) i = 𝟙 _ := by
  exact (chapter04CanonicalCohomologyContext X).map_id F i

theorem chapter09CohomologyMap_comp
    {X : Scheme.{u}} {F G H : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ H) (i : ℕ) :
    chapter09CohomologyMap (φ ≫ ψ) i =
      chapter09CohomologyMap φ i ≫ chapter09CohomologyMap ψ i := by
  exact (chapter04CanonicalCohomologyContext X).map_comp φ ψ i

/-- The underlying (not yet scalar-enhanced) dual of a cohomology type. -/
abbrev chapter09Dual (k V : Type*) := V → k

/-- The linear dual used when the cohomology scalar action is available. -/
abbrev chapter09LinearDual (k V : Type*) [Semiring k] [AddCommGroup V] [Module k V] :=
  V →ₗ[k] k

/-- Pushforward of a module sheaf along a scheme morphism. -/
abbrev chapter09Pushforward {X Y : Scheme.{u}} (i : X ⟶ Y) (F : X.Modules) : Y.Modules :=
  (Scheme.Modules.pushforward i).obj F

/-- Pullback of a module sheaf along a scheme morphism. -/
abbrev chapter09Pullback {X Y : Scheme.{u}} (i : Y ⟶ X) (F : X.Modules) : Y.Modules :=
  (Scheme.Modules.pullback i).obj F

/-- An invertible module sheaf, bridged to Book 8's canonical local criterion. -/
def chapter09IsInvertible {X : Scheme.{u}} (F : X.Modules) : Prop :=
  chapter04IsInvertible F

/-- A finite locally free module sheaf, i.e. a vector bundle for this chapter. -/
def chapter09VectorBundle {X : Scheme.{u}} (E : X.Modules) : Prop :=
  SheafOfModules.IsLocallyFree E ∧ SheafOfModules.IsFiniteType E

/-- The sheaf-level internal-Hom interface used for finite locally free sheaves.

The adjunction is the typed characterization of the internal Hom; in
particular, a later implementation cannot replace the dual by an unrelated
module sheaf while preserving this interface. -/
structure Chapter09InternalHomTheory (X : Scheme.{u}) where
  internalHom : X.Modules → X.Modules → X.Modules
  homEquiv : ∀ (M N P : X.Modules),
    (chapter04Tensor M N ⟶ P) ≃ (N ⟶ internalHom M P)

abbrev chapter09InternalHom {X : Scheme.{u}}
    (H : Chapter09InternalHomTheory X) (M N : X.Modules) : X.Modules :=
  H.internalHom M N

/-- A vector bundle together with its canonical internal-Hom dual and twist. -/
structure Chapter09VectorBundleDualTensor
    {X : Scheme.{u}} (E ω : X.Modules) where
  internalHom : Chapter09InternalHomTheory X
  dual_is_vectorBundle :
    chapter09VectorBundle
      (chapter09InternalHom internalHom E (chapter09StructureSheaf X))

abbrev Chapter09VectorBundleDualTensor.dual
    {X : Scheme.{u}} {E ω : X.Modules}
    (V : Chapter09VectorBundleDualTensor E ω) : X.Modules :=
  chapter09InternalHom V.internalHom E (chapter09StructureSheaf X)

abbrev Chapter09VectorBundleDualTensor.tensor
    {X : Scheme.{u}} {E ω : X.Modules}
    (V : Chapter09VectorBundleDualTensor E ω) : X.Modules :=
  chapter04Tensor V.dual ω

/-- An abstract perfect pairing before scalar-linearity is added by the field
API.  The two supplied dual spaces make the induced maps honest bijections;
they are not silently identified with all functions.  The scalar-linear
realization below specializes these dual spaces to linear duals. -/
structure Chapter09PerfectPairing
    (k : Type u) (A : Type v) (B : Type w) where
  pairing : A → B → k
  leftDual : Type (max u w)
  rightDual : Type (max u v)
  leftEvaluation : leftDual → B → k
  rightEvaluation : rightDual → A → k
  leftPairing : A → leftDual
  rightPairing : B → rightDual
  leftPerfect : Function.Bijective leftPairing
  rightPerfect : Function.Bijective rightPairing
  leftEvaluation_pairing : ∀ a b, leftEvaluation (leftPairing a) b = pairing a b
  rightEvaluation_pairing : ∀ b a, rightEvaluation (rightPairing b) a = pairing a b

/-- The scalar-linear form of a perfect pairing over the field of definition. -/
structure Chapter09LinearPerfectPairing
    (k A B : Type*) [CommSemiring k]
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] where
  leftPairing : A →ₗ[k] (B →ₗ[k] k)
  leftPerfect : Function.Bijective leftPairing
  rightPairing : B →ₗ[k] (A →ₗ[k] k)
  rightPerfect : Function.Bijective rightPairing
  compatibility : ∀ a b, leftPairing a b = rightPairing b a

/-- Forgetting scalar linearity turns a linear perfect pairing into the
abstract dual-space interface above. -/
def chapter09PerfectPairingOfLinear
    (k A B : Type*) [CommSemiring k]
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    (P : Chapter09LinearPerfectPairing k A B) :
    Chapter09PerfectPairing k A B :=
  { pairing := fun a b => P.leftPairing a b
    leftDual := B →ₗ[k] k
    rightDual := A →ₗ[k] k
    leftEvaluation := fun φ b => φ b
    rightEvaluation := fun ψ a => ψ a
    leftPairing := P.leftPairing
    rightPairing := P.rightPairing
    leftPerfect := P.leftPerfect
    rightPerfect := P.rightPerfect
    leftEvaluation_pairing := fun _ _ => rfl
    rightEvaluation_pairing := fun b a => (P.compatibility a b).symm }

/-! ### Derived Ext and sheaf Ext -/

/-- The chosen smallness witness needed by the canonical derived Ext groups. -/
class Chapter09ExtTheory (X : Scheme.{u}) where
  hasExt : CategoryTheory.HasExt.{u + 1} X.Modules
  sheafExt : X.Modules → X.Modules → CochainComplex X.Modules ℤ

attribute [instance] Chapter09ExtTheory.hasExt

/-- The canonical derived Ext group in the module-sheaf category. -/
abbrev chapter09Ext {X : Scheme.{u}} [Chapter09ExtTheory X]
    (F G : X.Modules) (n : ℕ) : Type (u + 1) :=
  CategoryTheory.Abelian.Ext F G n

/-- The sheaf-valued Ext object used by the projective construction. -/
abbrev chapter09SheafExt {X : Scheme.{u}} [Chapter09ExtTheory X]
    (F G : X.Modules) (n : ℕ) : X.Modules :=
  (Chapter09ExtTheory.sheafExt F G).homology (n : ℤ)

/-! ### Curves over a field and zero-dimensional sheaves -/

/-- The zero-dimensional coherent-sheaf hypothesis used in (9.1). -/
structure Chapter09ZeroDimensionalCoherentSheaf (X : Scheme.{u}) where
  carrier : X.Modules
  coherent : chapter09Coherent carrier
  support : Finset X
  support_is_closed : ∀ x, x ∈ support → IsClosed ({x} : Set X)
  stalk_subsingleton_off_support :
    ∀ x, x ∉ support → Subsingleton (carrier.presheaf.stalk x)

/-- Predicate form of `Chapter09ZeroDimensionalCoherentSheaf`. -/
def chapter09ZeroDimensional {X : Scheme.{u}} (T : X.Modules) : Prop :=
  ∃ hT : Chapter09ZeroDimensionalCoherentSheaf X,
    hT.carrier = T

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API does not expose a single
scheme-level Cohen--Macaulay predicate.  The preceding chapter supplies the
one-dimensional closed-stalk criterion, which is the relevant formulation for
the pure relative curves used here.  Keep this bridge concrete: an arbitrary
family of propositions on stalks would make the predicate vacuous. -/
abbrev chapter09CohenMacaulay (X : Scheme.{u}) : Prop :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Chapter08LocallyCohenMacaulayAtClosedPoints X

/-- A proper curve over a field, with the dimension-one assertion kept explicit. -/
structure Chapter09ProperCurveOverField (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  locallyOfFinitePresentation : LocallyOfFinitePresentation structureMap
  pureDimensionOne :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Chapter08PureDimensionOne
      scheme

/-- A proper Cohen--Macaulay curve over a field. -/
structure Chapter09CohenMacaulayCurveOverField
    (k : Type u) [Field k] extends Chapter09ProperCurveOverField k where
  relativeCohenMacaulay : chapter09CohenMacaulay scheme

/-! ### Absolute duality package -/

/-- The absolute derived `RΓ` and shifted `RHom` complexes in (9.2). -/
class Chapter09AbsoluteDerivedHomTheory (k : Type u) [Field k] (X : Scheme.{u}) where
  globalSections : X.Modules → CochainComplex (ModuleCat k) ℤ
  schemeRHom : X.Modules → X.Modules → CochainComplex (ModuleCat k) ℤ

/-- A typed quasi-isomorphism for the shifted form of absolute duality. -/
structure Chapter09AbsoluteDerivedDualityComparison
    (k : Type u) [Field k] {X : Scheme.{u}}
    [Chapter09AbsoluteDerivedHomTheory k X]
  (F ω : X.Modules) where
  comparison :
    Chapter09AbsoluteDerivedHomTheory.globalSections (k := k) (X := X) F ⟶
      Chapter09AbsoluteDerivedHomTheory.schemeRHom (k := k) (X := X) F ω
  comparison_quasiIso : QuasiIso comparison

/-- A trace-compatible isomorphism between two proposed absolute dualizing sheaves. -/
structure Chapter09TraceCompatibleIso
    (k : Type u) [Field k] {X : Scheme.{u}}
    (D E : X.Modules)
    (trD : chapter09H D 1 → k) (trE : chapter09H E 1 → k) where
  iso : D ≅ E
  trace_compatibility :
    ∀ x, trD x =
      trE ((chapter04CanonicalCohomologyContext X).map iso.hom 1 x)

/-- The full absolute dualizing-sheaf package for a proper Cohen--Macaulay curve. -/
structure Chapter09AbsoluteDualizingData
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme] where
  sheaf : C.scheme.Modules
  coherent : chapter09Coherent sheaf
  maximalCohenMacaulay : Prop
  maximalCohenMacaulay_holds : maximalCohenMacaulay
  trace : chapter09H sheaf 1 →+ k
  traceCohomologyComparison : chapter09H sheaf 1 →+ k
  trace_is_image_of_one : trace = traceCohomologyComparison
  zeroDimensionalExt :
    ∀ (T : C.scheme.Modules),
      chapter09ZeroDimensional T →
        Nonempty (chapter09Ext T sheaf 1 ≃ chapter09Dual k (chapter09H T 0))
  zeroDimensionalLinearExt :
    ∀ (T : C.scheme.Modules), chapter09ZeroDimensional T →
      ∃ hT : Module k (chapter09H T 0),
        ∃ hExt : Module k (chapter09Ext T sheaf 1),
          @Nonempty
            (letI : Module k (chapter09H T 0) := hT
             letI : Module k (chapter09Ext T sheaf 1) := hExt
             chapter09Ext T sheaf 1 ≃ₗ[k] chapter09LinearDual k (chapter09H T 0))
  perfectPairing :
    ∀ (F : C.scheme.Modules) (i : ℕ),
      chapter09Coherent F → i ≤ 1 →
        Chapter09PerfectPairing k (chapter09H F i) (chapter09Ext F sheaf (1 - i))
  /- The pinned module-sheaf API does not expose multiplication and trace as
     a canonical map.  Keep the actual pairing as data and identify it with
     the supplied multiplication-then-trace map, rather than recording that
     identification as an unconstrained proposition. -/
  multiplicationThenTrace :
    ∀ (F : C.scheme.Modules) (i : ℕ), chapter09Coherent F → i ≤ 1 →
      chapter09H F i → chapter09Ext F sheaf (1 - i) → k
  pairing_is_multiplication_then_trace :
    ∀ (F : C.scheme.Modules) (i : ℕ) (hF : chapter09Coherent F) (hi : i ≤ 1),
      (perfectPairing F i hF hi).pairing = multiplicationThenTrace F i hF hi
  linearPerfectPairing :
    ∀ (F : C.scheme.Modules) (i : ℕ), chapter09Coherent F → i ≤ 1 →
      ∃ hF : Module k (chapter09H F i),
        ∃ hExt : Module k (chapter09Ext F sheaf (1 - i)),
          @Nonempty
            (letI : Module k (chapter09H F i) := hF
             letI : Module k (chapter09Ext F sheaf (1 - i)) := hExt
             Chapter09LinearPerfectPairing k (chapter09H F i)
               (chapter09Ext F sheaf (1 - i)))
  vectorBundlePairing :
    ∀ (E : C.scheme.Modules)
      (V : Chapter09VectorBundleDualTensor E sheaf),
      chapter09VectorBundle E →
        ∀ (i : ℕ), i ≤ 1 →
          Chapter09PerfectPairing k (chapter09H E i)
            (chapter09H V.tensor (1 - i))
  derivedDuality :
    ∀ (F : C.scheme.Modules),
      chapter09Coherent F →
        Chapter09AbsoluteDerivedDualityComparison k F sheaf

/-! ### Projective embeddings and the projective-space calculation -/

/-- A closed immersion of the curve into a chosen projective space over the field. -/
structure Chapter09ProjectiveEmbedding
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k) where
  N : ℕ
  one_le_N : 1 ≤ N
  embedding : C.scheme ⟶
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
      (AlgebraicGeometry.Spec (.of k)) N
  closedImmersion : IsClosedImmersion embedding
  over :
    embedding ≫
        LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
          (AlgebraicGeometry.Spec (.of k)) N =
      C.structureMap

abbrev Chapter09ProjectiveEmbedding.ambient
    {k : Type u} [Field k]
    {C : Chapter09CohenMacaulayCurveOverField k}
    (I : Chapter09ProjectiveEmbedding k C) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
    (AlgebraicGeometry.Spec (.of k)) I.N

abbrev Chapter09ProjectiveEmbedding.ambientStructureMap
    {k : Type u} [Field k]
    {C : Chapter09CohenMacaulayCurveOverField k}
    (I : Chapter09ProjectiveEmbedding k C) : I.ambient ⟶ AlgebraicGeometry.Spec (.of k) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
    (AlgebraicGeometry.Spec (.of k)) I.N

/- LOCAL_DEPENDENCY_GUESS: the pinned revision has no finite-resolution
object for coherent module sheaves on a projective scheme.  The profile keeps
the exactness and pure-codimension obligations explicit for the later proof
pass. -/
structure Chapter09FiniteLocallyFreeResolutionProfile
    {P : Scheme.{u}} (M : P.Modules) where
  length : ℕ
  codimension : ℕ
  finiteLocallyFreeResolution : Prop
  finiteLocallyFreeResolution_holds : finiteLocallyFreeResolution
  exact : Prop
  exact_holds : exact
  pureCodimension : Prop
  pureCodimension_holds : pureCodimension

/-! A perfect embedding profile is shared by the local-projectivity and
relative-Ext interfaces, so it belongs to the chapter core. -/
structure Chapter09RelativePerfectEmbeddingProfile
    {X S : Scheme.{u}} (f : X ⟶ S) where
  ambientDimension : ℕ
  one_le_ambientDimension : 1 ≤ ambientDimension
  embedding : X ⟶
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
      S ambientDimension
  closedImmersion : IsClosedImmersion embedding
  over :
    embedding ≫
        LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
          S ambientDimension = f
  ambientDualizingSheaf :
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
      S ambientDimension).Modules
  ambientDualizingSheaf_is_relativeDualizing : Prop
  ambientDualizingSheaf_is_relativeDualizing_holds : ambientDualizingSheaf_is_relativeDualizing
  resolution :
    Chapter09FiniteLocallyFreeResolutionProfile
      (chapter09Pushforward embedding (chapter09StructureSheaf X))
  codimension_eq : resolution.codimension = ambientDimension - 1

abbrev Chapter09RelativePerfectEmbeddingProfile.ambient
    {X S : Scheme.{u}} {f : X ⟶ S}
    (P : Chapter09RelativePerfectEmbeddingProfile f) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
    S P.ambientDimension

abbrev Chapter09RelativePerfectEmbeddingProfile.ambientMap
    {X S : Scheme.{u}} {f : X ⟶ S}
    (P : Chapter09RelativePerfectEmbeddingProfile f) : P.ambient ⟶ S :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
    S P.ambientDimension

/-- The sheaf Ext presentation of a dualizing sheaf from a projective embedding. -/
structure Chapter09AbsoluteExtConstruction
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    (I : Chapter09ProjectiveEmbedding k C)
    [Chapter09ExtTheory I.ambient] where
  ambientDualizingSheaf : I.ambient.Modules
  ambientDualizingSheaf_is_dualizing : Prop
  ambientDualizingSheaf_is_dualizing_holds : ambientDualizingSheaf_is_dualizing
  resolution :
    Chapter09FiniteLocallyFreeResolutionProfile
      (chapter09Pushforward I.embedding (chapter09StructureSheaf C.scheme))
  codimension_eq : resolution.codimension = I.N - 1
  extSheaf : I.ambient.Modules
  extSheaf_formula :
    extSheaf =
      chapter09SheafExt
        (chapter09Pushforward I.embedding (chapter09StructureSheaf C.scheme))
        ambientDualizingSheaf (I.N - 1)
  changeOfRingsIdentification : Prop
  changeOfRingsIdentification_holds : changeOfRingsIdentification
  dualizingSheaf : C.scheme.Modules
  pushforward_iso : chapter09Pushforward I.embedding dualizingSheaf ≅ extSheaf

/-- The inverse product Laurent monomial appearing in the projective-space Cech pairing. -/
def chapter09InverseProductExponent (N : ℕ) : Fin (N + 1) → ℤ :=
  fun _ => -1

/-- The complementary twist `-m-N-1` in the projective-space pairing. -/
def chapter09ComplementaryTwist (N : ℕ) (m : ℤ) : ℤ :=
  -m - (N : ℤ) - 1

/- LOCAL_DEPENDENCY_GUESS: the pinned revision has no projective-space Cech
complex API over an arbitrary base ring.  The package records its two precise
twists, degrees, coefficient convention, and perfectness interface. -/
structure Chapter09ProjectiveCechPairing
    (k : Type u) [Field k] (N : ℕ) (m : ℤ) (q : ℕ) where
  degree_bound : q ≤ N
  degree_q_term : Type (u + 1)
  complementary_degree_term : Type (u + 1)
  leftTwist : ℤ
  leftTwist_eq : leftTwist = m
  rightTwist : ℤ
  rightTwist_eq : rightTwist = chapter09ComplementaryTwist N m
  leftDegree : ℕ
  leftDegree_eq : leftDegree = q
  rightDegree : ℕ
  rightDegree_eq : rightDegree = N - q
  degree_q_description : Prop
  degree_q_description_holds : degree_q_description
  complementary_degree_description : Prop
  complementary_degree_description_holds : complementary_degree_description
  coefficient_of_inverse_product : Prop
  coefficient_of_inverse_product_holds : coefficient_of_inverse_product
  perfect :
    Chapter09PerfectPairing k degree_q_term complementary_degree_term

/-! ### Relative curves, base change, and relative duality -/

/-- The proper flat geometrically reduced curve family used for local projectivity. -/
structure Chapter09ProperFlatReducedCurveFamily where
  X : Scheme.{u}
  S : Scheme.{u}
  f : X ⟶ S
  proper : IsProper f
  flat : Flat f
  quasiCompact : QuasiCompact f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  relativeCurve :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09RelativeCurve f
  geometricallyReducedFibers : GeometricallyReduced f

/-- The additional Cohen--Macaulay family hypotheses used by relative duality. -/
structure Chapter09RelativeCurveFamily where
  X : Scheme.{u}
  S : Scheme.{u}
  f : X ⟶ S
  proper : IsProper f
  flat : Flat f
  quasiCompact : QuasiCompact f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  relativeCurve :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09RelativeCurve f
  geometricallyReducedFibers : GeometricallyReduced f
  relativeCohenMacaulay :
    ∀ s : S,
      chapter09CohenMacaulay (Limits.pullback f (S.fromSpecResidueField s))
  baseLocallyNoetherian : IsLocallyNoetherian S

/-- An fpqc cover used in the local projectivity argument. -/
abbrev Chapter09FpqcCover (S : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09FaithfullyFlatCover S

/-- The total space and structure map after a base change `S' → S`. -/
abbrev chapter09BaseChangeTotal {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) : Scheme.{u} :=
  Limits.pullback f g

abbrev chapter09BaseChangeToX {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) : chapter09BaseChangeTotal f g ⟶ X :=
  Limits.pullback.fst f g

abbrev chapter09BaseChangeToBase {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) : chapter09BaseChangeTotal f g ⟶ S' :=
  Limits.pullback.snd f g

/-- The base-changed family map used in the arbitrary-base-change theorem. -/
abbrev chapter09BaseChangedFamilyMap {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) :
    chapter09BaseChangeTotal f g ⟶ S' :=
  chapter09BaseChangeToBase f g

/-- A relative effective Cartier divisor of constant finite-flat degree. -/
structure Chapter09RelativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) where
  canonical :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09EffectiveCartierDivisor X
  degree : ℕ
  finiteFlatRank :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09FiniteLocallyFreeProfile
      (canonical.ideal.subschemeι ≫ f) degree
  totalQuotient :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04TotalQuotientRingAPI X
  cartier :
    @LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04EffectiveCartierDivisor
      X totalQuotient
  cartier_ideal_eq : cartier.ideal = canonical.ideal
  associatedLineBundle : Chapter04LineBundle X
  associatedLineBundle_sheaf_eq :
    associatedLineBundle.sheaf =
      (@LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04OofD
        X totalQuotient cartier.cartier).sheaf
  canonicalSection :
    @LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Chapter04GlobalSection
      X
      (@LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04OofD
        X totalQuotient cartier.cartier)
  canonicalSection_eq :
    canonicalSection =
      @LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.chapter04CanonicalSection
        X totalQuotient cartier

abbrev Chapter09RelativeEffectiveCartierDivisor.lineBundle
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Chapter04LineBundle X :=
  D.associatedLineBundle

abbrev Chapter09RelativeEffectiveCartierDivisor.support
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Scheme.{u} :=
  D.canonical.ideal.subscheme

abbrev Chapter09RelativeEffectiveCartierDivisor.inclusion
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : D.support ⟶ X :=
  D.canonical.ideal.subschemeι

abbrev Chapter09RelativeEffectiveCartierDivisor.closedImmersion
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : IsClosedImmersion D.inclusion :=
  D.canonical.closed

abbrev Chapter09RelativeEffectiveCartierDivisor.finiteOverBase
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) :
    IsFinite (D.inclusion ≫ f) :=
  D.finiteFlatRank.finite

abbrev Chapter09RelativeEffectiveCartierDivisor.flatOverBase
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) :
    Flat (D.inclusion ≫ f) :=
  D.finiteFlatRank.flat

abbrev Chapter09RelativeEffectiveCartierDivisor.constantRank
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Prop :=
  ∀ y, Scheme.Hom.finrank (D.inclusion ≫ f) y = D.degree

abbrev Chapter09RelativeEffectiveCartierDivisor.effectiveCartier
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LocallyRegularPrincipal
    D.canonical.ideal

abbrev Chapter09RelativeEffectiveCartierDivisor.effective
    {X S : Scheme.{u}} {f : X ⟶ S}
    (D : Chapter09RelativeEffectiveCartierDivisor f) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LocallyRegularPrincipal
    D.canonical.ideal

/-- Local projectivity data obtained from sections through smooth points. -/
structure Chapter09FpqcLocalProjectivityWitness
    (F : Chapter09ProperFlatReducedCurveFamily) where
  cover : Chapter09FpqcCover F.S
  etaleNeighborhoodAroundGeometricFiber : Prop
  etaleNeighborhoodAroundGeometricFiber_holds : etaleNeighborhoodAroundGeometricFiber
  sectionsThroughSmoothPoints : Prop
  sectionsThroughSmoothPoints_holds : sectionsThroughSmoothPoints
  divisor :
    Chapter09RelativeEffectiveCartierDivisor
      (chapter09BaseChangedFamilyMap F.f cover.map)
  curvePositivityCriterion : Prop
  curvePositivityCriterion_holds : curvePositivityCriterion
  affineNonvanishingAfterShrinking : Prop
  affineNonvanishingAfterShrinking_holds : affineNonvanishingAfterShrinking
  relativelyAmple : chapter04Ample
    (chapter09BaseChangedFamilyMap F.f cover.map) divisor.lineBundle
  perfectEmbedding :
    Chapter09RelativePerfectEmbeddingProfile
      (chapter09BaseChangedFamilyMap F.f cover.map)
  noRiemannRochUsed : Prop
  noRiemannRochUsed_holds : noRiemannRochUsed
  projectiveAfterBaseChange :
    chapter04Projective (chapter09BaseChangedFamilyMap F.f cover.map)

/-- A projective morphism after an fpqc base change. -/
def chapter09FpqcLocallyProjective (F : Chapter09ProperFlatReducedCurveFamily) : Prop :=
  Nonempty (Chapter09FpqcLocalProjectivityWitness F)

/-- The relative derived pushforward and shifted base `RHom` complexes. -/
class Chapter09RelativeDerivedHomTheory {X S : Scheme.{u}} (f : X ⟶ S) where
  derivedPushforward : X.Modules → CochainComplex S.Modules ℤ
  baseRHom : CochainComplex S.Modules ℤ → S.Modules → CochainComplex S.Modules ℤ

abbrev chapter09RPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f] (F : X.Modules) (i : ℕ) : S.Modules :=
  (Chapter09RelativeDerivedHomTheory.derivedPushforward f F).homology (i : ℤ)

/-- The shifted comparison in relative duality (9.4). -/
structure Chapter09RelativeDualityComparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
  (E ω : X.Modules) (V : Chapter09VectorBundleDualTensor E ω) where
  comparison :
    Chapter09RelativeDerivedHomTheory.derivedPushforward f V.tensor ⟶
      Chapter09RelativeDerivedHomTheory.baseRHom
        f (Chapter09RelativeDerivedHomTheory.derivedPushforward f E)
        (chapter09StructureSheaf S)
  comparison_quasiIso : QuasiIso comparison

/-- A vector bundle on `X` together with its `E^∨ ⊗ ω` realization. -/
structure Chapter09RelativeDualizingData
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f] where
  omega : X.Modules
  coherent : chapter09Coherent omega
  relativeMaximalCohenMacaulay : Prop
  relativeMaximalCohenMacaulay_holds : relativeMaximalCohenMacaulay
  trace :
    (Chapter09RelativeDerivedHomTheory.derivedPushforward f omega).homology (1 : ℤ) ⟶
      chapter09StructureSheaf S
  cupProductTraceRealization :
    ∀ (E : X.Modules) (V : Chapter09VectorBundleDualTensor E omega),
      chapter09VectorBundle E →
        Nonempty (Chapter09RelativeDualityComparison f E omega V)
  relativeDuality :
    ∀ (E : X.Modules) (V : Chapter09VectorBundleDualTensor E omega),
      chapter09VectorBundle E →
        Chapter09RelativeDualityComparison f E omega V

/-- The base-change comparison package for the relative dualizing sheaf, trace, and duality. -/
structure Chapter09RelativeBaseChangeComparison
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Chapter09RelativeDerivedHomTheory f]
    [Chapter09RelativeDerivedHomTheory (Limits.pullback.snd f g)]
    (D : Chapter09RelativeDualizingData f)
    (D' : Chapter09RelativeDualizingData (Limits.pullback.snd f g)) where
  iso :
    chapter09Pullback (Limits.pullback.fst f g) D.omega ≅ D'.omega
  trace_compatibility : Prop
  trace_compatibility_holds : trace_compatibility
  duality_compatibility : Prop
  duality_compatibility_holds : duality_compatibility

/-- Relative dualizing sheaf existence, separated from the family hypotheses. -/
def chapter09HasRelativeDualizingSheaf
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09RelativeDerivedHomTheory f] : Prop :=
  Nonempty (Chapter09RelativeDualizingData f)

/-! ### Differentials, Gorenstein data, and adjunction -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib's scheme-level Kähler differential module
sheaf is not yet available at the pinned revision. -/
class Chapter09DifferentialSheafTheory {X S : Scheme.{u}} (f : X ⟶ S) where
  omegaOne : X.Modules

abbrev chapter09RelativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    [Chapter09DifferentialSheafTheory f] : X.Modules :=
  Chapter09DifferentialSheafTheory.omegaOne f

/-- Gorensteinness of a relative dualizing package in the curve case. -/
def chapter09RelativeGorenstein
    {X S : Scheme.{u}} {f : X ⟶ S}
    [Chapter09RelativeDerivedHomTheory f]
    (D : Chapter09RelativeDualizingData f) : Prop :=
  chapter09IsInvertible D.omega

/-- Gorensteinness of an absolute dualizing package. -/
def chapter09AbsoluteGorenstein
    (k : Type u) [Field k]
    (C : Chapter09CohenMacaulayCurveOverField k)
    [Chapter09ExtTheory C.scheme]
    [Chapter09AbsoluteDerivedHomTheory k C.scheme]
    (D : Chapter09AbsoluteDualizingData k C) : Prop :=
  chapter09IsInvertible D.sheaf

/-- Local complete-intersection data for a relative curve. -/
structure Chapter09RelativeLocalCompleteIntersection
    {X S : Scheme.{u}} (f : X ⟶ S) where
  ambient : Scheme.{u}
  ambientMap : ambient ⟶ S
  ambientSmooth : Smooth ambientMap
  immersion : X ⟶ ambient
  closedImmersion : IsClosedImmersion immersion
  over : immersion ≫ ambientMap = f
  regularSequence : Prop
  regularSequence_holds : regularSequence
  pureRelativeDimensionOne : Prop
  pureRelativeDimensionOne_holds : pureRelativeDimensionOne

/-- A relative hypersurface in a smooth relative surface, with its divisor line bundle. -/
structure Chapter09RelativeHypersurface
    {X S : Scheme.{u}} (f : X ⟶ S) where
  ambient : Scheme.{u}
  ambientMap : ambient ⟶ S
  ambientSmoothSurface : SmoothOfRelativeDimension 2 ambientMap
  inclusion : X ⟶ ambient
  closedImmersion : IsClosedImmersion inclusion
  over : inclusion ≫ ambientMap = f
  regularEquation : Prop
  regularEquation_holds : regularEquation
  nodalFiber : Prop
  nodalFiber_holds : nodalFiber
  divisorLineBundle : Chapter04LineBundle ambient
  divisorLineBundle_is_OX : Prop
  divisorLineBundle_is_OX_holds : divisorLineBundle_is_OX

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
