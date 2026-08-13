import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

/-!
Shared interfaces for Chapter 12.

The pinned Mathlib checkout supplies schemes, ideal sheaves, pullbacks, and the
usual finiteness properties, but it does not yet supply the relative Hilbert
scheme, relative symmetric powers, or the book's relative-projectivity and
very-ampleness predicates. The small interfaces below keep those seams
explicit. They are dependency interfaces, not replacement proofs of the
geometric theorems stated later in the chapter.
-/

abbrev Chapter12NumericalPolynomial := Chapter08NumericalPolynomial

/-!
The five book-facing predicates below are aliases or wrappers around the
canonical witnesses supplied by the preceding chapters.  In particular, a
relative projective space is the fixed `ℙ^r` construction, not an arbitrary
scheme carrying a marker proposition.
-/
abbrev chapter12IsProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop :=
  Chapter09ProjectiveMorphism f

def chapter12IsQuasiProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter11QuasiProjectivePresentation f)

abbrev chapter12IsInvertibleSheaf {X : Scheme} (L : X.Modules) : Prop :=
  chapter09IsInvertibleSheaf L

def chapter12IsRelativelyVeryAmple {X S : Scheme} (f : X ⟶ S)
    (L : X.Modules) : Prop :=
  ∃ hL : chapter12IsInvertibleSheaf L,
    chapter09RelativelyVeryAmple f
      { module := L, isInvertible := hL }

structure Chapter12ProjectiveSpaceWitness (X S : Scheme) (f : X ⟶ S) (r : ℕ) where
  iso : X ≅ chapter02ProjectiveSpace S r
  over : iso.hom ≫ chapter02ProjectiveSpaceProjection S r = f

def chapter12IsProjectiveSpaceOver (X S : Scheme) (f : X ⟶ S) (r : ℕ) : Prop :=
  Nonempty (Chapter12ProjectiveSpaceWitness X S f r)

abbrev chapter12HasRelativeDimension {X S : Scheme} (f : X ⟶ S) (r : ℕ) : Prop :=
  SmoothOfRelativeDimension r f

/-- A book-facing relatively very ample invertible sheaf. -/
structure Chapter12RelativeVeryAmple {X S : Scheme} (f : X ⟶ S) where
  /-- The underlying sheaf of modules. -/
  lineBundle : X.Modules
  /-- The invertibility interface supplied by the line-bundle chapters. -/
  lineBundle_invertible : chapter12IsInvertibleSheaf lineBundle
  /-- The relative very-ampleness interface supplied by the projective chapters. -/
  relativelyVeryAmple : chapter12IsRelativelyVeryAmple f lineBundle

/-- The standing projective, finitely presented, polarized family of Section 12.1. -/
structure Chapter12ProjectiveFamilySetup where
  base : Scheme
  total : Scheme
  structureMap : total ⟶ base
  base_noetherian : IsNoetherian base
  structureMap_finite_presentation : LocallyOfFinitePresentation structureMap
  /-- This is the missing relative-projective predicate. -/
  structureMap_projective : chapter12IsProjectiveMorphism structureMap
  polarization : Chapter12RelativeVeryAmple structureMap

attribute [instance] Chapter12ProjectiveFamilySetup.base_noetherian
attribute [instance] Chapter12ProjectiveFamilySetup.structureMap_finite_presentation

/-- A projective-space embedding used by the Grassmannian construction. -/
structure Chapter12ProjectiveEmbedding (D : Chapter12ProjectiveFamilySetup) where
  r : ℕ
  ambient : Scheme
  ambientMap : ambient ⟶ D.base
  embedding : D.total ⟶ ambient
  over : embedding ≫ ambientMap = D.structureMap
  closed : IsClosedImmersion embedding
  /-- The identification of `ambient` with `ℙ^r_D.base`. -/
  ambient_is_projective_space :
    chapter12IsProjectiveSpaceOver ambient D.base ambientMap r

/-- An object of the category of schemes over a fixed base. -/
abbrev Chapter12SchemeOver (S : Scheme) := Over S

/-- The base change `X_T` used throughout the functor definitions. -/
def chapter12BaseChange (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) : Scheme :=
  pullback D.structureMap T.hom

/-- The projection `X_T ⟶ X`. -/
def chapter12BaseChangeToTotal (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) : chapter12BaseChange D T ⟶ D.total :=
  pullback.fst D.structureMap T.hom

/-- The projection `X_T ⟶ T`. -/
def chapter12BaseChangeToTest (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) : chapter12BaseChange D T ⟶ T.left :=
  pullback.snd D.structureMap T.hom

@[simp]
theorem chapter12BaseChange_condition (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) :
    chapter12BaseChangeToTotal D T ≫ D.structureMap =
      chapter12BaseChangeToTest D T ≫ T.hom := by
  exact pullback.condition

/- The morphism of base changes induced by a morphism of test schemes.  It is
   the map along which an ideal sheaf must be comapped under inverse image. -/
noncomputable def chapter12BaseChangeMap (D : Chapter12ProjectiveFamilySetup)
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U) :
    chapter12BaseChange D T ⟶ chapter12BaseChange D U :=
  pullback.lift
    (chapter12BaseChangeToTotal D T)
    (chapter12BaseChangeToTest D T ≫ g.left) (by
      rw [Category.assoc, g.w]
      exact chapter12BaseChange_condition D T)

/-- A geometric point, represented by a point with values in a field. -/
structure Chapter12GeometricPoint (T : Scheme) where
  K : Type*
  [field : Field K]
  [algebraicallyClosed : IsAlgClosed K]
  point : Spec (.of K) ⟶ T
  basePoint : T
  basePoint_spec : point (⊥ : PrimeSpectrum K) = basePoint

attribute [instance] Chapter12GeometricPoint.field
attribute [instance] Chapter12GeometricPoint.algebraicallyClosed

/-- The scheme-theoretic projection of a closed family to its test scheme. -/
def chapter12FamilyProjection (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base)
    (I : (chapter12BaseChange D T).IdealSheafData) : I.subscheme ⟶ T.left :=
  I.subschemeι ≫ chapter12BaseChangeToTest D T

/-- A closed subscheme of `X_T`, represented by its ideal sheaf. -/
structure Chapter12ClosedFamily (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) where
  ideal : (chapter12BaseChange D T).IdealSheafData
  flat : Flat (chapter12FamilyProjection D T ideal)
  finitePresentation : LocallyOfFinitePresentation (chapter12FamilyProjection D T ideal)

/-!
The fiber length is Mathlib's canonical finite-rank function.  The Hilbert
function remains attached to the canonical Chapter 8 numerical data supplied
for a family; Chapter 12 only packages its eventual comparison with that
data.
-/
abbrev Chapter12FiberLength {X T : Scheme} (f : X ⟶ T) (t : T) : ℕ :=
  Scheme.Hom.finrank f t

abbrev Chapter12FiberHilbertFunction := ℕ → ℕ

/-- The numerical Hilbert function attached to a closed family and a geometric fiber. -/
structure Chapter12HilbertPolynomialTheory (D : Chapter12ProjectiveFamilySetup) where
  fiberHilbertFunction : {T : Chapter12SchemeOver D.base} →
    Chapter12ClosedFamily D T → Chapter12GeometricPoint T.left →
      Chapter12FiberHilbertFunction

/-- Eventual agreement of a fiber Hilbert function with a polynomial. -/
def chapter12HasFiberHilbertPolynomial
    {D : Chapter12ProjectiveFamilySetup}
    (H : Chapter12HilbertPolynomialTheory D)
    {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
  (t : Chapter12GeometricPoint T.left) (P : Chapter12NumericalPolynomial) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    P.value n = (H.fiberHilbertFunction Z t n : ℤ)

/-- The inclusion of the closed family in the base change. -/
def chapter12FamilyInclusion (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    Z.ideal.subscheme ⟶ chapter12BaseChange D T :=
  Z.ideal.subschemeι

/-- The underlying scheme of a closed family. -/
abbrev chapter12FamilyCarrier (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) (Z : Chapter12ClosedFamily D T) : Scheme :=
  Z.ideal.subscheme

theorem chapter12FamilyInclusion_isClosedImmersion
    (D : Chapter12ProjectiveFamilySetup) (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    IsClosedImmersion (chapter12FamilyInclusion D T Z) := by
  change IsClosedImmersion Z.ideal.subschemeι
  infer_instance

theorem chapter12Family_isFlat
    (D : Chapter12ProjectiveFamilySetup) (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    Flat (chapter12FamilyProjection D T Z.ideal) := by
  exact Z.flat

theorem chapter12Family_isFinitelyPresented
    (D : Chapter12ProjectiveFamilySetup) (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    LocallyOfFinitePresentation (chapter12FamilyProjection D T Z.ideal) := by
  exact Z.finitePresentation

/-- A family satisfying the fixed fiber-polynomial condition. -/
structure Chapter12HilbertFamily (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (T : Chapter12SchemeOver D.base) (P : Chapter12NumericalPolynomial) where
  closed : Chapter12ClosedFamily D T
  fiber_polynomial : ∀ t : Chapter12GeometricPoint T.left,
    chapter12HasFiberHilbertPolynomial H closed t P

/- The inverse-image operation is functorial data, not something that follows
   from a bare nonemptiness statement.  Keeping its identity and composition
   laws in the interface makes the contravariant functor below honest even
   while the ideal-sheaf flatness proof remains a dependency seam. -/
structure Chapter12HilbertFamilyPullbackData
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D) where
  pullback : {P : Chapter12NumericalPolynomial} →
    {T U : Chapter12SchemeOver D.base} → (g : T ⟶ U) →
      Chapter12HilbertFamily D H U P → Chapter12HilbertFamily D H T P
  /-- The chosen pullback is the scheme-theoretic inverse image of the ideal. -/
  pullback_ideal : ∀ {P : Chapter12NumericalPolynomial}
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (Z : Chapter12HilbertFamily D H U P),
    (pullback g Z).closed.ideal =
      Z.closed.ideal.comap (chapter12BaseChangeMap D g)
  pullback_id : ∀ {P : Chapter12NumericalPolynomial}
    {T : Chapter12SchemeOver D.base} (Z : Chapter12HilbertFamily D H T P),
    pullback (𝟙 T) Z = Z
  pullback_comp : ∀ {P : Chapter12NumericalPolynomial}
    {T U V : Chapter12SchemeOver D.base} (g : T ⟶ U) (h : U ⟶ V)
    (Z : Chapter12HilbertFamily D H V P),
    pullback g (pullback h Z) = pullback (g ≫ h) Z

theorem chapter12_hilbert_family_pullback_data_exists
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    : Nonempty (Chapter12HilbertFamilyPullbackData D H) := by
  sorry

noncomputable def chapter12HilbertFamilyPullbackData
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D) :
    Chapter12HilbertFamilyPullbackData D H :=
  Classical.choice (chapter12_hilbert_family_pullback_data_exists D H)

/-- Scheme-theoretic inverse image of a Hilbert family along a map of tests. -/
noncomputable def chapter12PullbackFamily
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (Z : Chapter12HilbertFamily D H U P) :
    Chapter12HilbertFamily D H T P :=
  (chapter12HilbertFamilyPullbackData D H).pullback g Z

theorem chapter12PullbackFamily_ideal
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (Z : Chapter12HilbertFamily D H U P) :
    (chapter12PullbackFamily D H g Z).closed.ideal =
      Z.closed.ideal.comap (chapter12BaseChangeMap D g) := by
  exact (chapter12HilbertFamilyPullbackData D H).pullback_ideal g Z

theorem chapter12PullbackFamily_id
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial} {T : Chapter12SchemeOver D.base}
    (Z : Chapter12HilbertFamily D H T P) :
    chapter12PullbackFamily D H (𝟙 T) Z = Z := by
  exact (chapter12HilbertFamilyPullbackData D H).pullback_id Z

theorem chapter12PullbackFamily_comp
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T U V : Chapter12SchemeOver D.base} (g : T ⟶ U) (h : U ⟶ V)
    (Z : Chapter12HilbertFamily D H V P) :
    chapter12PullbackFamily D H g (chapter12PullbackFamily D H h Z) =
      chapter12PullbackFamily D H (g ≫ h) Z := by
  exact (chapter12HilbertFamilyPullbackData D H).pullback_comp g h Z

/-- The constant numerical polynomial `d`. -/
def chapter12ConstantPolynomial (d : ℕ) : Chapter12NumericalPolynomial :=
  { polynomial := Polynomial.C (d : ℚ)
    integer_valued := by sorry
    integer_valued_on_integers := by sorry }

@[simp]
theorem chapter12ConstantPolynomial_eval (d n : ℕ) :
    (chapter12ConstantPolynomial d).eval n = (d : ℚ) := by
  sorry

/-- A finite locally free morphism of rank `d`, with the fiber-length interface explicit. -/
structure Chapter12FiniteLocallyFreeRank
    {X T : Scheme} (f : X ⟶ T) (d : ℕ) : Prop where
  finite : IsFinite f
  flat : Flat f
  finitePresentation : LocallyOfFinitePresentation f
  rank : ∀ t : T, Chapter12FiberLength f t = d

/-- The data that identifies the finite-length open locus for a quasi-projective
    scheme with the families in a projective compactification which avoid the
    boundary.  The boundary image is recorded as a closed subscheme of the
    compactification parameter space, rather than as an unstructured property
    of the resulting open. -/
structure Chapter12QuasiProjectiveLengthLocusData
    {X S : Scheme} (f : X ⟶ S) (d : ℕ) where
  compactification : Scheme
  compactificationToBase : compactification ⟶ S
  compactification_projective : chapter12IsProjectiveMorphism compactificationToBase
  openImmersion : X ⟶ compactification
  open_is_open : IsOpenImmersion openImmersion
  open_over : openImmersion ≫ compactificationToBase = f
  compactificationParameter : Scheme
  compactificationParameterToBase : compactificationParameter ⟶ S
  compactificationParameter_projective :
    chapter12IsProjectiveMorphism compactificationParameterToBase
  universalFamily : Scheme
  universalFamilyToParameter : universalFamily ⟶ compactificationParameter
  universalFamilyToCompactification : universalFamily ⟶ compactification
  universalFamily_over :
    universalFamilyToCompactification ≫ compactificationToBase =
      universalFamilyToParameter ≫ compactificationParameterToBase
  universalFamilyToPullback : universalFamily ⟶
    pullback compactificationToBase compactificationParameterToBase
  universalFamilyToPullback_fst :
    universalFamilyToPullback ≫
        pullback.fst compactificationToBase compactificationParameterToBase =
      universalFamilyToCompactification
  universalFamilyToPullback_snd :
    universalFamilyToPullback ≫
        pullback.snd compactificationToBase compactificationParameterToBase =
      universalFamilyToParameter
  universalFamily_closed : IsClosedImmersion universalFamilyToPullback
  universalFamily_finite_locally_free :
    Chapter12FiniteLocallyFreeRank universalFamilyToParameter d
  boundary : Scheme
  boundaryToCompactification : boundary ⟶ compactification
  boundary_closed : IsClosedImmersion boundaryToCompactification
  boundaryFamily : Scheme
  boundaryFamilyToUniversalFamily : boundaryFamily ⟶ universalFamily
  boundaryFamilyToBoundary : boundaryFamily ⟶ boundary
  boundaryFamilyToParameter : boundaryFamily ⟶ compactificationParameter
  boundaryFamily_to_compactification :
    boundaryFamilyToUniversalFamily ≫ universalFamilyToCompactification =
      boundaryFamilyToBoundary ≫ boundaryToCompactification
  boundaryFamily_to_parameter :
    boundaryFamilyToUniversalFamily ≫ universalFamilyToParameter =
      boundaryFamilyToParameter
  boundaryFamily_closed_in_universal :
    IsClosedImmersion boundaryFamilyToUniversalFamily
  boundaryFamily_finite : IsFinite boundaryFamilyToParameter
  boundaryImage : Scheme
  boundaryImageToParameter : boundaryImage ⟶ compactificationParameter
  boundaryImage_closed : IsClosedImmersion boundaryImageToParameter
  boundaryFamilyToImage : boundaryFamily ⟶ boundaryImage
  boundaryFamily_to_image :
    boundaryFamilyToImage ≫ boundaryImageToParameter =
      boundaryFamilyToParameter
  boundaryImage_range :
    Set.range boundaryImageToParameter = Set.range boundaryFamilyToParameter
  lengthLocus : compactificationParameter.Opens
  lengthLocus_complement :
    (lengthLocus : Set compactificationParameter) =
      (Set.range boundaryImageToParameter)ᶜ
  lengthLocus_family_iff :
    ∀ {T : Scheme} (q : T ⟶ compactificationParameter),
      (∃ h : T ⟶ lengthLocus.toScheme,
        h ≫ lengthLocus.ι = q) ↔
        ∃ h : pullback universalFamilyToParameter q ⟶ X,
          h ≫ openImmersion =
            pullback.fst universalFamilyToParameter q ≫
              universalFamilyToCompactification

/- LOCAL_DEPENDENCY_GUESS: the preceding Hilbert-polynomial chapters should
  supply these two standard comparison theorems. They connect the numerical
  fiber Hilbert polynomial with geometric fiber length and use projectivity to
  turn constant zero-dimensional fibers into a finite morphism. -/
structure Chapter12HilbertLengthCompatibility
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D) : Prop where
  polynomial_iff_fiber_length :
    ∀ {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
      (t : Chapter12GeometricPoint T.left) (d : ℕ),
      chapter12HasFiberHilbertPolynomial H Z t (chapter12ConstantPolynomial d) ↔
        Chapter12FiberLength (chapter12FamilyProjection D T Z.ideal) t.basePoint = d
  finite_of_constant_fiber_length :
    ∀ {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
      (d : ℕ),
      (∀ t : T.left,
        Chapter12FiberLength (chapter12FamilyProjection D T Z.ideal) t = d) →
        IsFinite (chapter12FamilyProjection D T Z.ideal)

def chapter12IdealSheafContains {X : Scheme}
    (I J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, I.ideal U ≤ J.ideal U

/-!
The ideal-sheaf representation is the set-valued part of the functor: an
object is an ideal sheaf, not an arbitrary quotient object with a chosen
isomorphic presentation.
-/

theorem chapter12_family_ideal_kernel
    (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base}
    (Z : Chapter12ClosedFamily D T) :
    (chapter12FamilyInclusion D T Z).ker = Z.ideal := by
  simp [chapter12FamilyInclusion]

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
