import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.Polynomial.HilbertPoly
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section04SerreCriteria
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section05TensorPowersAndOperations
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies

/-!
# Chapter 14: shared synthesis interfaces

The source chapter is a synthesis of the preceding relative-projective and Hilbert
constructions.  The pinned Mathlib tree supplies absolute `Proj`, its standard-open
calculation, and the Hilbert-polynomial algebra.  It does not yet supply the book's
relative Hilbert and symmetric-power objects, so the small data-bearing interfaces below
keep those dependencies explicit for the later reconciliation pass.
-/

noncomputable section

universe u v

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14

open CategoryTheory
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

/-! ## Elementary reusable predicates -/

/-- The numerical-polynomial interface already established in Chapter 8.

Keeping the integrality witnesses in the type prevents a later Hilbert functor
from accepting an arbitrary rational polynomial as if it were a Hilbert
polynomial. -/
abbrev Chapter14NumericalPolynomial :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Chapter08NumericalPolynomial

/-- A property which holds for every sufficiently large tensor degree. -/
def Chapter14Eventually {α : Type*} (P : ℕ → α → Prop) (x : α) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → P n x

/-- The non-dependent spelling of eventual truth, useful for asymptotic statements. -/
def chapter14EventuallyHolds (P : ℕ → Prop) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → P n

/-- A function to a discrete invariant is locally constant in the Zariski topology. -/
def chapter14LocallyConstant {S α : Type*} [TopologicalSpace S] (v : S → α) : Prop :=
  ∀ s : S, ∃ U : Set S, IsOpen U ∧ s ∈ U ∧ ∀ t, t ∈ U → v t = v s

/-- The constant numerical polynomial used for length `d`. -/
def chapter14ConstantHilbertPolynomial (d : ℕ) : Chapter14NumericalPolynomial :=
  { polynomial := Polynomial.C (d : ℚ)
    integer_valued := by
      intro n
      exact ⟨d, by simp⟩
    integer_valued_on_integers := by
      intro n
      exact ⟨d, by simp⟩ }

/-! ## Canonical absolute graded objects -/

/-- A compact carrier for the internally graded commutative rings used by the chapter. -/
structure Chapter14GradedAlgebra (A σ : Type*) [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] where
  component : ℕ → σ
  graded : GradedRing component

instance chapter14GradedAlgebra.gradedRing
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) : GradedRing G.component := G.graded

/-- The scheme supplied by Mathlib for the projective spectrum of `G`. -/
abbrev chapter14Proj {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) : Scheme :=
  AlgebraicGeometry.Proj G.component

/-- The homogeneous degree-zero localization used for a standard projective chart. -/
abbrev chapter14ChartRing {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) {n : ℕ} (f : A)
    (_hf : f ∈ G.component n) (_hn : 0 < n) : Type _ :=
  HomogeneousLocalization.Away G.component f

/-- The standard open `D₊(f)` on the projective spectrum. -/
def chapter14StandardOpen {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) {n : ℕ} (f : A)
    (_hf : f ∈ G.component n) (_hn : 0 < n) : (chapter14Proj G).Opens :=
  AlgebraicGeometry.Proj.basicOpen G.component f

/-- The Veronese component family `A^(d)_n = A_(nd)`. -/
def chapter14VeroneseComponent {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (d : ℕ) : ℕ → σ :=
  fun n => G.component (n * d)

/-!
The grading on the Veronese family is mathematically canonical.  It is not currently
packaged as a constructor in the pinned graded-algebra API, so callers pass that grading
certificate explicitly; this is a local dependency boundary, not an additional theorem.
-/

/-- A Veronese graded algebra with its canonical component family. -/
structure Chapter14VeroneseData {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
(G : Chapter14GradedAlgebra A σ) (d : ℕ) where
  graded : GradedRing (chapter14VeroneseComponent G d)

/-! ## Book-facing sheaf and family interfaces -/

/-- A rank-one locally free module sheaf, using the canonical Chapter 4 predicate. -/
abbrev chapter14IsInvertibleSheaf {X : Scheme.{u}} (L : X.Modules) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04IsInvertible L

/-- The fpqc cover data needed by the descent statements. -/
structure Chapter14FpqcCoverData {S T : Scheme} (g : T ⟶ S) where
  flat : Flat g
  surjective : Surjective g
  quasiCompact : QuasiCompact g

/-- The finite locally free module and tautological sheaf underlying a projective bundle. -/
structure Chapter14ProjectiveBundleData (S : Scheme) extends Chapter04ProjectiveBundle S

namespace Chapter14ProjectiveBundleData

abbrev coefficient {S : Scheme} (P : Chapter14ProjectiveBundleData S) : S.Modules := P.E

abbrev coefficientFiniteLocallyFree {S : Scheme}
    (P : Chapter14ProjectiveBundleData S) := P.finiteLocallyFree

abbrev tautologicalIsInvertible {S : Scheme}
    (P : Chapter14ProjectiveBundleData S) := P.tautological_isInvertible

abbrev universalQuotientIsEpi {S : Scheme}
    (P : Chapter14ProjectiveBundleData S) := P.universalQuotient_is_epi

abbrev projectionIsProper {S : Scheme}
    (P : Chapter14ProjectiveBundleData S) := P.projection_isProper

end Chapter14ProjectiveBundleData

/-- A relative locally closed projective presentation used for quasi-projectivity. -/
structure Chapter14QuasiProjectiveMorphismData {X S : Scheme} (f : X ⟶ S) where
  projectiveBundle : Chapter14ProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.space
  immersion : IsImmersion embedding
  overBase : embedding ≫ projectiveBundle.projection = f
  /-- The finiteness data needed when this presentation is used as a
      quasi-projective family in the quotient and Hilbert constructions. -/
  quasiCompact : QuasiCompact f
  finitePresentation : LocallyOfFinitePresentation f
  separated : IsSeparated f

/-- The group, smoothness, properness, and connected-fiber data of a polarized
abelian scheme.  The later moduli chapters may refine the final connectedness
field to the canonical geometric-fiber predicate. -/
structure Chapter14AbelianSchemeCore {A S : Scheme} (f : A ⟶ S) where
  [group : GrpObj (Over.mk f)]
  [commutative : IsCommMonObj (Over.mk f)]
  smooth : Smooth f
  proper : IsProper f
  geometricallyConnectedFibers : GeometricallyConnected f

/- The preceding Chapter 4 interface is the canonical book-facing line-bundle
object.  Keeping this as an abbreviation preserves the source vocabulary while
ensuring tensor, pullback, and invertibility all use one representation. -/
abbrev Chapter14LineBundle (X : Scheme) := Chapter04LineBundle X

/- A family of twisting sheaves indexed by the integral twist. -/
structure Chapter14TwistingSheafFamily (X : Scheme) where
  sheaf : ℤ → Chapter14LineBundle X

/-- A coherent coefficient sheaf together with the properties used in the Hilbert package. -/
structure Chapter14CoherentSheaf (X : Scheme) where
  sheaf : X.Modules
  isQuasiCoherent : sheaf.IsQuasicoherent
  isFiniteType : sheaf.IsFiniteType
  isFinitePresentation : sheaf.IsFinitePresentation

theorem chapter14CoherentSheaf_finiteTypeQuasiCoherent
    {X : Scheme} (F : Chapter14CoherentSheaf X) :
    chapter04FiniteTypeQuasiCoherent F.sheaf := by
  exact ⟨F.isQuasiCoherent, F.isFiniteType⟩

/-- A projective witness over a fixed base morphism. -/
structure Chapter14ProjectiveMorphismData {X S : Scheme} (f : X ⟶ S) where
  projectiveBundle : Chapter14ProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.space
  embedding_closed : IsClosedImmersion embedding
  overBase : embedding ≫ projectiveBundle.projection = f

/-- The witness carried by a relative very-ample line bundle.

The immersion is deliberately not assumed closed: properness is the separate hypothesis
which upgrades it to a projective (closed) embedding.  The displayed isomorphism keeps the
polarization attached to the embedding rather than recording only an ambient scheme. -/
structure Chapter14VeryAmpleEmbeddingData {X S : Scheme} {f : X ⟶ S}
    (L : Chapter14LineBundle X) where
  projectiveBundle : Chapter14ProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.space
  immersion : IsImmersion embedding
  overBase : embedding ≫ projectiveBundle.projection = f
  pullbackLineBundle : L.sheaf ≅
    (Scheme.Modules.pullback embedding).obj projectiveBundle.tautological

/-- The hypotheses used by the relative Hilbert and cohomology package. -/
structure Chapter14ProjectiveFlatFamilyData {X S : Scheme} (f : X ⟶ S)
    extends Chapter14ProjectiveMorphismData f where
  flat : Flat f
  quasiCompact : QuasiCompact f
  quasiSeparated : QuasiSeparated f
  finitePresentation : LocallyOfFinitePresentation f
  baseLocallyNoetherian : IsLocallyNoetherian S

/-- A smooth quasi-projective relative curve, with the dimension convention made explicit. -/
structure Chapter14SmoothRelativeCurveData {C S : Scheme} (f : C ⟶ S) where
  smooth : Smooth f
  relativeDimensionOne : SmoothOfRelativeDimension 1 f
  quasiProjective : Chapter14QuasiProjectiveMorphismData f

/-- The relative functor convention used for Hilbert, symmetric-power, and divisor functors. -/
abbrev Chapter14RelativeFunctor (S : Scheme.{u}) :=
  (Over S)ᵒᵖ ⥤ Type u

/-- A functor of `S`-points together with its representing object. -/
def chapter14RepresentedBy {S : Scheme.{u}}
    (F : Chapter14RelativeFunctor S) (Y : Over S) : Prop :=
  Nonempty (F ≅ yoneda.obj Y)

/-- The ambient square and finiteness properties of a universal family. -/
structure Chapter14UniversalFamilyData {X S P Z : Scheme} (x : X ⟶ S) (p : P ⟶ S) where
  familyToParameter : Z ⟶ P
  familyToAmbient : Z ⟶ X
  squareCommutes : familyToAmbient ≫ x = familyToParameter ≫ p
  ambientPullback : Z ⟶ Limits.pullback x p
  ambientPullback_fst : ambientPullback ≫ Limits.pullback.fst x p = familyToAmbient
  ambientPullback_snd : ambientPullback ≫ Limits.pullback.snd x p = familyToParameter
  closedInAmbientPullback : IsClosedImmersion ambientPullback
  properOverParameter : IsProper familyToParameter
  flatOverParameter : Flat familyToParameter
  finitelyPresentedOverParameter : LocallyOfFinitePresentation familyToParameter

/-- A finite flat family with a specified fiber rank. -/
structure Chapter14FiniteFlatFamilyData {X S P Z : Scheme} (x : X ⟶ S) (p : P ⟶ S)
    extends Chapter14UniversalFamilyData (Z := Z) x p where
  finiteOverParameter : IsFinite familyToParameter
  rank : ℕ
  rank_eq : ∀ t : P, Scheme.Hom.finrank familyToParameter t = rank

/-! ## Positivity and base-change interfaces -/

/-- The relative family interface used by the positivity dictionary.

The operations below are defined from the Chapter 4 line-bundle and sheaf APIs.  In
particular, ampleness and very ampleness are relative to `family`; they are not
properties of a line bundle on `X` with the base silently forgotten.  The finiteness,
affineness, noetherianity, and projectivity fields are exactly the hypotheses of the
canonical Chapter 4 Serre and tensor-power bridges. -/
structure Chapter14PositivityOperations (X : Scheme) where
  base : Scheme
  family : X ⟶ base
  familyQuasiCompact : QuasiCompact family
  familyQuasiSeparated : QuasiSeparated family
  familyFinitePresentation : LocallyOfFinitePresentation family
  familyLocallyOfFiniteType : LocallyOfFiniteType family
  familySeparated : IsSeparated family
  projective : chapter04Projective family
  baseAffine : IsAffine base
  baseNoetherian : IsNoetherian base
  familyNoetherian : IsNoetherian X
  baseLocallyNoetherian : IsLocallyNoetherian base
  baseQuasiCompact : QuasiCompact (𝟙 base)

namespace Chapter14PositivityOperations

noncomputable def tensorPower {X : Scheme} (_O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) (n : ℕ) : Chapter14LineBundle X :=
  chapter04LineBundleTensorPower L n

def twist {X : Scheme} (_O : Chapter14PositivityOperations X)
    (F : X.Modules) (L : Chapter14LineBundle X) (n : ℕ) : X.Modules :=
  chapter04TwistedModule F L n

def globallyGenerated {X : Scheme} (O : Chapter14PositivityOperations X)
    (F : X.Modules) (L : Chapter14LineBundle X) (n : ℕ) : Prop :=
  chapter04TwistGeneratedByRelativeGlobalSections O.family F L n

def higherCohomologyVanishes {X : Scheme} (_O : Chapter14PositivityOperations X)
    (F : X.Modules) (L : Chapter14LineBundle X) (n i : ℕ) : Prop :=
  chapter04CohomologyVanishes (chapter04TwistedModule F L n) i

def veryAmple {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) : Prop :=
  chapter04VeryAmple O.family L

def ample {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) : Prop :=
  chapter04Ample O.family L

def affineNonvanishing {X : Scheme} (O : Chapter14PositivityOperations X)
    (L : Chapter14LineBundle X) : Prop :=
  Nonempty (Chapter04AmpleWitness O.family L)

end Chapter14PositivityOperations

/-- The two canonical kinds of parameter object occurring in the synthesis. -/
inductive Chapter14ParameterKind
  | orderedTuple
  | permutationQuotient
  | finiteLocallyFreeSubscheme
  | fixedHilbertPolynomial
  | effectiveCartierDivisor

/-- A source-facing parameter object records its kind and its universal family separately. -/
structure Chapter14ParameterObject (S : Scheme) where
  parameter : Scheme
  toBase : parameter ⟶ S
  kind : Chapter14ParameterKind
  /-- Only parameter spaces carrying a universal family supply this optional datum. -/
  universalFamily : Option (Σ Z : Scheme, Z ⟶ parameter)

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
