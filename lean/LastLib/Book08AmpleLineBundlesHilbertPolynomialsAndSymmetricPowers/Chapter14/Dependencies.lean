import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly

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

/-! ## Elementary reusable predicates -/

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
def chapter14ConstantHilbertPolynomial (d : ℕ) : Polynomial ℚ :=
  Polynomial.C (d : ℚ)

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
    (G : Chapter14GradedAlgebra A σ) (f : A) : Type _ :=
  HomogeneousLocalization.Away G.component f

/-- The standard open `D₊(f)` on the projective spectrum. -/
def chapter14StandardOpen {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A]
    (G : Chapter14GradedAlgebra A σ) (f : A) : (chapter14Proj G).Opens :=
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

/-- A line bundle is recorded as an invertible sheaf, not as its total space. -/
structure Chapter14LineBundle (X : Scheme) where
  sheaf : X.Modules
  isInvertible : Prop

/- A family of twisting sheaves indexed by the integral twist. -/
structure Chapter14TwistingSheafFamily (X : Scheme) where
  sheaf : ℤ → Chapter14LineBundle X

/-- A coherent coefficient sheaf together with the properties used in the Hilbert package. -/
structure Chapter14CoherentSheaf (X : Scheme) where
  sheaf : X.Modules
  isQuasiCoherent : Prop
  isFinitePresentation : Prop

/-- A projective witness over a fixed base morphism. -/
structure Chapter14ProjectiveMorphismData {X S : Scheme} (f : X ⟶ S) where
  ambient : Scheme
  ambientToBase : ambient ⟶ S
  embedding : X ⟶ ambient
  embedding_closed : IsClosedImmersion embedding
  overBase : embedding ≫ ambientToBase = f
  /- LOCAL_DEPENDENCY_GUESS: the preceding Book08 projective-bundle API supplies this
     predicate as `ambient = ProjectiveBundle(E)` for a finite locally free `E`. -/
  ambientIsProjectiveBundle : Prop

/-- The hypotheses used by the relative Hilbert and cohomology package. -/
structure Chapter14ProjectiveFlatFamilyData {X S : Scheme} (f : X ⟶ S)
    extends Chapter14ProjectiveMorphismData f where
  flat : Flat f
  finitePresentation : LocallyOfFinitePresentation f
  baseLocallyNoetherian : IsLocallyNoetherian S

/-- A smooth quasi-projective relative curve, with the dimension convention made explicit. -/
structure Chapter14SmoothRelativeCurveData {C S : Scheme} (f : C ⟶ S) where
  smooth : Smooth f
  relativeDimensionOne : SmoothOfRelativeDimension 1 f
  quasiProjective : Prop

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
  closedInAmbientPullback : Prop
  flatOverParameter : Flat familyToParameter
  finitelyPresentedOverParameter : LocallyOfFinitePresentation familyToParameter

/-- A finite flat family with a specified fiber rank. -/
structure Chapter14FiniteFlatFamilyData {X S P Z : Scheme} (x : X ⟶ S) (p : P ⟶ S)
    extends Chapter14UniversalFamilyData (Z := Z) x p where
  finiteOverParameter : IsFinite familyToParameter
  rank : ℕ

/-! ## Positivity and base-change interfaces -/

/-- Operations needed to state the asymptotic positivity dictionary. -/
structure Chapter14PositivityOperations (X : Scheme) where
  coefficientSheaf : Type*
  tensorPower : Chapter14LineBundle X → ℕ → Chapter14LineBundle X
  twist : coefficientSheaf → Chapter14LineBundle X → coefficientSheaf
  globallyGenerated : coefficientSheaf → Prop
  higherCohomologyVanishes : coefficientSheaf → ℕ → Prop
  veryAmple : Chapter14LineBundle X → Prop
  ample : Chapter14LineBundle X → Prop
  affineNonvanishing : Chapter14LineBundle X → Prop

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
  universalFamily : Option Scheme

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14
