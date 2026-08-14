import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.Dimension.Finite
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 11.

The preceding books provide the canonical scheme, invertible-module, and
relative-curve interfaces.  The pinned sheaf-cohomology API does not yet
package finite-dimensional field-valued cohomology spaces, divisors, or
dualizing sheaves in the form used by this chapter.  The records below keep
those missing interfaces explicit and attach every book-facing object to a
canonical scheme or sheaf object.
-/

/-! ### Curves and line bundles -/

/-- A smooth proper geometrically connected curve over a field, with its genus.

The `integral` field is the geometric fact used by the negative-degree
vanishing statement.  It is separated from the scheme morphism properties so
that the same vanishing interface can later be reused for an independently
constructed integral curve. -/
structure Chapter11CurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  smooth : Smooth structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  curve : Chapter09RelativeCurve structureMap
  integral : Prop
  genus : ℕ

/-- The predicate used when a theorem only needs integrality of a curve. -/
def Chapter11IntegralCurve {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) : Prop :=
  C.integral

/-- A proper geometrically connected pure one-dimensional Gorenstein curve.

Unlike `Chapter11CurveOverField`, this record does not assume smoothness: it
is the boundary needed for the Gorenstein form of Riemann--Roch. -/
structure Chapter11ProperGorensteinCurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  curve : Chapter09RelativeCurve structureMap
  pureDimensionOne : Prop
  gorenstein : Prop
  arithmeticGenus : ℕ

/-- A reduced connected curve, used for the componentwise vanishing warning;
the criterion does not require properness or Gorenstein hypotheses. -/
structure Chapter11ReducedConnectedCurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  connected : Prop
  reduced : Prop
  curve : Chapter09RelativeCurve structureMap

/-- The earlier Book 8 line-bundle record, exposed under the Book 9 name. -/
abbrev Chapter11LineBundle (X : Scheme.{u}) := Chapter09LineBundle X

/-- Isomorphisms of Chapter 11 line bundles are sheaf isomorphisms. -/
abbrev Chapter11LineBundleIso {X : Scheme.{u}}
    (L M : Chapter11LineBundle X) := Chapter09LineBundleIso L M

/-- The canonical structure-sheaf line bundle. -/
noncomputable def chapter11StructureSheafLineBundle (X : Scheme.{u}) :
    Chapter11LineBundle X :=
  chapter09StructureSheafLineBundle X

/-- The line-bundle equivalence relation used by triviality and divisor
constructions. -/
def chapter11LineBundleIsomorphic {X : Scheme.{u}}
    (L M : Chapter11LineBundle X) : Prop :=
  Nonempty (Chapter11LineBundleIso L M)

theorem chapter11_lineBundleIsomorphic_refl {X : Scheme.{u}}
    (L : Chapter11LineBundle X) :
    chapter11LineBundleIsomorphic L L := by
  exact ⟨⟨Iso.refl L.module⟩⟩

theorem chapter11_lineBundleIsomorphic_symm {X : Scheme.{u}}
    {L M : Chapter11LineBundle X}
    (h : chapter11LineBundleIsomorphic L M) :
    chapter11LineBundleIsomorphic M L := by
  rcases h with ⟨h⟩
  exact ⟨⟨h.hom.symm⟩⟩

/- LOCAL_DEPENDENCY_GUESS: the tensor and inverse line-bundle operations are
the missing Picard-level
bridge in the pinned snapshot.  The tensor field extends the canonical
Chapter 9 tensor theory; `dual` is the only genuinely new operation.
-/
class Chapter11PicardTheory (X : Scheme.{u})
    extends Chapter09LineBundleTensorTheory X where
  dual : Chapter11LineBundle X → Chapter11LineBundle X
  dual_tensor_iso : ∀ L,
    Chapter11LineBundleIso
      (tensor (dual L) L) (chapter11StructureSheafLineBundle X)

def chapter11Tensor {X : Scheme.{u}} [Chapter11PicardTheory X]
    (L M : Chapter11LineBundle X) : Chapter11LineBundle X :=
  Chapter09LineBundleTensorTheory.tensor L M

def chapter11Dual {X : Scheme.{u}} [Chapter11PicardTheory X]
    (L : Chapter11LineBundle X) : Chapter11LineBundle X :=
  Chapter11PicardTheory.dual L

def chapter11LineBundleTrivial {X : Scheme.{u}}
    (L : Chapter11LineBundle X) : Prop :=
  chapter11LineBundleIsomorphic L (chapter11StructureSheafLineBundle X)

@[ext] theorem chapter11_lineBundle_ext {X : Scheme.{u}}
    {L M : Chapter11LineBundle X} (h : L.module = M.module) : L = M := by
  cases L
  cases M
  cases h
  rfl

def chapter11LineBundleIsoRefl {X : Scheme.{u}}
    (L : Chapter11LineBundle X) : Chapter11LineBundleIso L L :=
  ⟨Iso.refl L.module⟩

def chapter11LineBundleIsoSymm {X : Scheme.{u}}
    {L M : Chapter11LineBundle X} (e : Chapter11LineBundleIso L M) :
    Chapter11LineBundleIso M L :=
  ⟨e.hom.symm⟩

def chapter11LineBundleIsoTrans {X : Scheme.{u}}
    {L M N : Chapter11LineBundle X}
    (e₁ : Chapter11LineBundleIso L M)
    (e₂ : Chapter11LineBundleIso M N) : Chapter11LineBundleIso L N :=
  ⟨e₁.hom.trans e₂.hom⟩

theorem chapter11_lineBundle_isomorphic_trans {X : Scheme.{u}}
    {L M N : Chapter11LineBundle X}
    (hLM : chapter11LineBundleIsomorphic L M)
    (hMN : chapter11LineBundleIsomorphic M N) :
    chapter11LineBundleIsomorphic L N := by
  rcases hLM with ⟨e₁⟩
  rcases hMN with ⟨e₂⟩
  exact ⟨chapter11LineBundleIsoTrans e₁ e₂⟩

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf-cohomology API does not expose
finite-dimensional field-valued cohomology spaces with the module instances
needed by the numerical statements below. -/
/-! ### Cohomology over a field -/

/-- A finite-dimensional, field-valued model of sheaf cohomology on `X`.

`H` is indexed by the canonical module sheaf and degree.  The explicit
instances make `Module.finrank` and linear evaluation maps available without
identifying the underlying additive-category object by hand. -/
class Chapter11CohomologyTheory {k : Type u} [Field k]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) where
  H : X.Modules → ℕ → Type u
  addCommGroup : ∀ (F : X.Modules) (i : ℕ), AddCommGroup (H F i)
  module : ∀ (F : X.Modules) (i : ℕ), Module k (H F i)
  finite : ∀ (F : X.Modules) (i : ℕ),
    letI : Module k (H F i) := module F i
    Module.Finite k (H F i)

instance chapter11CohomologyTheory.addCommGroup
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter11CohomologyTheory X f] (F : X.Modules) (i : ℕ) :
    AddCommGroup (T.H F i) :=
  T.addCommGroup F i

instance chapter11CohomologyTheory.module
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter11CohomologyTheory X f] (F : X.Modules) (i : ℕ) :
    Module k (T.H F i) :=
  T.module F i

abbrev Chapter11CohomologySpace {k : Type u} [Field k]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [Chapter11CohomologyTheory X f] (F : X.Modules) (i : ℕ) :=
  Chapter11CohomologyTheory.H F i

abbrev Chapter11H0 {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) :=
  Chapter11CohomologySpace C.carrier C.structureMap L.module 0

abbrev Chapter11H1 {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) :=
  Chapter11CohomologySpace C.carrier C.structureMap L.module 1

noncomputable def chapter11CohomologyFinrank
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter11CohomologyTheory X f]
    (F : X.Modules) (i : ℕ) : ℕ :=
  Module.finrank k (T.H F i)

noncomputable def chapter11EulerCharacteristic
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of k)}
    [T : Chapter11CohomologyTheory X f]
  (F : X.Modules) : ℤ :=
  (chapter11CohomologyFinrank (f := f) F 0 : ℤ) -
    (chapter11CohomologyFinrank (f := f) F 1 : ℤ)

noncomputable def chapter11H0Finrank
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℕ :=
  chapter11CohomologyFinrank (f := C.structureMap) L.module 0

noncomputable def chapter11H1Finrank
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℕ :=
  chapter11CohomologyFinrank (f := C.structureMap) L.module 1

noncomputable def chapter11EulerCharacteristicOfLineBundle
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℤ :=
  chapter11EulerCharacteristic (f := C.structureMap) L.module

/- LOCAL_DEPENDENCY_GUESS: degree, Picard dualization, and a chosen dualizing
line bundle are kept as thin book-facing interfaces until the preceding
divisor/dualizing chapters expose their canonical constructions. -/
/-! ### Degree and canonical data -/

/-- Degree of a line bundle, with the Picard compatibilities used below. -/
class Chapter11DegreeTheory (X : Scheme.{u})
    [Chapter11PicardTheory X] where
  degree : Chapter11LineBundle X → ℤ
  degree_structureSheaf :
    degree (chapter11StructureSheafLineBundle X) = 0
  degree_tensor : ∀ L M,
    degree (chapter11Tensor L M) = degree L + degree M
  degree_dual : ∀ L,
    degree (chapter11Dual L) = -degree L
  degree_iso : ∀ {L M},
    chapter11LineBundleIsomorphic L M → degree L = degree M

def chapter11Degree {X : Scheme.{u}}
    [Chapter11PicardTheory X] [Chapter11DegreeTheory X]
    (L : Chapter11LineBundle X) : ℤ :=
  Chapter11DegreeTheory.degree L

theorem chapter11_degree_eq_of_isomorphic {X : Scheme.{u}}
    [Chapter11PicardTheory X] [Chapter11DegreeTheory X]
    {L M : Chapter11LineBundle X}
    (hLM : chapter11LineBundleIsomorphic L M) :
    chapter11Degree L = chapter11Degree M := by
  exact Chapter11DegreeTheory.degree_iso hLM

/- A chosen dualizing line bundle.  Smooth curves and Gorenstein curves both
use this interface; the actual sheaf construction belongs to the earlier
dualizing-sheaf chapter and is not duplicated here. -/
class Chapter11DualizingSheafTheory (X : Scheme.{u}) where
  dualizing : Chapter11LineBundle X
  isDualizing : Prop

def chapter11CanonicalBundle {X : Scheme.{u}}
    [Chapter11DualizingSheafTheory X] : Chapter11LineBundle X :=
  Chapter11DualizingSheafTheory.dualizing

/-- A divisor with its degree and associated line bundle. -/
structure Chapter11Divisor (X : Scheme.{u})
    [Chapter11PicardTheory X] [Chapter11DegreeTheory X] where
  degree : ℤ
  lineBundle : Chapter11LineBundle X
  degree_eq_lineBundle : degree = chapter11Degree lineBundle

@[ext] theorem chapter11_divisor_ext {X : Scheme.{u}}
    [Chapter11PicardTheory X] [Chapter11DegreeTheory X]
    {D E : Chapter11Divisor X}
    (hdegree : D.degree = E.degree)
    (hlineBundle : D.lineBundle = E.lineBundle) : D = E := by
  cases D
  cases E
  cases hdegree
  cases hlineBundle
  rfl

def chapter11DivisorSub {X : Scheme.{u}}
    [Chapter11PicardTheory X] [Chapter11DegreeTheory X]
    (D E : Chapter11Divisor X) : Chapter11Divisor X where
  degree := D.degree - E.degree
  lineBundle := chapter11Tensor D.lineBundle (chapter11Dual E.lineBundle)
  degree_eq_lineBundle := by
    sorry

notation D " -ᵈ " E => chapter11DivisorSub D E

/-- A canonical divisor is a divisor whose line bundle is the dualizing one. -/
structure Chapter11CanonicalDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier] where
  divisor : Chapter11Divisor C.carrier
  associated : Chapter11LineBundleIso divisor.lineBundle
    (chapter11CanonicalBundle (X := C.carrier))

/-- An effective divisor with its canonical line-bundle representative and
finite length. -/
structure Chapter11EffectiveDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) where
  support : Type u
  [support_finite : Fintype support]
  point : support → C.carrier
  point_closed : ∀ x, IsClosed ({point x} : Set C.carrier)
  multiplicity : support → ℕ
  residueDegree : support → ℕ
  residueDegree_is_field_extension_degree : Prop
  degree : ℕ
  degree_eq_sum : degree = ∑ x, multiplicity x * residueDegree x
  lineBundle : Chapter11LineBundle C.carrier
  length : ℕ
  length_eq_degree : length = degree

/-! ### Cartier sequences and zero-dimensional quotients -/

/-- The sheaf sequence attached to an effective divisor.

The quotient is the pushforward of `𝒪_D(D)` to `X`; the two explicit
properties record exactly the invertibility and length assertions used in the
point-adding proof. -/
structure Chapter11CartierSequenceData {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) (D : Chapter11EffectiveDivisor C)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  quotient : C.carrier.Modules
  inclusion : (chapter11StructureSheafLineBundle C.carrier).module ⟶ D.lineBundle.module
  quotientMap : D.lineBundle.module ⟶ quotient
  inclusion_mono : Mono inclusion
  quotient_epi : Epi quotientMap
  comp_zero : inclusion ≫ quotientMap = 0
  exact : (ShortComplex.mk inclusion quotientMap comp_zero).Exact
  quotient_invertible_on_divisor : Prop
  quotient_length : ℕ
  quotient_length_eq_degree : quotient_length = D.degree
  quotient_dimension : ℕ
  quotient_dimension_eq_length : quotient_dimension = quotient_length
  quotient_dimension_eq_h0_finrank :
    quotient_dimension = chapter11CohomologyFinrank (f := C.structureMap) quotient 0

/-- An effective Cartier divisor is an effective divisor together with its
Cartier exact sequence. -/
structure Chapter11EffectiveCartierDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  divisor : Chapter11EffectiveDivisor C
  cartier : Chapter11CartierSequenceData C divisor

abbrev Chapter11CartierQuotient {k : Type u} [Field k]
    {C : Chapter11CurveOverField k}
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (D : Chapter11EffectiveCartierDivisor C) : C.carrier.Modules :=
  D.cartier.quotient

theorem chapter11_cartier_sequence_exact
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (D : Chapter11EffectiveCartierDivisor C) :
    (ShortComplex.mk D.cartier.inclusion D.cartier.quotientMap
      D.cartier.comp_zero).Exact :=
  D.cartier.exact

/-! ### Evaluation, twists, and length-two restrictions -/

/-- A closed geometric point used in generation and separation statements. -/
structure Chapter11GeometricPoint {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) where
  underlying : C.carrier
  closed : IsClosed ({underlying} : Set C.carrier)
  geometric : Prop

class Chapter11FiberTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  fiber : Chapter11LineBundle C.carrier → Chapter11GeometricPoint C → Type u
  addCommGroup : ∀ L p, AddCommGroup (fiber L p)
  module : ∀ L p, Module k (fiber L p)
  evaluation : ∀ L p,
    letI : AddCommGroup (fiber L p) := addCommGroup L p
    letI : Module k (fiber L p) := module L p
    Chapter11H0 C L →ₗ[k] fiber L p

instance chapter11FiberTheory.addCommGroup
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [T : Chapter11FiberTheory C] (L : Chapter11LineBundle C.carrier)
    (p : Chapter11GeometricPoint C) : AddCommGroup (T.fiber L p) :=
  T.addCommGroup L p

instance chapter11FiberTheory.module
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [T : Chapter11FiberTheory C] (L : Chapter11LineBundle C.carrier)
    (p : Chapter11GeometricPoint C) : Module k (T.fiber L p) :=
  T.module L p

def chapter11EvaluationMap {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C] (L : Chapter11LineBundle C.carrier)
    (p : Chapter11GeometricPoint C) :
    Chapter11H0 C L →ₗ[k] (Chapter11FiberTheory.fiber L p) :=
  Chapter11FiberTheory.evaluation L p

def chapter11GloballyGenerated {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C] (L : Chapter11LineBundle C.carrier) : Prop :=
  ∀ p : Chapter11GeometricPoint C,
    Function.Surjective (chapter11EvaluationMap C L p)

/-- A finite-length-two subscheme, with its canonical quotient sheaf exposed.
The quotient is kept as a module on `C`; this is the target of restriction of
global sections. -/
structure Chapter11LengthTwoSubscheme {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) where
  support : Scheme.{u}
  inclusion : support ⟶ C.carrier
  closed : IsClosedImmersion inclusion
  quotient : C.carrier.Modules
  finiteLength : ℕ
  finiteLength_eq_two : finiteLength = 2
  quotient_is_structure_sheaf_pushforward : Prop

class Chapter11LengthTwoRestrictionTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  restriction : ∀ (L : Chapter11LineBundle C.carrier)
    (Z : Chapter11LengthTwoSubscheme C),
    Chapter11H0 C L →ₗ[k]
      Chapter11CohomologySpace C.carrier C.structureMap Z.quotient 0

def chapter11RestrictionMap {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11LengthTwoRestrictionTheory C]
    (L : Chapter11LineBundle C.carrier)
    (Z : Chapter11LengthTwoSubscheme C) :
    Chapter11H0 C L →ₗ[k]
      Chapter11CohomologySpace C.carrier C.structureMap Z.quotient 0 :=
  Chapter11LengthTwoRestrictionTheory.restriction L Z

def chapter11SeparatesLengthTwo {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11LengthTwoRestrictionTheory C]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  ∀ Z : Chapter11LengthTwoSubscheme C,
    Function.Surjective (chapter11RestrictionMap C L Z)

def chapter11VeryAmpleByLengthTwoCriterion {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C]
    [Chapter11LengthTwoRestrictionTheory C]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  chapter11GloballyGenerated C L ∧ chapter11SeparatesLengthTwo C L

class Chapter11PointTwistTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  twistAt : Chapter11LineBundle C.carrier → Chapter11GeometricPoint C →
    Chapter11LineBundle C.carrier
  degree_twistAt : ∀ L p,
    chapter11Degree (twistAt L p) = chapter11Degree L - 1

def chapter11TwistAtPoint {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11PointTwistTheory C]
    (L : Chapter11LineBundle C.carrier) (p : Chapter11GeometricPoint C) :
    Chapter11LineBundle C.carrier :=
  Chapter11PointTwistTheory.twistAt L p

/-! ### Duality and connectedness bridges -/

/- LOCAL_DEPENDENCY_GUESS: Chapter 12 supplies this duality interface, but
Chapter 11 cannot import a later chapter.  The field is the canonical linear
equivalence between H¹ and the dual of H⁰ of the dual-twisted line bundle. -/
class Chapter11SerreDualityTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  h1_h0_dual_iso : ∀ L,
    Chapter11H1 C L ≃ₗ[k]
      (Chapter11H0 C
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)) →ₗ[k] k)

class Chapter11ConnectedGlobalSections {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  h0_structure_sheaf :
    chapter11H0Finrank C (chapter11StructureSheafLineBundle C.carrier) = 1

theorem chapter11_connected_global_sections_eq_one
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C] :
    chapter11H0Finrank C (chapter11StructureSheafLineBundle C.carrier) = 1 :=
  Chapter11ConnectedGlobalSections.h0_structure_sheaf

/-! ### Section-zero and reducible-curve interfaces -/

structure Chapter11SectionZeroDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier]
    [Chapter11DegreeTheory C.carrier]
    (L : Chapter11LineBundle C.carrier)
    (s : Chapter11H0 C L) where
  divisor : Chapter11EffectiveDivisor C
  degree_eq : (divisor.degree : ℤ) = chapter11Degree L
  section_nonzero : s ≠ 0

/-- The formal warning that total degree is not a vanishing criterion on a
reducible curve.  The support condition is deliberately retained instead of
being replaced by a bare existential counterexample. -/
structure Chapter11ReducibleNegativeDegreeSection {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  reducible : Prop
  reduced : Prop
  lineBundle : Chapter11LineBundle C.carrier
  section : Chapter11CohomologySpace C.carrier C.structureMap lineBundle.module 0
  totalDegree_negative : chapter11Degree lineBundle < 0
  section_nonzero : section ≠ 0
  components : Type u
  positiveComponent : components
  componentDegree : components → ℤ
  positive_component_degree : 0 < componentDegree positiveComponent
  section_supported_on_positive_component : Prop

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
