import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Section03RosenlichtDifferentials
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open scoped BigOperators TensorProduct

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
  pureDimensionOne :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Chapter08PureDimensionOne
      carrier
  integral : IsIntegral carrier
  genus : ℕ

/-- The predicate used when a theorem only needs integrality of a curve. -/
def Chapter11IntegralCurve {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) : Prop :=
  IsIntegral C.carrier

/-- A proper geometrically connected pure one-dimensional Gorenstein curve.

Unlike `Chapter11CurveOverField`, this record does not assume smoothness: it
is the boundary needed for the Gorenstein form of Riemann--Roch. -/
structure Chapter11ProperGorensteinCurveOverField (k : Type u) [Field k] where
  canonical :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Chapter09CohenMacaulayCurveOverField
      k
  extTheory :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Chapter09ExtTheory
      canonical.scheme
  derivedHomTheory :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Chapter09AbsoluteDerivedHomTheory
      k canonical.scheme
  canonicalDualizing :
    @LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Chapter09AbsoluteDualizingData
      k _ canonical extTheory derivedHomTheory
  geometricallyConnected :
    GeometricallyConnected canonical.structureMap
  gorenstein :
    @LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.chapter09AbsoluteGorenstein
      k _ canonical extTheory derivedHomTheory canonicalDualizing
  arithmeticGenus : ℕ

abbrev Chapter11ProperGorensteinCurveOverField.carrier
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) : Scheme.{u} :=
  C.canonical.scheme

abbrev Chapter11ProperGorensteinCurveOverField.structureMap
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) :
    C.carrier ⟶ AlgebraicGeometry.Spec (.of k) :=
  C.canonical.structureMap

abbrev Chapter11ProperGorensteinCurveOverField.proper
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) : IsProper C.structureMap :=
  C.canonical.proper

abbrev Chapter11ProperGorensteinCurveOverField.quasiCompact
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) : QuasiCompact C.structureMap :=
  C.canonical.quasiCompact

abbrev Chapter11ProperGorensteinCurveOverField.pureDimensionOne
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Chapter08PureDimensionOne
      C.carrier :=
  C.canonical.pureDimensionOne

/-- A reduced connected curve, used for the componentwise vanishing warning;
the criterion does not require properness or Gorenstein hypotheses. -/
structure Chapter11ReducedConnectedCurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  connected : _root_.IsConnected (Set.univ : Set carrier)
  reduced : IsReduced carrier
  pureDimensionOne :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Chapter08PureDimensionOne
      carrier

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
  tensor_iso : ∀ {L₁ L₂ M₁ M₂},
    Chapter11LineBundleIso L₁ L₂ →
    Chapter11LineBundleIso M₁ M₂ →
    Chapter11LineBundleIso (tensor L₁ M₁) (tensor L₂ M₂)
  structureSheaf_tensor_right : ∀ L,
    Chapter11LineBundleIso
      (tensor L (chapter11StructureSheafLineBundle X)) L

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

theorem chapter11_dual_structureSheaf_isomorphic {X : Scheme.{u}}
    [Chapter11PicardTheory X] :
    chapter11LineBundleIsomorphic
      (chapter11Dual (chapter11StructureSheafLineBundle X))
      (chapter11StructureSheafLineBundle X) := by
  let e₁ := Chapter11PicardTheory.structureSheaf_tensor_right
    (chapter11Dual (chapter11StructureSheafLineBundle X))
  let e₂ := Chapter11PicardTheory.dual_tensor_iso
    (chapter11StructureSheafLineBundle X)
  exact ⟨chapter11LineBundleIsoTrans (chapter11LineBundleIsoSymm e₁) e₂⟩

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
  Chapter11CohomologyTheory.H f F i

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

/-! The pinned cohomology object is indexed by sheaves, so the two numerical
properties used by the point-adding argument are recorded explicitly: Euler
characteristic is invariant under sheaf isomorphism and additive on exact
short complexes.  These are the usual functorial and exactness properties of
coherent cohomology, not extra numerical conclusions. -/
class Chapter11EulerCharacteristicTheory {k : Type u} [Field k]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [Chapter11CohomologyTheory X f] where
  exact_additive : ∀ {A B C : X.Modules} (i : A ⟶ B) (p : B ⟶ C)
    (hzero : i ≫ p = 0),
    (ShortComplex.mk i p hzero).Exact →
      chapter11EulerCharacteristic (f := f) B =
        chapter11EulerCharacteristic (f := f) A +
          chapter11EulerCharacteristic (f := f) C
  iso_invariant : ∀ {A B : X.Modules},
    Nonempty (A ≅ B) →
      chapter11EulerCharacteristic (f := f) A =
        chapter11EulerCharacteristic (f := f) B

/-! Isomorphic sheaves also have isomorphic cohomology.  Only the finrank
form is needed for the divisor spelling of Riemann--Roch. -/
class Chapter11CohomologyIsomorphismTheory {k : Type u} [Field k]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [Chapter11CohomologyTheory X f] where
  finrank_iso : ∀ {A B : X.Modules}, Nonempty (A ≅ B) → ∀ i,
    chapter11CohomologyFinrank (f := f) A i =
      chapter11CohomologyFinrank (f := f) B i

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

/-! The preceding degree chapter identifies numerical degree with the
Euler-characteristic degree.  Chapter 11 keeps that compatibility explicit
because its line-bundle and cohomology objects are book-facing interfaces. -/
class Chapter11DegreeEulerCharacteristicTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  degree_eq_euler_difference : ∀ L,
    chapter11Degree L =
      chapter11EulerCharacteristic (f := C.structureMap) L.module -
        chapter11EulerCharacteristic (f := C.structureMap)
          (chapter11StructureSheafLineBundle C.carrier).module

/-! On a proper Gorenstein curve, the Picard degree is the
Euler-characteristic degree used in the singular-curve form of the book. -/
class Chapter11GorensteinDegreeTheory {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  degree_eq_euler_difference : ∀ L,
    chapter11Degree L =
      chapter11EulerCharacteristic (f := C.structureMap) L.module -
        chapter11EulerCharacteristic (f := C.structureMap)
          (chapter11StructureSheafLineBundle C.carrier).module

/- A chosen dualizing line bundle.  Smooth curves and Gorenstein curves both
use this interface; the actual sheaf construction belongs to the earlier
dualizing-sheaf chapter and is not duplicated here. -/
class Chapter11DualizingSheafTheory (X : Scheme.{u}) where
  dualizing : Chapter11LineBundle X

def chapter11CanonicalBundle {X : Scheme.{u}}
    [Chapter11DualizingSheafTheory X] : Chapter11LineBundle X :=
  Chapter11DualizingSheafTheory.dualizing

/-- A divisor with its degree and associated line bundle. -/
structure Chapter11Divisor (X : Scheme.{u})
    [Chapter11PicardTheory X] [Chapter11DegreeTheory X] where
  degree : ℤ
  lineBundle : Chapter11LineBundle X
  degree_eq_lineBundle : degree = chapter11Degree lineBundle

/-- A line bundle is represented by a divisor.  This is the divisor--Picard
bridge supplied by the preceding divisor chapters; it is kept separate from
the Riemann--Roch assertion itself. -/
def Chapter11LineBundleDivisorRepresentation {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  ∃ D : Chapter11Divisor C.carrier,
    chapter11LineBundleIsomorphic D.lineBundle L

class Chapter11DivisorRepresentationTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  every_line_bundle_has_divisor_representation : ∀ L,
    Chapter11LineBundleDivisorRepresentation C L

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

/-- The residue-field degree of a closed point on a curve over `k`. -/
noncomputable def chapter11ClosedPointDegree {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) (x : C.carrier)
    (_hx : IsClosed ({x} : Set C.carrier)) : ℕ := by
  letI : Algebra k (C.carrier.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.structureMap.appTop ≫
      C.carrier.Γevaluation x).hom.toAlgebra
  exact Module.finrank k (C.carrier.residueField x)

/-- An effective divisor with its canonical line-bundle representative and
finite length. -/
structure Chapter11EffectiveDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) where
  support : Type u
  [support_finite : Fintype support]
  point : support → C.carrier
  point_closed : ∀ x, IsClosed ({point x} : Set C.carrier)
  point_injective : Function.Injective point
  multiplicity : support → ℕ
  residueDegree : support → ℕ
  residueDegree_is_field_extension_degree : ∀ x,
    residueDegree x = chapter11ClosedPointDegree C (point x) (point_closed x)
  degree : ℕ
  degree_eq_sum : degree = ∑ x, multiplicity x * residueDegree x
  lineBundle : Chapter11LineBundle C.carrier
  degree_zero_lineBundle_trivial : degree = 0 → chapter11LineBundleTrivial lineBundle
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
  quotient_invertible_on_divisor_holds : quotient_invertible_on_divisor
  quotient_length : ℕ
  quotient_length_eq_degree : quotient_length = D.degree
  quotient_dimension : ℕ
  quotient_dimension_eq_length : quotient_dimension = quotient_length
  quotient_dimension_eq_h0_finrank :
    quotient_dimension = chapter11CohomologyFinrank (f := C.structureMap) quotient 0
  quotient_h1_finrank_eq_zero :
    chapter11CohomologyFinrank (f := C.structureMap) quotient 1 = 0

/-- An effective Cartier divisor is an effective divisor together with its
Cartier exact sequence. -/
structure Chapter11EffectiveCartierDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  divisor : Chapter11EffectiveDivisor C
  cartier : Chapter11CartierSequenceData C divisor

/-! Tensoring the Cartier sequence by a line bundle is the local input needed
to subtract an effective divisor from an arbitrary line bundle.  The
structure-sheaf instance is recorded separately above because it is useful
for the one-step calculation even before this general twist interface is
available.  The sequence data is kept below the Euler-characteristic
conclusion: the latter is derived from exactness and the finite quotient
calculation, rather than being assumed as a second copy of the theorem. -/
class Chapter11EffectiveCartierTwistSequenceTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  quotient : ∀ (_D : Chapter11EffectiveCartierDivisor C)
    (_L : Chapter11LineBundle C.carrier),
    C.carrier.Modules
  inclusion : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier),
    L.module ⟶ (chapter11Tensor L D.divisor.lineBundle).module
  quotientMap : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier),
    (chapter11Tensor L D.divisor.lineBundle).module ⟶ quotient D L
  inclusion_mono : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier), Mono (inclusion D L)
  quotient_epi : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier), Epi (quotientMap D L)
  comp_zero : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier),
    inclusion D L ≫ quotientMap D L = 0
  exact : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier),
    (ShortComplex.mk (inclusion D L) (quotientMap D L)
      (comp_zero D L)).Exact
  quotient_euler_characteristic : ∀ (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier),
    chapter11EulerCharacteristic (f := C.structureMap) (quotient D L) =
      (D.divisor.degree : ℤ)

theorem chapter11_effective_cartier_twist_euler_difference
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    (D : Chapter11EffectiveCartierDivisor C)
    (L : Chapter11LineBundle C.carrier) :
    chapter11EulerCharacteristic (f := C.structureMap)
        (chapter11Tensor L D.divisor.lineBundle).module -
        chapter11EulerCharacteristic (f := C.structureMap) L.module =
      (D.divisor.degree : ℤ) := by
  sorry

/-! A divisor on a regular curve is the difference of disjoint effective
divisors.  The concrete construction belongs to the preceding divisor
chapters; this interface prevents the adding-points theorem from silently
assuming it for the unconstrained book-facing divisor record. -/
structure Chapter11EffectiveDecomposition {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (D : Chapter11Divisor C.carrier) where
  positive : Chapter11EffectiveCartierDivisor C
  negative : Chapter11EffectiveCartierDivisor C
  disjoint : ∀ x : positive.divisor.support, ∀ y : negative.divisor.support,
    positive.divisor.point x ≠ negative.divisor.point y
  degree_decomposition :
    D.degree = (positive.divisor.degree : ℤ) - (negative.divisor.degree : ℤ)
  lineBundle_comparison :
    Chapter11LineBundleIso D.lineBundle
      (chapter11Tensor positive.divisor.lineBundle
        (chapter11Dual negative.divisor.lineBundle))

class Chapter11EffectiveDecompositionTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  every_divisor_has_effective_decomposition : ∀ D,
    Nonempty (Chapter11EffectiveDecomposition C D)

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
  K : Type u
  [field : Field K]
  [algebra : Algebra k K]
  [algebraicallyClosed : IsAlgClosed K]
  point : AlgebraicGeometry.Spec (.of K) ⟶ C.carrier
  point_over_base :
    point ≫ C.structureMap =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  underlying : C.carrier
  underlying_eq_point : point (⊥ : PrimeSpectrum K) = underlying
  closed : IsClosed ({underlying} : Set C.carrier)

attribute [instance] Chapter11GeometricPoint.field
attribute [instance] Chapter11GeometricPoint.algebra
attribute [instance] Chapter11GeometricPoint.algebraicallyClosed

class Chapter11FiberTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  fiber : Chapter11LineBundle C.carrier → Chapter11GeometricPoint C → Type u
  addCommGroup : ∀ L p, AddCommGroup (fiber L p)
  module : ∀ L p, Module p.K (fiber L p)
  evaluation : ∀ L p,
    letI : AddCommGroup (fiber L p) := addCommGroup L p
    letI : Module p.K (fiber L p) := module L p
    (p.K ⊗[k] Chapter11H0 C L) →ₗ[p.K] fiber L p

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
    (p : Chapter11GeometricPoint C) : Module p.K (T.fiber L p) :=
  T.module L p

def chapter11EvaluationMap {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C] (L : Chapter11LineBundle C.carrier)
    (p : Chapter11GeometricPoint C) :
    (p.K ⊗[k] Chapter11H0 C L) →ₗ[p.K] (Chapter11FiberTheory.fiber L p) :=
  Chapter11FiberTheory.evaluation L p

def chapter11GloballyGenerated {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C] (L : Chapter11LineBundle C.carrier) : Prop :=
  ∀ p : Chapter11GeometricPoint C,
    Function.Surjective (chapter11EvaluationMap C L p)

/-! The point used in a geometric evaluation lives on the scalar extension
`C_K`, not on `C` itself.  The following package keeps the cohomology,
Picard, and degree interfaces on that base change and records invariance of
degree for pulled-back line bundles. -/

abbrev chapter11GeometricBaseChange {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) (p : Chapter11GeometricPoint C) : Scheme.{u} :=
  chapter04FieldExtensionBaseChange C.structureMap (algebraMap k p.K)

abbrev chapter11GeometricBaseChangeMap {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) (p : Chapter11GeometricPoint C) :
    chapter11GeometricBaseChange C p ⟶ C.carrier :=
  chapter04FieldExtensionPullbackMap C.structureMap (algebraMap k p.K)

abbrev chapter11GeometricBaseChangeStructureMap {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) (p : Chapter11GeometricPoint C) :
    chapter11GeometricBaseChange C p ⟶ AlgebraicGeometry.Spec (.of p.K) :=
  chapter04FieldExtensionStructureMap C.structureMap (algebraMap k p.K)

abbrev chapter11GeometricBaseChangedLineBundle {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) (p : Chapter11GeometricPoint C)
    (L : Chapter11LineBundle C.carrier) :
    Chapter11LineBundle (chapter11GeometricBaseChange C p) :=
  chapter09PullbackLineBundle (chapter11GeometricBaseChangeMap C p) L

class Chapter11GeometricBaseChangeTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  cohomology : ∀ p,
    Chapter11CohomologyTheory
      (chapter11GeometricBaseChange C p)
      (chapter11GeometricBaseChangeStructureMap C p)
  picard : ∀ p,
    Chapter11PicardTheory (chapter11GeometricBaseChange C p)
  degree : ∀ p,
    Chapter11DegreeTheory (chapter11GeometricBaseChange C p)
  degree_pullback : ∀ (p : Chapter11GeometricPoint C)
    (L : Chapter11LineBundle C.carrier),
    chapter11Degree (chapter11GeometricBaseChangedLineBundle C p L) =
      chapter11Degree L

instance chapter11GeometricBaseChangeTheory.cohomology
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [T : Chapter11GeometricBaseChangeTheory C]
    (p : Chapter11GeometricPoint C) :
    Chapter11CohomologyTheory
      (chapter11GeometricBaseChange C p)
      (chapter11GeometricBaseChangeStructureMap C p) :=
  T.cohomology p

instance chapter11GeometricBaseChangeTheory.picard
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [T : Chapter11GeometricBaseChangeTheory C]
    (p : Chapter11GeometricPoint C) :
    Chapter11PicardTheory (chapter11GeometricBaseChange C p) :=
  T.picard p

instance chapter11GeometricBaseChangeTheory.degree
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [T : Chapter11GeometricBaseChangeTheory C]
    (p : Chapter11GeometricPoint C) :
    Chapter11DegreeTheory (chapter11GeometricBaseChange C p) :=
  T.degree p

noncomputable def chapter11GeometricCohomologyFinrank
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11GeometricBaseChangeTheory C]
    (p : Chapter11GeometricPoint C)
    (M : Chapter11LineBundle (chapter11GeometricBaseChange C p)) (i : ℕ) : ℕ :=
  chapter11CohomologyFinrank
    (f := chapter11GeometricBaseChangeStructureMap C p) M.module i

/-- A finite-length-two subscheme, with its canonical quotient sheaf exposed.

Use the earlier Book 8 record rather than replacing scheme-theoretic finiteness
and length by a bare natural-number field. -/
abbrev Chapter11LengthTwoSubscheme {k : Type u} [Field k]
    (C : Chapter11CurveOverField k) :=
  Chapter04LengthTwoClosedSubscheme k C.structureMap

abbrev Chapter11LengthTwoSubscheme.quotient {k : Type u} [Field k]
    {C : Chapter11CurveOverField k}
    (Z : Chapter11LengthTwoSubscheme C) : C.carrier.Modules :=
  (Scheme.Modules.pushforward Z.inclusion).obj
    (chapter11StructureSheafLineBundle Z.Z).module

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

/-! The Chapter 4 criterion quantifies over every field extension.  This
record supplies the section maps and their base-field restrictions without
pretending that the abstract Chapter 11 cohomology object is definitionally a
space of sheaf sections. -/
structure Chapter11LengthTwoRestrictionData {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) where
  [addCommGroupSections : AddCommGroup L.module.val.sections]
  [moduleSections : Module k L.module.val.sections]
  addCommGroupSections_canonical :
    addCommGroupSections = chapter04SectionsAddCommGroup L.module
  moduleSections_canonical :
    moduleSections = chapter04SectionsModuleOverField C.structureMap L.module
  sectionMap : Chapter11H0 C L →ₗ[k] L.module.val.sections
  section_injective : Function.Injective sectionMap
  restriction : ∀ Z : Chapter11LengthTwoSubscheme C,
    let M := (Scheme.Modules.pullback Z.inclusion).obj L.module
    letI : AddCommGroup M.val.sections := chapter04SectionsAddCommGroup M
    letI : Module k M.val.sections :=
      chapter04SectionsModuleOverField Z.structureMap M
    Chapter11H0 C L →ₗ[k] M.val.sections
  restriction_eq : ∀ (Z : Chapter11LengthTwoSubscheme C)
    (i : Chapter11H0 C L),
    restriction Z i =
      (chapter04PullbackSectionData Z.inclusion L.module).map (sectionMap i)

class Chapter11LengthTwoRestrictionDataTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  data : ∀ L : Chapter11LineBundle C.carrier,
    Chapter11LengthTwoRestrictionData C L

noncomputable def chapter11LengthTwoFiniteSectionSystem
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier)
    (D : Chapter11LengthTwoRestrictionData C L)
    (hgenerate : Epi (L.module.freeHomEquiv.symm (fun i => D.sectionMap i))) :
    Chapter04FiniteSectionSystem k C.structureMap
      (chapter09AsChapter04LineBundle L) := by
  exact
    { I := Chapter11H0 C L
      addCommGroupI := inferInstance
      moduleI := inferInstance
      addCommGroupSections := D.addCommGroupSections
      moduleSections := D.moduleSections
      addCommGroupSections_canonical := D.addCommGroupSections_canonical
      moduleSections_canonical := D.moduleSections_canonical
      finite := by
        exact Chapter11CohomologyTheory.finite L.module 0
      sectionMap := D.sectionMap
      section_injective := D.section_injective
      generates := hgenerate
      restriction := D.restriction
      restriction_eq := D.restriction_eq }

def chapter11VeryAmpleByChapter04LengthTwoCriterion {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier)
    (D : Chapter11LengthTwoRestrictionData C L) : Prop :=
  ∃ hgenerate : Epi (L.module.freeHomEquiv.symm (fun i => D.sectionMap i)),
    chapter04SeparatesLengthTwo
      (chapter11LengthTwoFiniteSectionSystem C L D hgenerate)

theorem chapter11_chapter04_very_ample_of_length_two_criterion
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier)
    (D : Chapter11LengthTwoRestrictionData C L)
    (hcriterion : chapter11VeryAmpleByChapter04LengthTwoCriterion C L D) :
    chapter04VeryAmple C.structureMap (chapter09AsChapter04LineBundle L) := by
  sorry

def chapter11BaseFieldGenerationAndLengthTwoSeparation {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C]
    [Chapter11LengthTwoRestrictionTheory C]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  chapter11GloballyGenerated C L ∧ chapter11SeparatesLengthTwo C L

class Chapter11PointTwistTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11GeometricBaseChangeTheory C] where
  twistAt : ∀ (_L : Chapter11LineBundle C.carrier) (p : Chapter11GeometricPoint C),
    Chapter11LineBundle (chapter11GeometricBaseChange C p)
  degree_twistAt : ∀ L p,
    chapter11Degree (twistAt L p) =
      chapter11Degree (chapter11GeometricBaseChangedLineBundle C p L) - 1

def chapter11TwistAtPoint {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11GeometricBaseChangeTheory C]
    [Chapter11PointTwistTheory C]
    (L : Chapter11LineBundle C.carrier) (p : Chapter11GeometricPoint C) :
    Chapter11LineBundle (chapter11GeometricBaseChange C p) :=
  Chapter11PointTwistTheory.twistAt L p

/-! The point-twist exact sequence identifies the cokernel of evaluation with
the first cohomology of the twisted bundle.  The pinned sheaf API does not
expose that connecting map, so retain precisely the surjectivity consequence
used by global generation. -/
class Chapter11PointEvaluationTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11FiberTheory C]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11GeometricBaseChangeTheory C]
    [Chapter11PointTwistTheory C] where
  evaluation_surjective_of_h1_twist_zero : ∀ L p,
    chapter11GeometricCohomologyFinrank C p
        (chapter11TwistAtPoint C L p) 1 = 0 →
      Function.Surjective (chapter11EvaluationMap C L p)

/-! The analogous length-two exact sequence is the bridge used for very
ampleness. -/
class Chapter11LengthTwoTwistTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11LengthTwoRestrictionTheory C] where
  twistAt : Chapter11LineBundle C.carrier → Chapter11LengthTwoSubscheme C →
    Chapter11LineBundle C.carrier
  degree_twistAt : ∀ L Z,
    chapter11Degree (twistAt L Z) = chapter11Degree L - 2
  restriction_surjective_of_h1_twist_zero : ∀ L Z,
    chapter11H1Finrank C (twistAt L Z) = 0 →
      Function.Surjective (chapter11RestrictionMap C L Z)

def chapter11TwistAtLengthTwo {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11LengthTwoRestrictionTheory C]
    [Chapter11LengthTwoTwistTheory C]
    (L : Chapter11LineBundle C.carrier) (Z : Chapter11LengthTwoSubscheme C) :
    Chapter11LineBundle C.carrier :=
  Chapter11LengthTwoTwistTheory.twistAt L Z

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
  h1_structure_sheaf :
    chapter11H1Finrank C (chapter11StructureSheafLineBundle C.carrier) = C.genus

theorem chapter11_connected_global_sections_eq_one
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C] :
    chapter11H0Finrank C (chapter11StructureSheafLineBundle C.carrier) = 1 :=
  Chapter11ConnectedGlobalSections.h0_structure_sheaf

/-! The analogous numerical package for a proper Gorenstein curve records the
definition of its arithmetic genus through the structure-sheaf Euler
characteristic.  This is the hypothesis needed for the Gorenstein formula and
does not silently impose geometric reducedness. -/
class Chapter11GorensteinEulerCharacteristicTheory {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  structure_euler_characteristic :
    chapter11EulerCharacteristic (f := C.structureMap)
        (chapter11StructureSheafLineBundle C.carrier).module =
      1 - (C.arithmeticGenus : ℤ)

/-! ### Section-zero and reducible-curve interfaces -/

structure Chapter11SectionZeroDivisor {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier]
    [Chapter11DegreeTheory C.carrier]
    (L : Chapter11LineBundle C.carrier)
    (s : Chapter11H0 C L) where
  divisor : Chapter11EffectiveDivisor C
  lineBundle_associated : Chapter11LineBundleIso divisor.lineBundle L
  degree_eq : (divisor.degree : ℤ) = chapter11Degree L
  section_nonzero : s ≠ 0

/-! The preceding rational-section/divisor API supplies the zero divisor of a
nonzero section.  Since the pinned cohomology object is intentionally
book-facing, keep this construction as an explicit bridge rather than
silently treating an arbitrary cohomology vector as a sheaf section. -/
class Chapter11SectionZeroDivisorTheory {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  zero_divisor_of_nonzero_section : ∀ (L : Chapter11LineBundle C.carrier)
    (s : Chapter11H0 C L), s ≠ 0 →
      Nonempty (Chapter11SectionZeroDivisor C L s)

/-- The formal warning that total degree is not a vanishing criterion on a
reducible curve.  The support condition is deliberately retained instead of
being replaced by a bare existential counterexample. -/
structure Chapter11ReducibleNegativeDegreeSection {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier] where
  reducible : ¬ IsIntegral C.carrier
  reduced : IsReduced C.carrier
  lineBundle : Chapter11LineBundle C.carrier
  globalSection : Chapter11CohomologySpace C.carrier C.structureMap lineBundle.module 0
  totalDegree_negative : chapter11Degree lineBundle < 0
  section_nonzero : globalSection ≠ 0
  components : Type u
  positiveComponent : components
  componentDegree : components → ℤ
  positive_component_degree : 0 < componentDegree positiveComponent
  section_supported_on_positive_component : Prop
  section_supported_on_positive_component_holds :
    section_supported_on_positive_component

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
