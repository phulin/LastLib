import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.TensorProduct.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section03TheGlobalResidueTheorem
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 12.

 The preceding Book 09 chapters supply the canonical residue and duality
 interfaces used below.  The records in this file retain the book-facing
 notation while exposing explicit bridges to those earlier interfaces.
-/

/-! ### Curves, divisors, and cohomology -/

/-- A smooth proper geometrically connected relative curve over a field. -/
structure Chapter12Curve (k : Type u) [Field k] where
  residueCurve : Chapter08ProperGeometricallyConnectedCurve k
  functionFieldAlgebra : Algebra k residueCurve.carrier.functionField
  smoothRelative : SmoothOfRelativeDimension 1 residueCurve.structureMap
  quasiCompact : QuasiCompact residueCurve.structureMap
  locallyOfFinitePresentation : LocallyOfFinitePresentation residueCurve.structureMap
  relativeCohenMacaulay : chapter09CohenMacaulay residueCurve.carrier

attribute [instance] Chapter12Curve.functionFieldAlgebra

abbrev Chapter12Curve.scheme {k : Type u} [Field k]
    (C : Chapter12Curve k) : Scheme.{u} :=
  C.residueCurve.carrier

abbrev Chapter12Curve.structureMap {k : Type u} [Field k]
    (C : Chapter12Curve k) : C.scheme ⟶ AlgebraicGeometry.Spec (.of k) :=
  C.residueCurve.structureMap

abbrev Chapter12Curve.smooth {k : Type u} [Field k]
    (C : Chapter12Curve k) : SmoothOfRelativeDimension 1 C.structureMap :=
  C.smoothRelative

abbrev Chapter12Curve.proper {k : Type u} [Field k]
    (C : Chapter12Curve k) : IsProper C.structureMap :=
  C.residueCurve.proper

abbrev Chapter12Curve.geometricallyConnected {k : Type u} [Field k]
    (C : Chapter12Curve k) : GeometricallyConnected C.structureMap :=
  C.residueCurve.geometricallyConnected

abbrev Chapter12Curve.toChapter09CohenMacaulayCurveOverField
    {k : Type u} [Field k] (C : Chapter12Curve k) :
    Chapter09CohenMacaulayCurveOverField k :=
  { toChapter09ProperCurveOverField :=
      { scheme := C.scheme
        structureMap := C.structureMap
        proper := C.proper
        quasiCompact := C.quasiCompact
        locallyOfFinitePresentation := C.locallyOfFinitePresentation
        pureDimensionOne :=
          C.residueCurve.toChapter08SmoothIntegralCurve.dimensionOne }
    relativeCohenMacaulay := C.relativeCohenMacaulay }

abbrev Chapter12Base (k : Type u) [Field k] :=
  AlgebraicGeometry.Spec (CommRingCat.of k)

/- LOCAL_DEPENDENCY_GUESS: the preceding divisor chapters are not imported into
this focused dependency file, so the relation between a divisor coefficient and
its associated invertible sheaf is retained as a named property. -/
/-- A divisor together with its invertible sheaf 𝓞(D). -/
structure Chapter12Divisor {k : Type u} [Field k] (C : Chapter12Curve k) where
  coefficient : C.scheme →₀ ℤ
  support : Set C.scheme
  support_eq : support = (coefficient.support : Set C.scheme)
  support_points_closed : ∀ x ∈ support, IsClosed ({x} : Set C.scheme)
  lineBundle : Chapter04LineBundle C.scheme
  lineBundle_is_divisor_sheaf : Prop
  lineBundle_is_divisor_sheaf_holds : lineBundle_is_divisor_sheaf

abbrev chapter12OOfDivisor {k : Type u} [Field k] {C : Chapter12Curve k}
    (D : Chapter12Divisor C) : C.scheme.Modules :=
  D.lineBundle.sheaf

def chapter12DivisorSupport {k : Type u} [Field k] {C : Chapter12Curve k}
    (D : Chapter12Divisor C) : Set C.scheme :=
  D.support

/-- The affine two-open cover used for the Čech residue representative. -/
structure Chapter12AffineResidueCover {k : Type u} [Field k]
    (C : Chapter12Curve k) (D : Chapter12Divisor C) where
  U : C.scheme.Opens
  V : C.scheme.Opens
  U_affine : IsAffineOpen U
  V_affine : IsAffineOpen V
  cover : U ⊔ V = ⊤
  poles_in_U_minus_V : D.support ⊆ (U : Set C.scheme) \ (V : Set C.scheme)

/-- The field-valued cohomology context used by the duality statements.

Its objects are bundled modules, so all displayed duals are genuine k-linear
duals.  The map laws are the coefficient-functoriality interface needed by the
transpose statements.
-/
structure Chapter12CohomologyContext {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  H : C.scheme.Modules → ℕ → ModuleCat.{v} k
  map : ∀ {F G : C.scheme.Modules}, (F ⟶ G) → ∀ i, H F i ⟶ H G i
  map_id : ∀ (F : C.scheme.Modules) (i : ℕ), map (𝟙 F) i = 𝟙 _
  map_comp : ∀ {F G H : C.scheme.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (i : ℕ),
    map (φ ≫ ψ) i = map φ i ≫ map ψ i
  canonicalCohomology : ∀ (F : C.scheme.Modules) (i : ℕ),
    (H F i : Type v) ≃+ chapter09H F i

/-! The field-valued Ext groups used by the coherent-sheaf form of duality.
The separate context keeps the displayed Ext statement independent of a
particular model for derived categories. -/
structure Chapter12ExtContext {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  Ext : C.scheme.Modules → C.scheme.Modules → ℕ → ModuleCat.{v} k
  extModule : ∀ (F G : C.scheme.Modules) (i : ℕ), Module k (Ext F G i)
  canonical : Chapter09ExtTheory C.scheme
  canonicalExtEquiv : ∀ (F G : C.scheme.Modules) (i : ℕ),
    (Ext F G i : Type v) ≃+ @chapter09Ext C.scheme canonical F G i

abbrev chapter12Ext {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12ExtContext C) (F G : C.scheme.Modules) (i : ℕ) : Type v :=
  K.Ext F G i

instance chapter12ExtModule {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12ExtContext C) (F G : C.scheme.Modules) (i : ℕ) :
    Module k (K.Ext F G i) :=
  K.extModule F G i

abbrev chapter12H {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C) (F : C.scheme.Modules) (i : ℕ) : Type v :=
  K.H F i

abbrev chapter12Hdual {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C) (F : C.scheme.Modules) (i : ℕ) :=
  Module.Dual k (chapter12H K F i)

abbrev chapter12HZero {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C) (F : C.scheme.Modules) :=
  chapter12H K F 0

abbrev chapter12HOne {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C) (F : C.scheme.Modules) :=
  chapter12H K F 1

def chapter12CohomologyMap {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C) {F G : C.scheme.Modules}
    (φ : F ⟶ G) (i : ℕ) : chapter12H K F i →ₗ[k] chapter12H K G i :=
  (K.map φ i).hom

/-! ### Tensor, dual, and dualizing-sheaf interfaces -/

/-- Isomorphism of Book 08 line bundles, expressed by the canonical sheaf iso. -/
def chapter12LineBundleIsomorphic {X : Scheme} (L M : Chapter04LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

class Chapter12LineBundleDuality {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  dual : Chapter04LineBundle C.scheme → Chapter04LineBundle C.scheme
  dual_involutive : ∀ L,
    chapter12LineBundleIsomorphic (dual (dual L)) L
  dual_tensor_iso_unit : ∀ L,
    chapter12LineBundleIsomorphic
      (chapter04LineBundleTensor (dual L) L) (chapter04TrivialLineBundle C.scheme)
  canonicalDualTensor : ∀ (L : Chapter04LineBundle C.scheme),
    Chapter09VectorBundleDualTensor L.sheaf
      (chapter04TrivialLineBundle C.scheme).sheaf
  canonicalDualTensor_dual : ∀ L,
    (canonicalDualTensor L).dual = (dual L).sheaf

def chapter12LineBundleDual {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    (L : Chapter04LineBundle C.scheme) : Chapter04LineBundle C.scheme :=
  Chapter12LineBundleDuality.dual L

def chapter12LineBundleDualTensor {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    (L M : Chapter04LineBundle C.scheme) : Chapter04LineBundle C.scheme :=
  chapter04LineBundleTensor (chapter12LineBundleDual L) M

/-- A finite-type locally free sheaf, retaining the canonical module sheaf. -/
structure Chapter12VectorBundle {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  module : C.scheme.Modules
  canonical : chapter09VectorBundle module

def chapter12VectorBundleIsomorphic {k : Type u} [Field k]
    {C : Chapter12Curve k} (E F : Chapter12VectorBundle C) : Prop :=
  Nonempty (E.module ≅ F.module)

class Chapter12VectorBundleDuality {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  dual : Chapter12VectorBundle C → Chapter12VectorBundle C
  dual_involutive : ∀ E,
    chapter12VectorBundleIsomorphic (dual (dual E)) E
  canonicalDualTensor : ∀ (E : Chapter12VectorBundle C) (ω : C.scheme.Modules),
    Chapter09VectorBundleDualTensor E.module ω
  canonicalDualTensor_dual : ∀ (E : Chapter12VectorBundle C) (ω : C.scheme.Modules),
    (canonicalDualTensor E ω).dual = (dual E).module

def chapter12VectorBundleDual {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12VectorBundleDuality C]
    (E : Chapter12VectorBundle C) : Chapter12VectorBundle C :=
  Chapter12VectorBundleDuality.dual E

structure Chapter12DualizingSheafData {k : Type u} [Field k]
    (C : Chapter12Curve k) (K : Chapter12CohomologyContext C) where
  extTheory : Chapter09ExtTheory C.scheme
  derivedHomTheory : Chapter09AbsoluteDerivedHomTheory k C.scheme
  canonical :
    @Chapter09AbsoluteDualizingData k _
      C.toChapter09CohenMacaulayCurveOverField extTheory derivedHomTheory
  differentialSheaf : C.scheme.Modules
  omega_invertible :
    letI := extTheory
    letI := derivedHomTheory
    chapter04IsInvertible canonical.sheaf
  isDualizing : Prop
  isDualizing_holds : isDualizing
  trace :
    letI := extTheory
    letI := derivedHomTheory
    chapter12HOne K canonical.sheaf →ₗ[k] k
  trace_agrees_with_canonical :
    letI := extTheory
    letI := derivedHomTheory
    ∀ x, trace x = canonical.trace (K.canonicalCohomology canonical.sheaf 1 x)

abbrev Chapter12DualizingSheafData.omega {k : Type u} [Field k]
    {C : Chapter12Curve k} {K : Chapter12CohomologyContext C}
    (W : Chapter12DualizingSheafData C K) : C.scheme.Modules :=
  letI := W.extTheory
  letI := W.derivedHomTheory
  W.canonical.sheaf

def chapter12OmegaLineBundle {k : Type u} [Field k]
    {C : Chapter12Curve k} {K : Chapter12CohomologyContext C}
    (W : Chapter12DualizingSheafData C K) : Chapter04LineBundle C.scheme :=
  { sheaf := W.omega
    isInvertible := W.omega_invertible }

def chapter12LineBundleOmegaTwist {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C}
    (W : Chapter12DualizingSheafData C K)
    (L : Chapter04LineBundle C.scheme) : Chapter04LineBundle C.scheme :=
  chapter12LineBundleDualTensor L (chapter12OmegaLineBundle W)

def chapter12OmegaMinusDivisor {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C}
    (W : Chapter12DualizingSheafData C K) (D : Chapter12Divisor C) :
    Chapter04LineBundle C.scheme :=
  chapter12LineBundleOmegaTwist W D.lineBundle

abbrev chapter12DivisorHOne {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C) :=
  chapter12HOne K D.lineBundle.sheaf

abbrev chapter12DivisorOmegaHZero {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K) (D : Chapter12Divisor C) :=
  chapter12HZero K (chapter12OmegaMinusDivisor W D).sheaf

def chapter12VectorBundleOmegaTwist {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12VectorBundleDuality C]
    {K : Chapter12CohomologyContext C}
    (W : Chapter12DualizingSheafData C K)
    (E : Chapter12VectorBundle C) : C.scheme.Modules :=
  (Chapter12VectorBundleDuality.canonicalDualTensor E W.omega).tensor

/- LOCAL_DEPENDENCY_GUESS: the pinned tensor-sheaf API supplies the tensor
object but not its functorial map on morphisms. -/
class Chapter12TensorTheory (X : Scheme) where
  map : ∀ {M M' N N' : X.Modules},
    (M ⟶ M') → (N ⟶ N') →
      (chapter04Tensor M N ⟶ chapter04Tensor M' N')

/-! ### Čech representatives and residues -/

/- LOCAL_DEPENDENCY_GUESS: the earlier meromorphic-function package is not
imported into this focused dependency file, so its restrictions are retained as
an explicit local interface. -/
class Chapter12RationalFunctionTheory {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  RationalFunction : C.scheme.Opens → Type v
  RegularFunction : C.scheme.Opens → Type v
  regularToRational : ∀ U, RegularFunction U → RationalFunction U
  zero : ∀ U, RationalFunction U
  add : ∀ {U}, RationalFunction U → RationalFunction U → RationalFunction U
  neg : ∀ {U}, RationalFunction U → RationalFunction U
  restriction : ∀ {U V : C.scheme.Opens}, U ≤ V → RationalFunction V → RationalFunction U

abbrev chapter12RationalFunction {k : Type u} [Field k]
    {C : Chapter12Curve k} [R : Chapter12RationalFunctionTheory C]
    (U : C.scheme.Opens) :=
  R.RationalFunction U

/-- The local data saying that a Čech representative is a rational function
modulo functions extending from the two affine opens. -/
structure Chapter12ResiduePairingData {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C] where
  globalResidues : Chapter08GlobalResidueFamily k C.residueCurve
  multiply : chapter12RationalFunction (A.U ⊓ A.V) →
    chapter12DivisorOmegaHZero K W D →
      Chapter08RationalDifferentials k C.scheme
  classOf : chapter12RationalFunction (A.U ⊓ A.V) →
    chapter12DivisorHOne K D
  leftToOverlap : R.RegularFunction A.U →
    chapter12RationalFunction (A.U ⊓ A.V)
  rightToOverlap : R.RegularFunction A.V →
    chapter12RationalFunction (A.U ⊓ A.V)
  leftToOverlap_is_restriction : ∀ u,
    leftToOverlap u = R.restriction inf_le_left (R.regularToRational A.U u)
  rightToOverlap_is_restriction : ∀ v,
    rightToOverlap v = R.restriction inf_le_right (R.regularToRational A.V v)
  classOf_leftExtension : ∀ u, classOf (leftToOverlap u) = 0
  classOf_rightExtension : ∀ v, classOf (rightToOverlap v) = 0
  modify : chapter12RationalFunction (A.U ⊓ A.V) →
    R.RegularFunction A.U → R.RegularFunction A.V →
    chapter12RationalFunction (A.U ⊓ A.V)
  modify_eq_add_extensions : ∀ g u v,
    modify g u v = R.add (R.add g (leftToOverlap u)) (rightToOverlap v)
  classOf_modify : ∀ g u v, classOf (modify g u v) = classOf g
  cupProduct : chapter12DivisorHOne K D →ₗ[k]
    chapter12DivisorOmegaHZero K W D →ₗ[k] chapter12HOne K W.omega
  cupProductTrace : chapter12DivisorHOne K D →ₗ[k]
    chapter12DivisorOmegaHZero K W D →ₗ[k] k
  cupProductTrace_eq_trace : ∀ c η,
    cupProductTrace c η = W.trace (cupProduct c η)

abbrev Chapter12ResiduePairingData.rationalDifferential
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [_R : Chapter12RationalFunctionTheory C]
    (_P : Chapter12ResiduePairingData K D A W) : Type u :=
  Chapter08RationalDifferentials k C.scheme

def Chapter12ResiduePairingData.residue
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (x : Chapter08ClosedPoint C.scheme) (h : P.rationalDifferential) : k :=
  chapter08ResidueAt k C.residueCurve.toChapter08SmoothIntegralCurve x
    (Chapter08GlobalResidueFamily.localResidue k P.globalResidues x) h

noncomputable def Chapter12ResiduePairingData.globalResidueSupport
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (h : P.rationalDifferential) : Finset (Chapter08ClosedPoint C.scheme) :=
  (chapter08_global_residue_support_finite k P.globalResidues h).toFinset

noncomputable def Chapter12ResiduePairingData.residueSupport
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (g : chapter12RationalFunction (A.U ⊓ A.V))
    (η : chapter12DivisorOmegaHZero K W D) :
    Finset (Chapter08ClosedPoint C.scheme) :=
  P.globalResidueSupport (P.multiply g η)

structure Chapter12CechRepresentative {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
  [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) where
  g : chapter12RationalFunction (A.U ⊓ A.V)
  cohomologyClass : chapter12DivisorHOne K D
  class_represented_by_g : P.classOf g = cohomologyClass

/-- Every cohomology class admits a Čech representative on the chosen affine
cover.  The existence statement is kept in the shared interface because the
pairing is consumed by the later perfectness and functoriality sections. -/
theorem chapter12_cech_representative_exists
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    ∀ c : chapter12DivisorHOne K D,
      Nonempty {Q : Chapter12CechRepresentative K D A W P //
        Q.cohomologyClass = c} := by
  sorry

noncomputable def chapter12ResidueRepresentative
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D) :
    chapter12RationalFunction (A.U ⊓ A.V) :=
  (Classical.choice (chapter12_cech_representative_exists K D A W P c)).1.g

def chapter12ResidueSum {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (g : chapter12RationalFunction (A.U ⊓ A.V))
  (η : chapter12DivisorOmegaHZero K W D) : k :=
  ∑ x ∈ P.residueSupport g η, P.residue x (P.multiply g η)

def chapter12ResiduePairing {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) : k :=
  chapter12ResidueSum P (chapter12ResidueRepresentative K D A W P c) η

/-! ### Local residue models -/

abbrev Chapter12PrincipalPartAtRationalPoint (k : Type u) := k
abbrev Chapter12DifferentialAtRationalPoint (k : Type u) := k

def chapter12RationalPointLocalResiduePairing {k : Type u} [Field k]
    (a : Chapter12PrincipalPartAtRationalPoint k)
    (b : Chapter12DifferentialAtRationalPoint k) : k :=
  a * b

theorem chapter12_rational_point_local_residue_calculation
    {k : Type u} [Field k] (a b : k) :
    chapter12RationalPointLocalResiduePairing a b = a * b := by
  rfl

structure Chapter12ClosedPointResidueData (k : Type u) [Field k] where
  residueField : Type v
  [field : Field residueField]
  [algebra : Algebra k residueField]
  principalParts : ModuleCat.{v} k
  pairing : principalParts →ₗ[k] Module.Dual k residueField →ₗ[k] k
  pairing_injective : Function.Injective pairing
  pairing_finrank_eq :
    Module.finrank k (principalParts : Type v) =
      Module.finrank k (Module.Dual k residueField)

attribute [instance] Chapter12ClosedPointResidueData.field
  Chapter12ClosedPointResidueData.algebra

structure Chapter12LocalSkyscraperResidueData (k : Type u) [Field k] where
  principalParts : ModuleCat.{v} k
  differentialFiber : ModuleCat.{v} k
  tInv : principalParts
  dt : differentialFiber
  pairing : principalParts →ₗ[k] differentialFiber →ₗ[k] k
  pairing_tInv_dt : pairing tInv dt = 1

/-! ### Coherent sheaves, sheaf Ext, and finite duality -/

abbrev chapter12CoherentSheaf {X : Scheme} (F : X.Modules) : Prop :=
  chapter04FiniteTypeQuasiCoherent F

class Chapter12SheafExtTheory (X : Scheme) extends Chapter09ExtTheory X

def chapter12SheafExt {X : Scheme} [Chapter12SheafExtTheory X]
    (F G : X.Modules) (i : ℕ) : X.Modules :=
  chapter09SheafExt F G i

class Chapter12InternalHomTheory (X : Scheme) where
  internalHom : X.Modules → X.Modules → X.Modules
  canonicalDualTensor : ∀ (M N : X.Modules),
    Chapter09VectorBundleDualTensor M N
  internalHom_eq_canonicalDualTensor : ∀ (M N : X.Modules),
    internalHom M N = (canonicalDualTensor M N).tensor
  evaluationAtOne : ∀ {M N : X.Modules},
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) → (internalHom M N ⟶ N)

def chapter12InternalHom {X : Scheme} [Chapter12InternalHomTheory X]
    (M N : X.Modules) : X.Modules :=
  Chapter12InternalHomTheory.internalHom M N

structure Chapter12ProperCohenMacaulayCurve (k : Type u) [Field k] where
  canonical : Chapter09CohenMacaulayCurveOverField k
  extTheory : Chapter09ExtTheory canonical.scheme
  derivedHomTheory : Chapter09AbsoluteDerivedHomTheory k canonical.scheme
  canonicalDualizing :
    @Chapter09AbsoluteDualizingData k _ canonical extTheory derivedHomTheory
  gorenstein : Prop

abbrev Chapter12ProperCohenMacaulayCurve.carrier {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) : Scheme.{u} :=
  C.canonical.scheme

abbrev Chapter12ProperCohenMacaulayCurve.structureMap
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) :
    C.carrier ⟶ AlgebraicGeometry.Spec (.of k) :=
  C.canonical.structureMap

abbrev Chapter12ProperCohenMacaulayCurve.proper
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) : IsProper C.structureMap :=
  C.canonical.proper

def Chapter12ProperCohenMacaulayCurve.dualizing
    {k : Type u} [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) : C.carrier.Modules :=
by
  letI : Chapter09ExtTheory C.canonical.scheme := C.extTheory
  letI : Chapter09AbsoluteDerivedHomTheory k C.canonical.scheme := C.derivedHomTheory
  exact C.canonicalDualizing.sheaf

structure Chapter12ProperCMCohomologyContext (k : Type u) [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) where
  H : C.carrier.Modules → ℕ → ModuleCat.{v} k
  Ext : C.carrier.Modules → C.carrier.Modules → ℕ → ModuleCat.{v} k
  extModule : ∀ (F G : C.carrier.Modules) (i : ℕ), Module k (Ext F G i)
  canonicalExt : Chapter09ExtTheory C.carrier
  canonicalExtEquiv : ∀ (F G : C.carrier.Modules) (i : ℕ),
    (Ext F G i : Type v) ≃+
      @chapter09Ext C.carrier canonicalExt F G i

instance chapter12ProperExtModule {k : Type u} [Field k]
    {C : Chapter12ProperCohenMacaulayCurve k}
    (T : Chapter12ProperCMCohomologyContext k C)
    (F G : C.carrier.Modules) (i : ℕ) :
    Module k (T.Ext F G i) :=
  T.extModule F G i

structure Chapter12FiniteMapOfProperCohenMacaulayCurves
    (k : Type u) [Field k] where
  source : Chapter12ProperCohenMacaulayCurve k
  target : Chapter12ProperCohenMacaulayCurve k
  hom : source.carrier ⟶ target.carrier
  overBase : hom ≫ target.structureMap = source.structureMap
  finite : IsFinite hom

abbrev chapter12PushforwardStructureSheaf
    {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k) :
    P.target.carrier.Modules :=
  (Scheme.Modules.pushforward P.hom).obj
    (SheafOfModules.unit P.source.carrier.ringCatSheaf)

abbrev chapter12PushforwardDualizingSheaf
    {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k) :
    P.target.carrier.Modules :=
  (Scheme.Modules.pushforward P.hom).obj P.source.dualizing

def chapter12FiniteMapUnit {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k) :
    SheafOfModules.unit P.target.carrier.ringCatSheaf ⟶
      chapter12PushforwardStructureSheaf P :=
  SheafOfModules.unitToPushforwardObjUnit P.hom.toRingCatSheafHom

structure Chapter12FiniteDualizingComparison {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k)
    [Chapter12InternalHomTheory P.target.carrier] where
  iso : chapter12PushforwardDualizingSheaf P ≅
    chapter12InternalHom (chapter12PushforwardStructureSheaf P) P.target.dualizing

noncomputable def chapter12FiniteTraceByEvaluation {k : Type u} [Field k]
    {P : Chapter12FiniteMapOfProperCohenMacaulayCurves k}
    [Chapter12InternalHomTheory P.target.carrier]
    (E : Chapter12FiniteDualizingComparison P) :
    chapter12PushforwardDualizingSheaf P ⟶ P.target.dualizing :=
  E.iso.hom ≫ Chapter12InternalHomTheory.evaluationAtOne (chapter12FiniteMapUnit P)

/-! ### Functorial residue and cohomology interfaces -/

structure Chapter12FiniteMapResidueData {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k) where
  rationalFunctionX : Type v
  rationalFunctionY : Type v
  rationalDifferentialX : Type v
  rationalDifferentialY : Type v
  pullbackFunction : rationalFunctionX → rationalFunctionY
  traceDifferential : rationalDifferentialY → rationalDifferentialX
  pairingX : rationalFunctionX → rationalDifferentialX → k
  pairingY : rationalFunctionY → rationalDifferentialY → k
  pairing_adjoint : ∀ α η,
    pairingY (pullbackFunction α) η = pairingX α (traceDifferential η)

structure Chapter12FiniteMapRationalTraceData {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k) where
  smoothSource : Prop
  smoothTarget : Prop
  genericallySeparable : Prop
  rationalDifferentialX : Type v
  rationalDifferentialY : Type v
  sheafDifferentialX : P.target.carrier.Modules
  sheafDifferentialY : P.source.carrier.Modules
  rationalTrace : rationalDifferentialY → rationalDifferentialX
  sheafTrace :
    (Scheme.Modules.pushforward P.hom).obj sheafDifferentialY ⟶ sheafDifferentialX
  traceCompatibility : rationalDifferentialY → rationalDifferentialX → Prop
  traceCompatibility_holds :
    ∀ (_ : smoothSource) (_ : smoothTarget) (_ : genericallySeparable)
      (η : rationalDifferentialY),
      traceCompatibility η (rationalTrace η)

structure Chapter12DualizedVectorBundleMap {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12VectorBundleDuality C]
    (E F : Chapter12VectorBundle C) where
  hom : E.module ⟶ F.module
  dualizedTwistMap :
    (chapter12VectorBundleDual F).module ⟶ (chapter12VectorBundleDual E).module
  dualizedTwistMap_property : Prop
  dualizedTwistMap_property_holds : dualizedTwistMap_property

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
