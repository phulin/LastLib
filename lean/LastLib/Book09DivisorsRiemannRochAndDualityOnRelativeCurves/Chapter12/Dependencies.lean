import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Abelian.Ext
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

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped BigOperators

universe u v

/-!
Shared interfaces for Chapter 12.

The preceding Book 09 chapters are not present in this checkout.  The records
below therefore keep the missing divisor, dualizing-sheaf, and residue seams
explicit while using the pinned Mathlib scheme/module objects and the earlier
Book 08 line-bundle and cohomology APIs.  The fields marked as local dependency
guesses are structural constructions, not statements of the duality theorem.
-/

/-! ### Curves, divisors, and cohomology -/

/-- A smooth proper geometrically connected relative curve over a field. -/
structure Chapter12Curve (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ AlgebraicGeometry.Spec (.of k)
  smooth : SmoothOfRelativeDimension 1 structureMap
  proper : IsProper structureMap
  geometricallyConnected : GeometricallyConnected structureMap

abbrev Chapter12Base (k : Type u) [Field k] :=
  AlgebraicGeometry.Spec (CommRingCat.of k)

/- LOCAL_DEPENDENCY_GUESS: the preceding divisor chapters are absent in this
checkout, so the relation between a divisor coefficient and its associated
invertible sheaf is retained as a named property. -/
/-- A divisor together with its invertible sheaf 𝓞(D). -/
structure Chapter12Divisor {k : Type u} [Field k] (C : Chapter12Curve k) where
  coefficient : C.scheme →₀ ℤ
  support : Set C.scheme
  support_eq : support = (coefficient.support : Set C.scheme)
  lineBundle : Chapter04LineBundle C.scheme
  lineBundle_is_divisor_sheaf : Prop

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

/-! The field-valued Ext groups used by the coherent-sheaf form of duality.
The separate context keeps the displayed Ext statement independent of a
particular model for derived categories. -/
structure Chapter12ExtContext {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  Ext : C.scheme.Modules → C.scheme.Modules → ℕ → ModuleCat.{v} k

abbrev chapter12Ext {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12ExtContext C) (F G : C.scheme.Modules) (i : ℕ) : Type v :=
  K.Ext F G i

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

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf API has the tensor construction but
not the inverse line-bundle constructor.  This class exposes the canonical
book-level dual of an invertible sheaf without assuming any cohomological
duality conclusion. -/
class Chapter12LineBundleDuality {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  unit : Chapter04LineBundle C.scheme
  dual : Chapter04LineBundle C.scheme → Chapter04LineBundle C.scheme
  dual_involutive : ∀ L,
    chapter12LineBundleIsomorphic (dual (dual L)) L
  dual_tensor_iso_unit : ∀ L,
    chapter12LineBundleIsomorphic
      (chapter04LineBundleTensor (dual L) L) unit

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
  locallyFree : module.IsLocallyFree
  finiteType : module.IsFiniteType

def chapter12VectorBundleIsomorphic {k : Type u} [Field k]
    {C : Chapter12Curve k} (E F : Chapter12VectorBundle C) : Prop :=
  Nonempty (E.module ≅ F.module)

/- LOCAL_DEPENDENCY_GUESS: the dual of a locally free sheaf is canonical, but
its book-facing closure and map API is not supplied by the assigned earlier
chapters. -/
class Chapter12VectorBundleDuality {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  dual : Chapter12VectorBundle C → Chapter12VectorBundle C
  dual_involutive : ∀ E,
    chapter12VectorBundleIsomorphic (dual (dual E)) E

def chapter12VectorBundleDual {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12VectorBundleDuality C]
    (E : Chapter12VectorBundle C) : Chapter12VectorBundle C :=
  Chapter12VectorBundleDuality.dual E

/- LOCAL_DEPENDENCY_GUESS: this is the missing relative-dualizing-sheaf
construction used by the preceding Chapter 9 interfaces.  The field
isDualizing names that geometric property; it is not a duality theorem. -/
structure Chapter12DualizingSheafData {k : Type u} [Field k]
    (C : Chapter12Curve k) (K : Chapter12CohomologyContext C) where
  omega : C.scheme.Modules
  omega_invertible : chapter04IsInvertible omega
  differentialSheaf : C.scheme.Modules
  omega_differential_iso : omega ≅ differentialSheaf
  isDualizing : Prop
  trace : chapter12HOne K omega →ₗ[k] k

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
  chapter04Tensor (chapter12VectorBundleDual E).module W.omega

/-! ### Čech representatives and residues -/

/- LOCAL_DEPENDENCY_GUESS: meromorphic functions and their restrictions are
not yet packaged for the scheme function field in the assigned chapters. -/
class Chapter12RationalFunctionTheory {k : Type u} [Field k]
    (C : Chapter12Curve k) where
  RationalFunction : C.scheme.Opens → Type v
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
  rationalDifferential : Type v
  multiply : chapter12RationalFunction (A.U ⊓ A.V) →
    chapter12DivisorOmegaHZero K W D → rationalDifferential
  residue : C.scheme → rationalDifferential → k
  globalResidueSupport : rationalDifferential → Finset C.scheme
  global_residue_theorem : ∀ h,
    ∑ x in globalResidueSupport h, residue x h = 0
  residueSupport : chapter12RationalFunction (A.U ⊓ A.V) →
    chapter12DivisorOmegaHZero K W D → Finset C.scheme
  residue_vanishes_off_support : ∀ g η x,
    x ∉ residueSupport g η → residue x (multiply g η) = 0
  classOf : chapter12RationalFunction (A.U ⊓ A.V) →
    chapter12DivisorHOne K D
  representative : chapter12DivisorHOne K D →
    chapter12RationalFunction (A.U ⊓ A.V)
  classOf_representative : ∀ c, classOf (representative c) = c
  leftExtension : Type v
  rightExtension : Type v
  leftToOverlap : leftExtension → chapter12RationalFunction (A.U ⊓ A.V)
  rightToOverlap : rightExtension → chapter12RationalFunction (A.U ⊓ A.V)
  classOf_leftExtension : ∀ u, classOf (leftToOverlap u) = 0
  classOf_rightExtension : ∀ v, classOf (rightToOverlap v) = 0
  modify : chapter12RationalFunction (A.U ⊓ A.V) → leftExtension → rightExtension →
    chapter12RationalFunction (A.U ⊓ A.V)
  modify_eq_add_extensions : ∀ g u v,
    modify g u v = R.add (R.add g (leftToOverlap u)) (rightToOverlap v)
  classOf_modify : ∀ g u v, classOf (modify g u v) = classOf g
  left_extension_residue_zero : ∀ u η,
    ∑ x in globalResidueSupport (multiply (leftToOverlap u) η),
      residue x (multiply (leftToOverlap u) η) = 0
  modify_invariant : ∀ g u v η,
    (∑ x in residueSupport g η, residue x (multiply g η)) =
      ∑ x in residueSupport (modify g u v) η,
        residue x (multiply (modify g u v) η)
  residuePairingLinear : chapter12DivisorHOne K D →ₗ[k]
    chapter12DivisorOmegaHZero K W D →ₗ[k] k
  residuePairingLinear_apply : ∀ c η,
    residuePairingLinear c η =
      ∑ x in residueSupport (representative c) η,
        residue x (multiply (representative c) η)
  cupProductTrace : chapter12DivisorHOne K D →
    chapter12DivisorOmegaHZero K W D → k
  cupProductTrace_eq_residueSum : ∀ c η,
    cupProductTrace c η =
      ∑ x in residueSupport (representative c) η,
        residue x (multiply (representative c) η)

structure Chapter12CechRepresentative {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) where
  g : chapter12RationalFunction (A.U ⊓ A.V)
  class : chapter12DivisorHOne K D
  class_represented_by_g : P.representative class = g

def chapter12ResidueSum {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (g : chapter12RationalFunction (A.U ⊓ A.V))
    (η : chapter12DivisorOmegaHZero K W D) : k :=
  ∑ x in P.residueSupport g η, P.residue x (P.multiply g η)

def chapter12ResiduePairing {k : Type u} [Field k]
    {C : Chapter12Curve k} [Chapter12LineBundleDuality C]
    {K : Chapter12CohomologyContext C} {D : Chapter12Divisor C}
    {A : Chapter12AffineResidueCover C D}
    {W : Chapter12DualizingSheafData C K}
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) : k :=
  chapter12ResidueSum P (P.representative c) η

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
  pairing_left_nondegenerate : ∀ x,
    (∀ φ, pairing x φ = 0) → x = 0
  pairing_right_nondegenerate : ∀ φ,
    (∀ x, pairing x φ = 0) → φ = 0

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

noncomputable def chapter12SheafExt {X : Scheme.{u}} (F G : X.Modules) (i : ℕ) :
    ModuleCat.{u + 1} ℤ := by
  letI : CategoryTheory.HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    CategoryTheory.HasExt.standard _
  exact ((CategoryTheory.Ext ℤ
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) i).obj
      (Opposite.op ((SheafOfModules.toSheaf X.ringCatSheaf).obj F))).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)

/- LOCAL_DEPENDENCY_GUESS: internal Hom sheaves and evaluation at the unit are
not exposed in the assigned Book 09 files. -/
class Chapter12InternalHomTheory (X : Scheme) where
  internalHom : X.Modules → X.Modules → X.Modules
  evaluationAtOne : ∀ {M N : X.Modules},
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) → internalHom M N ⟶ N

def chapter12InternalHom {X : Scheme} [Chapter12InternalHomTheory X]
    (M N : X.Modules) : X.Modules :=
  Chapter12InternalHomTheory.internalHom M N

/- LOCAL_DEPENDENCY_GUESS: Mathlib supplies IsFinite and the pushforward
functor, but not the book's Cohen--Macaulay curve and dualizing-sheaf package. -/
structure Chapter12ProperCohenMacaulayCurve (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structureMap
  oneDimensional : Prop
  cohenMacaulay : Prop
  dualizing : carrier.Modules
  dualizing_property : Prop
  gorenstein : Prop

structure Chapter12ProperCMCohomologyContext (k : Type u) [Field k]
    (C : Chapter12ProperCohenMacaulayCurve k) where
  H : C.carrier.Modules → ℕ → ModuleCat.{v} k
  Ext : C.carrier.Modules → C.carrier.Modules → ℕ → ModuleCat.{v} k

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
  SheafOfModules.unitToPushforwardObjUnit P.hom

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
  adjoint : ∀ α η,
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
  rationalTrace_is_sheafTrace : ∀ η,
    traceCompatibility η (rationalTrace η)

structure Chapter12DualizedVectorBundleMap {k : Type u} [Field k]
    {C : Chapter12Curve k} (E F : Chapter12VectorBundle C) where
  hom : E.module ⟶ F.module
  dualizedTwistMap :
    (chapter12VectorBundleDual F).module ⟶ (chapter12VectorBundleDual E).module
  dualizedTwistMap_property : Prop

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
