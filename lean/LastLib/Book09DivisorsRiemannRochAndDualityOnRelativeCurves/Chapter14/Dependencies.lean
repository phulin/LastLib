import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.LinearAlgebra.Dual.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Section01WhyOrdinaryDifferentialsAreNotEnough
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Section02DualizingSheavesOnProperCurves
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Section04SmoothAndGorensteinFamilies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10.Section04FamiliesOfNodalCurves
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13.Section02SemicontinuityAndBaseChange

/-!
## Chapter 14: relative duality interfaces

The pinned Mathlib tree supplies schemes, sheaves of modules, pullback and
pushforward, geometric connectedness and reducedness, but not the coherent
relative-duality package used by this chapter.  This file keeps the canonical
Mathlib objects at the boundary and isolates the missing book-level interfaces
in small data structures.
-/

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13

noncomputable section

universe u

/-! ### Standing relative-curve hypotheses -/

/- A weakened context is used only for the failure-mode records in Section
14.4.  In particular, it deliberately does not carry the hypothesis whose
failure is being exhibited. -/
structure Chapter14RelativeCurveContext where
  X : Scheme
  S : Scheme
  map : X ⟶ S
  relativeCurve : Chapter09RelativeCurveData map
  relativeCurve_hypothesis : relativeCurve.fibers_are_curves
  baseLocallyNoetherian : IsLocallyNoetherian S
  geometricallyReducedFibers : GeometricallyReduced map

abbrev Chapter14RelativeCurveContext.relativeDimensionOne
    (C : Chapter14RelativeCurveContext) : Prop :=
  C.relativeCurve.fibers_are_curves

/- The earlier Book 9 interfaces expose total-space Cohen--Macaulayness and
Gorensteinness of a morphism.  Relative Cohen--Macaulayness itself is still a
book-facing hypothesis in the pinned API, so the family keeps it explicit. -/

structure Chapter14RelativeCurveFamily where
  X : Scheme
  S : Scheme
  map : X ⟶ S
  proper : IsProper map
  flat : Flat map
  finitePresentation : LocallyOfFinitePresentation map
  baseLocallyNoetherian : IsLocallyNoetherian S
  geometricallyReducedFibers : GeometricallyReduced map
  relativeCurve : Chapter09RelativeCurveData map
  relativeCurve_hypothesis : relativeCurve.fibers_are_curves
  relativeCohenMacaulay : ∀ s : S,
    chapter09CohenMacaulay (pullback map (S.fromSpecResidueField s))
  Gorenstein : chapter09GorensteinMorphism map

abbrev Chapter14RelativeCurveFamily.relativeDimensionOne
    (C : Chapter14RelativeCurveFamily) : Prop :=
  C.relativeCurve.fibers_are_curves

abbrev Chapter14RelativeCurveFamily.structureMap
    (C : Chapter14RelativeCurveFamily) : C.X ⟶ C.S :=
  C.map

def chapter14GeometricallyConnectedReducedFibers
    (C : Chapter14RelativeCurveFamily) : Prop :=
  GeometricallyConnected C.map ∧ GeometricallyReduced C.map

/-! A function on the points of a scheme is locally constant when it is
constant on an open neighbourhood of every point.  The cohomology-and-base-
change interfaces below use this predicate instead of accidentally requiring
one value on disconnected bases. -/
def chapter14LocallyConstant {S : Scheme} {α : Type} (g : S → α) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∀ t : S, t ∈ U → g t = g s

structure Chapter14SmoothRelativeCurveFamily where
  curve : Chapter14RelativeCurveFamily
  smooth : Smooth curve.map
  geometricallyConnectedFibers : GeometricallyConnected curve.map
  genus : ℕ
  fiberGenus : curve.S → ℕ
  fiberGenus_eq_genus : ∀ s : curve.S, fiberGenus s = genus

structure Chapter14NodalRelativeCurveFamily where
  curve : Chapter14RelativeCurveFamily
  nodalFibers : ∀ s : curve.S,
    Chapter10NodalCurvePredicate (curve.map.fiber s)
  geometricallyConnectedFibers : GeometricallyConnected curve.map
  arithmeticGenus : ℕ
  fiberArithmeticGenus : curve.S → ℕ
  fiberArithmeticGenus_eq_arithmeticGenus :
    ∀ s : curve.S, fiberArithmeticGenus s = arithmeticGenus

/-! ### Vector bundles, tensor products, and sheaf duals -/

structure Chapter14VectorBundle (X : Scheme) where
  sheaf : X.Modules
  finiteLocallyFree : chapter04FiniteLocallyFree sheaf

abbrev chapter14StructureSheaf (X : Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def chapter14VectorBundleOfLineBundle {X : Scheme} (L : Chapter04LineBundle X)
    (hL : chapter04FiniteLocallyFree L.sheaf) :
    Chapter14VectorBundle X :=
  { sheaf := L.sheaf
    finiteLocallyFree := hL }

/- LOCAL_DEPENDENCY_GUESS: internal-Hom sheaves and their functorial dual maps
are not exposed by the pinned scheme-module API.  This is the book-facing
interface for the dual of a finite locally free sheaf; all operations below
are required to be contravariantly functorial. -/

structure Chapter14SheafDualityData (X : Scheme) where
  dual : X.Modules → X.Modules
  dualMap : ∀ {M N : X.Modules}, (M ⟶ N) → (dual N ⟶ dual M)
  dualMap_id : ∀ (M : X.Modules), dualMap (𝟙 M) = 𝟙 (dual M)
  dualMap_comp : ∀ {M N P : X.Modules} (u : M ⟶ N) (v : N ⟶ P),
    dualMap (u ≫ v) = dualMap v ≫ dualMap u
  tensorMapLeft : ∀ {M N P : X.Modules}, (M ⟶ N) →
    ((chapter04Tensor M P) ⟶ (chapter04Tensor N P))
  tensorMapLeft_id : ∀ (M P : X.Modules),
    tensorMapLeft (𝟙 M : M ⟶ M) = 𝟙 (chapter04Tensor M P)
  tensorMapLeft_comp : ∀ {M N P : X.Modules}
      (u : M ⟶ N) (v : N ⟶ P) (W : X.Modules),
    tensorMapLeft (P := W) (u ≫ v) =
      tensorMapLeft (P := W) u ≫ tensorMapLeft (P := W) v
  dualFiniteLocallyFree : ∀ {M : X.Modules},
    chapter04FiniteLocallyFree M → chapter04FiniteLocallyFree (dual M)
  evaluation : ∀ (M : X.Modules),
    chapter04Tensor (dual M) M ⟶ chapter14StructureSheaf X

def chapter14DualVectorBundle {X : Scheme} (D : Chapter14SheafDualityData X)
    (E : Chapter14VectorBundle X) : Chapter14VectorBundle X :=
  { sheaf := D.dual E.sheaf
    finiteLocallyFree := D.dualFiniteLocallyFree E.finiteLocallyFree }

/-! ### Relative higher direct images -/

/- The pinned Mathlib API does not expose the sheaves `R^i f_* M` in the
module-sheaf interface used here.  This chapter-level theory records those
objects, their module functoriality, and the degree-zero comparison with
ordinary pushforward.  A relative-duality package below additionally compares
these sheaves with Chapter 9's typed derived homology. -/

structure Chapter14RelativeCohomologyTheory where
  higherDirectImage : ∀ {X S : Scheme} (_f : X ⟶ S), X.Modules → ℕ → S.Modules
  map : ∀ {X S : Scheme} (f : X ⟶ S) {M N : X.Modules},
    (M ⟶ N) → ∀ i : ℕ,
      higherDirectImage f M i ⟶ higherDirectImage f N i
  map_id : ∀ {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (i : ℕ),
    map f (𝟙 M) i = 𝟙 (higherDirectImage f M i)
  map_comp : ∀ {X S : Scheme} (f : X ⟶ S)
      {M N P : X.Modules} (u : M ⟶ N) (v : N ⟶ P) (i : ℕ),
    map f (u ≫ v) i = map f u i ≫ map f v i
  degreeZeroIso : ∀ {X S : Scheme} (f : X ⟶ S) (M : X.Modules),
    higherDirectImage f M 0 ≅ (Scheme.Modules.pushforward f).obj M
  baseChangeMap : ∀ {X S T : Scheme} (f : X ⟶ S) (M : X.Modules) (i : ℕ)
      (g : T ⟶ S),
    (Scheme.Modules.pullback g).obj (higherDirectImage f M i) ⟶
      higherDirectImage (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj M) i

abbrev chapter14HigherDirectImage (H : Chapter14RelativeCohomologyTheory)
    {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (i : ℕ) : S.Modules :=
  H.higherDirectImage f M i

abbrev chapter14R1Pushforward (H : Chapter14RelativeCohomologyTheory)
    {X S : Scheme} (f : X ⟶ S) (M : X.Modules) : S.Modules :=
  H.higherDirectImage f M 1

def chapter14RelativeCohomologyFinite
    (H : Chapter14RelativeCohomologyTheory) {X S : Scheme}
    (f : X ⟶ S) (M : X.Modules) (i : ℕ) : Prop :=
  chapter04FiniteLocallyFree (H.higherDirectImage f M i)

def chapter14HigherDirectImageCommutesWithBaseChange
    (H : Chapter14RelativeCohomologyTheory) {X S : Scheme}
    (f : X ⟶ S) (M : X.Modules) (i : ℕ) : Prop :=
  ∀ {T : Scheme} (g : T ⟶ S),
    IsIso (H.baseChangeMap f M i g)

/-! ### Relative dualizing sheaves and their base change -/

/- The preceding Chapter 9 interface records relative duality at a derived
level.  The wrapper below keeps that derived object and its typed trace, while
also exposing the module-sheaf pullback comparison used by this chapter. -/

structure Chapter14RelativeDualizingSheafTheory
    (C : Chapter14RelativeCurveFamily) where
  derivedTheory : Chapter09RelativeDerivedHomTheory C.map
  derived : @Chapter09RelativeDualizingData C.X C.S C.map derivedTheory
  invertible : chapter04IsInvertible derived.omega
  baseChangeOmega : ∀ {T : Scheme} (g : T ⟶ C.S),
    (pullback C.map g).Modules
  baseChangeIso : ∀ {T : Scheme} (g : T ⟶ C.S),
    (Scheme.Modules.pullback (pullback.fst C.map g)).obj derived.omega ≅
      baseChangeOmega g
  baseChangeOmegaInvertible : ∀ {T : Scheme} (g : T ⟶ C.S),
    chapter04IsInvertible (baseChangeOmega g)

namespace Chapter14RelativeDualizingSheafTheory

abbrev omega {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C) : C.X.Modules :=
  @Chapter09RelativeDualizingData.omega C.X C.S C.map W.derivedTheory W.derived

end Chapter14RelativeDualizingSheafTheory

abbrev chapter14RelativeDualizingSheaf
    {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C) : C.X.Modules :=
  W.omega

def chapter14RelativeDualizingLineBundle
    {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C) : Chapter04LineBundle C.X :=
  { sheaf := W.omega
    isInvertible := W.invertible }

/-! Chapter 9's typed comparison for a base-changed dualizing package. -/

structure Chapter14RelativeDerivedBaseChangeData
    (C : Chapter14RelativeCurveFamily)
    (W : Chapter14RelativeDualizingSheafTheory C)
    {T : Scheme} (g : T ⟶ C.S) where
  derivedTheory : Chapter09RelativeDerivedHomTheory (pullback.snd C.map g)
  derived : @Chapter09RelativeDualizingData
    (pullback C.map g) T (pullback.snd C.map g) derivedTheory
  comparison : @Chapter09RelativeBaseChangeComparison
    C.X C.S T C.map g W.derivedTheory derivedTheory W.derived
      derived

/-! ### Trace, multiplication, and the local two-term model -/

structure Chapter14RelativeBaseChangeTraceData
    (C : Chapter14RelativeCurveFamily)
    (H : Chapter14RelativeCohomologyTheory)
    (W : Chapter14RelativeDualizingSheafTheory C)
    (trace : chapter14R1Pushforward H C.map W.omega ⟶
      chapter14StructureSheaf C.S)
    {T : Scheme} (g : T ⟶ C.S) where
  omegaIso :
    (Scheme.Modules.pullback (pullback.fst C.map g)).obj W.omega ≅
      W.baseChangeOmega g
  cohomologyIso :
    (Scheme.Modules.pullback g).obj
        (chapter14R1Pushforward H C.map W.omega) ≅
      chapter14R1Pushforward H (pullback.snd C.map g)
        ((Scheme.Modules.pullback (pullback.fst C.map g)).obj W.omega)
  unitIso :
    (Scheme.Modules.pullback g).obj (chapter14StructureSheaf C.S) ≅
      chapter14StructureSheaf T
  traceAfterBaseChange :
    chapter14R1Pushforward H (pullback.snd C.map g) (W.baseChangeOmega g) ⟶
      chapter14StructureSheaf T
  derivedComparison : Chapter14RelativeDerivedBaseChangeData C W g
  trace_compatibility :
    cohomologyIso.hom ≫
        H.map (pullback.snd C.map g) omegaIso.hom 1 ≫ traceAfterBaseChange =
      (Scheme.Modules.pullback g).map trace ≫ unitIso.hom

/-! A perfect-pairing witness keeps the pairing map connected to its two
duality isomorphisms. -/
structure Chapter14PerfectPairingData
    {S : Scheme} (A B : S.Modules)
    (dual : Chapter14SheafDualityData S)
    (pairing : chapter04Tensor A B ⟶ chapter14StructureSheaf S) where
  rightToDual : B ≅ dual.dual A
  leftToDual : A ≅ dual.dual B
  pairing_eq_evaluation :
    pairing = dual.tensorMapLeft leftToDual.hom ≫ dual.evaluation B

structure Chapter14RelativeDualityData (C : Chapter14RelativeCurveFamily) where
  cohomology : Chapter14RelativeCohomologyTheory
  dualOnTotalSpace : Chapter14SheafDualityData C.X
  dualOnBase : Chapter14SheafDualityData C.S
  dualizing : Chapter14RelativeDualizingSheafTheory C
  trace : chapter14R1Pushforward cohomology C.map dualizing.omega ⟶
    chapter14StructureSheaf C.S
  multiplication : ∀ (E : Chapter14VectorBundle C.X),
    chapter04Tensor
        (chapter14R1Pushforward cohomology C.map E.sheaf)
        ((Scheme.Modules.pushforward C.map).obj
          (chapter04Tensor (dualOnTotalSpace.dual E.sheaf)
            dualizing.omega)) ⟶
      chapter14R1Pushforward cohomology C.map dualizing.omega
  derivedCohomologyComparison : ∀ (M : C.X.Modules) (i : ℕ),
    chapter14HigherDirectImage cohomology C.map M i ≅
      @chapter09RPushforward C.X C.S C.map dualizing.derivedTheory M i
  derivedTraceCompatibility :
    (derivedCohomologyComparison dualizing.omega 1).hom ≫
        @Chapter09RelativeDualizingData.trace C.X C.S C.map
          dualizing.derivedTheory dualizing.derived = trace
  derivedEvaluation : ∀ (E : C.X.Modules)
      (V : Chapter09VectorBundleDualTensor E dualizing.omega),
      chapter09VectorBundle E →
        Nonempty (@Chapter09RelativeDualityComparison C.X C.S C.map
          dualizing.derivedTheory E dualizing.omega V)
  baseChange : ∀ {T : Scheme} (g : T ⟶ C.S),
    Chapter14RelativeBaseChangeTraceData C cohomology dualizing trace g

def chapter14RelativePairing
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) (E : Chapter14VectorBundle C.X) :
    chapter04Tensor
        (chapter14R1Pushforward D.cohomology C.map E.sheaf)
        ((Scheme.Modules.pushforward C.map).obj
          (chapter04Tensor (D.dualOnTotalSpace.dual E.sheaf)
            D.dualizing.omega)) ⟶
      chapter14StructureSheaf C.S :=
  D.multiplication E ≫ D.trace

def chapter14PullbackTrace
    {C : Chapter14RelativeCurveFamily}
    (D : Chapter14RelativeDualityData C) {T : Scheme} (g : T ⟶ C.S) :
    (Scheme.Modules.pullback g).obj
        (chapter14R1Pushforward D.cohomology C.map D.dualizing.omega) ⟶
      chapter14StructureSheaf T :=
  (Scheme.Modules.pullback g).map D.trace ≫ (D.baseChange g).unitIso.hom

structure Chapter14TraceIdentification {S : Scheme} (M : S.Modules)
    (trace : M ⟶ chapter14StructureSheaf S) where
  iso : M ≅ chapter14StructureSheaf S
  iso_hom_eq_trace : iso.hom = trace

/-! A two-term finite-free presentation and its transposed dual.

The kernel/cokernel fields are the sheaf-level analogue of Chapter 13's
finite-free two-term model.  They make the computation data actual typed
cohomology objects, rather than a proposition which could be unrelated to the
displayed differential. -/

structure Chapter14FiniteFreeModel
    (C : Chapter14RelativeCurveFamily)
    (H : Chapter14RelativeCohomologyTheory)
    (E : Chapter14VectorBundle C.X) where
  K0 : C.S.Modules
  K1 : C.S.Modules
  differential : K0 ⟶ K1
  K0FiniteLocallyFree : chapter04FiniteLocallyFree K0
  K1FiniteLocallyFree : chapter04FiniteLocallyFree K1
  h0Model : C.S.Modules
  h0Kernel : h0Model ⟶ K0
  h0Kernel_comp : h0Kernel ≫ differential = 0
  h0IsKernel : IsLimit (KernelFork.ofι h0Kernel h0Kernel_comp)
  h1Model : C.S.Modules
  h1Cokernel : K1 ⟶ h1Model
  h1Cokernel_comp : differential ≫ h1Cokernel = 0
  h1IsCokernel : IsColimit (CokernelCofork.ofπ h1Cokernel h1Cokernel_comp)
  h0Identification : h0Model ≅
    chapter14HigherDirectImage H C.map E.sheaf 0
  h1Identification : h1Model ≅
    chapter14HigherDirectImage H C.map E.sheaf 1

/- The transposed complex reverses the actual kernel/cokernel computations.
Its two typed identifications are retained on the dualized cohomology terms. -/
structure Chapter14TransposedDualFiniteFreeModel
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    (dual : Chapter14SheafDualityData C.S)
    (K : Chapter14FiniteFreeModel C H E) where
  K0 : C.S.Modules
  K1 : C.S.Modules
  differential : K0 ⟶ K1
  K0_eq_dual_K1 : K0 = dual.dual K.K1
  K1_eq_dual_K0 : K1 = dual.dual K.K0
  differential_eq_dual : differential =
    eqToHom K0_eq_dual_K1 ≫ dual.dualMap K.differential ≫
      eqToHom K1_eq_dual_K0.symm
  K0FiniteLocallyFree : chapter04FiniteLocallyFree K0
  K1FiniteLocallyFree : chapter04FiniteLocallyFree K1
  h0Model : C.S.Modules
  h1Model : C.S.Modules
  h0Model_eq_dual_h1Model : h0Model = dual.dual K.h1Model
  h1Model_eq_dual_h0Model : h1Model = dual.dual K.h0Model
  h0Identification : h0Model ≅
    dual.dual (chapter14HigherDirectImage H C.map E.sheaf 1)
  h1Identification : h1Model ≅
    dual.dual (chapter14HigherDirectImage H C.map E.sheaf 0)

def chapter14TransposedDualModel
    {C : Chapter14RelativeCurveFamily}
    {H : Chapter14RelativeCohomologyTheory}
    {E : Chapter14VectorBundle C.X}
    (dual : Chapter14SheafDualityData C.S)
    (K : Chapter14FiniteFreeModel C H E) :
    Chapter14TransposedDualFiniteFreeModel dual K :=
  { K0 := dual.dual K.K1
    K1 := dual.dual K.K0
    differential := dual.dualMap K.differential
    K0_eq_dual_K1 := rfl
    K1_eq_dual_K0 := rfl
    differential_eq_dual := by sorry
    K0FiniteLocallyFree := dual.dualFiniteLocallyFree K.K1FiniteLocallyFree
    K1FiniteLocallyFree := dual.dualFiniteLocallyFree K.K0FiniteLocallyFree
    h0Model := dual.dual K.h1Model
    h1Model := dual.dual K.h0Model
    h0Model_eq_dual_h1Model := rfl
    h1Model_eq_dual_h0Model := rfl
    h0Identification := by sorry
    h1Identification := by sorry }

/-! ### Fiberwise and differential interfaces used by the Hodge statements -/

/- LOCAL_DEPENDENCY_GUESS: restriction of a sheaf to a scheme-theoretic fiber,
fiberwise coherent cohomology, and Kähler differential sheaves are not exposed
as one reusable interface in the pinned tree. -/

abbrev chapter14FiberModule {X S : Scheme} (f : X ⟶ S)
    (M : X.Modules) (s : S) : (f.fiber s).Modules :=
  (Scheme.Modules.pullback (f.fiberι s)).obj M

abbrev chapter14ResidueFiberModule {S : Scheme} (M : S.Modules) (s : S) :
    ModuleCat (S.residueField s) :=
  chapter13BaseResidueFiberModule M s

structure Chapter14FiberCohomologyModule
    (C : Chapter14RelativeCurveFamily)
    (M : C.X.Modules) (s : C.S) (i : ℕ) where
  module : ModuleCat (C.S.residueField s)
  finite : Module.Finite (C.S.residueField s) (module : Type)
  additive_identification :
    (AddCommGrpCat.uliftFunctor.{1, 0}).obj
        (AddCommGrpCat.of (module : Type)) ≅
      chapter04Cohomology (chapter14FiberModule C.map M s) i

structure Chapter14FiberCohomologyData
    (C : Chapter14RelativeCurveFamily) where
  baseFinite : ∀ (M : C.S.Modules) (s : C.S),
    Module.Finite (C.S.residueField s)
      (chapter14ResidueFiberModule M s : Type)
  h0 : ∀ (M : C.X.Modules) (s : C.S),
    Chapter14FiberCohomologyModule C M s 0
  h1 : ∀ (M : C.X.Modules) (s : C.S),
    Chapter14FiberCohomologyModule C M s 1

namespace Chapter14FiberCohomologyData

abbrev fiber {C : Chapter14RelativeCurveFamily}
    (_B : Chapter14FiberCohomologyData C)
    (M : C.S.Modules) (s : C.S) : ModuleCat (C.S.residueField s) :=
  chapter14ResidueFiberModule M s

noncomputable def fiberFinrank {C : Chapter14RelativeCurveFamily}
    (_B : Chapter14FiberCohomologyData C)
    (M : C.S.Modules) (s : C.S) : ℕ :=
  Module.finrank (C.S.residueField s)
    (chapter14ResidueFiberModule M s : Type)

abbrev h0Module {C : Chapter14RelativeCurveFamily}
    (B : Chapter14FiberCohomologyData C)
    (M : C.X.Modules) (s : C.S) : ModuleCat (C.S.residueField s) :=
  (B.h0 M s).module

abbrev h1Module {C : Chapter14RelativeCurveFamily}
    (B : Chapter14FiberCohomologyData C)
    (M : C.X.Modules) (s : C.S) : ModuleCat (C.S.residueField s) :=
  (B.h1 M s).module

end Chapter14FiberCohomologyData

structure Chapter14RelativeDifferentialData where
  theory : ∀ {X S : Scheme} (_f : X ⟶ S), Chapter09DifferentialSheafTheory _f

abbrev Chapter14RelativeDifferentialData.differentials
    (Ω : Chapter14RelativeDifferentialData)
    {X S : Scheme} (f : X ⟶ S) : X.Modules :=
  (Ω.theory f).omegaOne

structure Chapter14NodalFiberDifferentialDescription
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData F.curve) where
  normalizedDifferentials : ∀ s : F.curve.S,
    ModuleCat (F.curve.S.residueField s)
  normalizedDifferentialsFinite : ∀ s : F.curve.S,
    Module.Finite (F.curve.S.residueField s)
      (normalizedDifferentials s : Type)
  oppositeResidues : ∀ s : F.curve.S,
    (normalizedDifferentials s).carrier → Prop
  oppositeResidues_holds :
    ∀ (s : F.curve.S) (η : (normalizedDifferentials s).carrier),
      oppositeResidues s η
  fiberIsoNormalized : ∀ s : F.curve.S,
    Nonempty (
      (B.fiber
        ((Scheme.Modules.pushforward F.curve.map).obj D.dualizing.omega) s : Type) ≃ₗ[
          F.curve.S.residueField s] (normalizedDifferentials s : Type))
  normalizedComponentGenus : ∀ _s : F.curve.S, ℕ
  dualGraphCycleRank : ∀ _s : F.curve.S, ℕ
  arithmeticGenusDecomposition : ∀ s : F.curve.S,
    normalizedComponentGenus s + dualGraphCycleRank s = F.arithmeticGenus

structure Chapter14SmoothingDifferentialFailureWitness
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData) where
  coefficientField : Type
  [field : Field coefficientField]
  smoothing : Chapter10RamifiedSmoothingCounterexample coefficientField
  smoothingParameter : coefficientField
  torsionElement :
    KaehlerDifferential coefficientField
      (chapter10SmoothingRing coefficientField smoothingParameter)
  torsionAnnihilator : chapter10SmoothingRing coefficientField smoothingParameter
  torsionElement_ne_zero : torsionElement ≠ 0
  torsionAnnihilator_ne_zero : torsionAnnihilator ≠ 0
  torsion_annihilates : torsionAnnihilator • torsionElement = 0
  differentialSheaf : F.curve.X.Modules
  differentialSheaf_eq : differentialSheaf = Ω.differentials F.curve.map
  baseChangeTest : Scheme
  baseChange : baseChangeTest ⟶ F.curve.S
  differentialBaseChangeMap :
    (Scheme.Modules.pullback baseChange).obj
        ((Scheme.Modules.pushforward F.curve.map).obj differentialSheaf) ⟶
      (Scheme.Modules.pushforward (pullback.snd F.curve.map baseChange)).obj
        (Ω.differentials (pullback.snd F.curve.map baseChange))
  differentialBaseChangeMap_not_iso : ¬ IsIso differentialBaseChangeMap
  dualizingPushforwardLocallyFree :
    chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward F.curve.map).obj D.dualizing.omega)

def chapter14DifferentialPushforward
    (F : Chapter14SmoothRelativeCurveFamily)
    (Ω : Chapter14RelativeDifferentialData) : F.curve.S.Modules :=
  (Scheme.Modules.pushforward F.curve.map).obj (Ω.differentials F.curve.map)

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
