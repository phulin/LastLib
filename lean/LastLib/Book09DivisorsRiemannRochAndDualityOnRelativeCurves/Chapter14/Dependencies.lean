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
import Mathlib.CategoryTheory.Limits.Shapes.Pullback
import Mathlib.LinearAlgebra.Dual.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

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
  CohenMacaulay : Prop
  Gorenstein : Prop

abbrev Chapter14RelativeCurveContext.relativeDimensionOne
    (C : Chapter14RelativeCurveContext) : Prop :=
  C.relativeCurve.fibers_are_curves

/- LOCAL_DEPENDENCY_GUESS: the earlier Book 9 chapters have not yet exposed a
book-facing relative-curve predicate, Cohen--Macaulay predicate, or Gorenstein
predicate.  These fields keep the exact geometric hypotheses visible without
confusing them with smoothness. -/

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
  Gorenstein : Prop
  gorenstein : Gorenstein

abbrev Chapter14RelativeCurveFamily.relativeDimensionOne
    (C : Chapter14RelativeCurveFamily) : Prop :=
  C.relativeCurve.fibers_are_curves

abbrev Chapter14RelativeCurveFamily.structureMap
    (C : Chapter14RelativeCurveFamily) : C.X ⟶ C.S :=
  C.map

def chapter14GeometricallyConnectedReducedFibers
    (C : Chapter14RelativeCurveFamily) : Prop :=
  GeometricallyConnected C.map ∧ GeometricallyReduced C.map

structure Chapter14SmoothRelativeCurveFamily where
  curve : Chapter14RelativeCurveFamily
  smooth : Smooth curve.map
  geometricallyConnectedFibers : GeometricallyConnected curve.map
  genus : ℕ
  fiberGenus : ∀ s : curve.S, Prop
  fiberGenus_holds : ∀ s : curve.S, fiberGenus s

structure Chapter14NodalRelativeCurveFamily where
  curve : Chapter14RelativeCurveFamily
  nodalFibers : ∀ s : curve.S, Prop
  nodalFibers_holds : ∀ s : curve.S, nodalFibers s
  geometricallyConnectedFibers : GeometricallyConnected curve.map
  arithmeticGenus : ℕ
  arithmeticGenusIsConstant : ∀ s : curve.S, Prop
  arithmeticGenusIsConstant_holds : ∀ s : curve.S, arithmeticGenusIsConstant s

/-! ### Vector bundles, tensor products, and sheaf duals -/

structure Chapter14VectorBundle (X : Scheme) where
  sheaf : X.Modules
  finiteLocallyFree : chapter04FiniteLocallyFree sheaf

abbrev chapter14StructureSheaf (X : Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def chapter14VectorBundleOfLineBundle {X : Scheme} (L : Chapter04LineBundle X) :
    Chapter14VectorBundle X :=
  { sheaf := L.sheaf
    finiteLocallyFree := ⟨L.isInvertible.1, L.isInvertible.2.1⟩ }

/- LOCAL_DEPENDENCY_GUESS: internal-Hom sheaves and their functorial dual maps
are not exposed by the pinned scheme-module API.  This is the book-facing
interface for the dual of a finite locally free sheaf; all operations below
are required to be contravariantly functorial. -/

structure Chapter14SheafDualityData (X : Scheme) where
  dual : X.Modules → X.Modules
  dualMap : ∀ {M N : X.Modules}, (M ⟶ N) → dual N ⟶ dual M
  dualMap_id : ∀ (M : X.Modules), dualMap (𝟙 M) = 𝟙 (dual M)
  dualMap_comp : ∀ {M N P : X.Modules} (u : M ⟶ N) (v : N ⟶ P),
    dualMap (u ≫ v) = dualMap v ≫ dualMap u
  dualFiniteLocallyFree : ∀ {M : X.Modules},
    chapter04FiniteLocallyFree M → chapter04FiniteLocallyFree (dual M)
  evaluation : ∀ (M : X.Modules),
    chapter04Tensor (dual M) M ⟶ chapter14StructureSheaf X

def chapter14DualVectorBundle {X : Scheme} (D : Chapter14SheafDualityData X)
    (E : Chapter14VectorBundle X) : Chapter14VectorBundle X :=
  { sheaf := D.dual E.sheaf
    finiteLocallyFree := D.dualFiniteLocallyFree E.finiteLocallyFree }

/-! ### Relative higher direct images -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib's coherent cohomology API does not expose
the sheaves `R^i f_* M` used by the source.  The theory below records those
objects, their module functoriality, and the degree-zero comparison with
ordinary pushforward.  Base change is supplied by the hypotheses of the
relative-duality data below, not asserted for arbitrary cohomology sheaves. -/

structure Chapter14RelativeCohomologyTheory where
  higherDirectImage : ∀ {X S : Scheme} (f : X ⟶ S), X.Modules → ℕ → S.Modules
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
    Nonempty ((Scheme.Modules.pullback g).obj
        (H.higherDirectImage f M i) ≅
      H.higherDirectImage (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj M) i)

/-! ### Relative dualizing sheaves and their base change -/

/- LOCAL_DEPENDENCY_GUESS: the relative dualizing complex/sheaf is absent from
the pinned API.  The `omega` operation and its base-change isomorphisms are
kept explicit for the fixed relative curve family. -/

structure Chapter14RelativeDualizingSheafTheory
    (C : Chapter14RelativeCurveFamily) where
  omega : C.X.Modules
  invertible : chapter04IsInvertible omega
  baseChangeOmega : ∀ {T : Scheme} (g : T ⟶ C.S),
    (pullback C.map g).Modules
  baseChangeIso : ∀ {T : Scheme} (g : T ⟶ C.S),
    (Scheme.Modules.pullback (pullback.fst C.map g)).obj omega ≅
      baseChangeOmega g
  baseChangeOmegaInvertible : ∀ {T : Scheme} (g : T ⟶ C.S),
    chapter04IsInvertible (baseChangeOmega g)
  baseChangeIdentity : Prop
  baseChangeComposition : Prop

abbrev chapter14RelativeDualizingSheaf
    {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C) : C.X.Modules :=
  W.omega

def chapter14RelativeDualizingLineBundle
    {C : Chapter14RelativeCurveFamily}
    (W : Chapter14RelativeDualizingSheafTheory C) : Chapter04LineBundle C.X :=
  { sheaf := W.omega
    isInvertible := W.invertible }

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
  trace_compatibility :
    cohomologyIso.hom ≫
        H.map (pullback.snd C.map g) omegaIso.hom 1 ≫ traceAfterBaseChange =
      (Scheme.Modules.pullback g).map trace ≫ unitIso.hom

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

structure Chapter14PerfectPairingData
    {S : Scheme} (A B : S.Modules)
    (dual : Chapter14SheafDualityData S)
    (pairing : chapter04Tensor A B ⟶ chapter14StructureSheaf S) where
  rightToDual : B ≅ dual.dual A
  leftToDual : A ≅ dual.dual B
  perfect : Prop

/-! A two-term finite-free presentation and its transposed dual. -/

structure Chapter14FiniteFreeModel (S : Scheme) (M : S.Modules) where
  K0 : S.Modules
  K1 : S.Modules
  differential : K0 ⟶ K1
  K0FiniteLocallyFree : chapter04FiniteLocallyFree K0
  K1FiniteLocallyFree : chapter04FiniteLocallyFree K1
  computes : Prop

def chapter14TransposedDualModel {S : Scheme} {M : S.Modules}
    (dual : Chapter14SheafDualityData S)
    (K : Chapter14FiniteFreeModel S M) : Chapter14FiniteFreeModel S (dual.dual M) :=
  { K0 := dual.dual K.K1
    K1 := dual.dual K.K0
    differential := dual.dualMap K.differential
    K0FiniteLocallyFree := dual.dualFiniteLocallyFree K.K1FiniteLocallyFree
    K1FiniteLocallyFree := dual.dualFiniteLocallyFree K.K0FiniteLocallyFree
    computes := K.computes }

/-! ### Fiberwise and differential interfaces used by the Hodge statements -/

/- LOCAL_DEPENDENCY_GUESS: restriction of a sheaf to a scheme-theoretic fiber,
fiberwise coherent cohomology, and Kähler differential sheaves are not exposed
as one reusable interface in the pinned tree. -/

structure Chapter14FiberCohomologyData where
  fiber : ∀ {S : Scheme} (M : S.Modules) (s : S), Type
  h0 : ∀ {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (s : S), Type
  h1 : ∀ {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (s : S), Type
  pushforwardFiberIsoH0 : ∀ {X S : Scheme} (f : X ⟶ S) (M : X.Modules) (s : S),
    Nonempty (fiber ((Scheme.Modules.pushforward f).obj M) s ≃ h0 f M s)

structure Chapter14RelativeDifferentialData where
  differentials : ∀ {X S : Scheme} (f : X ⟶ S), X.Modules

structure Chapter14NodalFiberDifferentialDescription
    (F : Chapter14NodalRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (B : Chapter14FiberCohomologyData) where
  normalizedDifferentials : ∀ s : F.curve.S, Type
  oppositeResidues : ∀ s : F.curve.S, Prop
  fiberIsoNormalized : ∀ s : F.curve.S,
    Nonempty (B.fiber
      ((Scheme.Modules.pushforward F.curve.map)
        D.dualizing.omega) s ≃ normalizedDifferentials s)
  normalizedComponentGenus : ∀ s : F.curve.S, ℕ
  dualGraphCycleRank : ∀ s : F.curve.S, ℕ
  arithmeticGenusDecomposition : ∀ s : F.curve.S,
    normalizedComponentGenus s + dualGraphCycleRank s = F.arithmeticGenus
  nodePoleDifferentialsAccountForCycles : ∀ s : F.curve.S, Prop

structure Chapter14SmoothingDifferentialFailureWitness
    (F : Chapter14SmoothRelativeCurveFamily)
    (D : Chapter14RelativeDualityData F.curve)
    (Ω : Chapter14RelativeDifferentialData) where
  differentialHasTorsion : Prop
  differentialFailsBaseChange : Prop
  dualizingPushforwardLocallyFree :
    chapter04FiniteLocallyFree
      ((Scheme.Modules.pushforward F.curve.map).obj D.dualizing.omega)
  dualitySelectsDualizingExtension : Prop

def chapter14DifferentialPushforward
    (F : Chapter14SmoothRelativeCurveFamily)
    (Ω : Chapter14RelativeDifferentialData) : F.curve.S.Modules :=
  (Scheme.Modules.pushforward F.curve.map).obj (Ω.differentials F.curve.map)

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter14
