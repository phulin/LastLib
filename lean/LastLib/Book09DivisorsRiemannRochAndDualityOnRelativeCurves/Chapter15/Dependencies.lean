import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section05SymmetricPowersAndBaseChange
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Dependencies
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.Exact

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

universe u v

/-!
Shared Chapter 15 interfaces.

The preceding Book 8 chapters already provide the scheme-theoretic symmetric
power and universal Cartier-divisor APIs.  This file only supplies thin
book-facing names and the hypotheses which Chapter 15 repeatedly carries.
The Picard, dualizing, infinitesimal, and relative-cohomology constructions
which are not present in the pinned earlier API are introduced as explicit
data in the source-order leaves.
-/

abbrev Chapter15EffectiveCartierDivisor (X : Scheme.{u}) :=
  EffectiveCartierDivisor X

abbrev Chapter15RelativeEffectiveCartierDivisor {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) :=
  RelativeEffectiveCartierDivisor C T d

abbrev Chapter15LineBundle (X : Scheme.{u}) := Chapter09LineBundle X

abbrev Chapter15LineBundleIso {X : Scheme.{u}}
    (L M : Chapter15LineBundle X) := Chapter09LineBundleIso L M

abbrev Chapter15LineBundleSection {X : Scheme.{u}}
    (L : Chapter15LineBundle X) :=
  SheafOfModules.unit X.ringCatSheaf ⟶ L.module

def chapter15FieldBase (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of k)

def chapter15StructureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

noncomputable def chapter15Cohomology
    {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : AddCommGrpCat.{u + 1} :=
  chapter04Cohomology F i

abbrev chapter15H0 {X : Scheme.{u}} (F : X.Modules) : AddCommGrpCat.{u + 1} :=
  chapter15Cohomology F 0

abbrev chapter15H1 {X : Scheme.{u}} (F : X.Modules) : AddCommGrpCat.{u + 1} :=
  chapter15Cohomology F 1

def chapter15PullbackLineBundle {X Y : Scheme.{u}}
    (f : X ⟶ Y) (L : Chapter15LineBundle Y) : Chapter15LineBundle X :=
  chapter09PullbackLineBundle f L

/- The canonical sheaf tensor from Book 8 is reused here.  The wrapper keeps
  tensor products visible in Picard-equivalence statements without requiring a
  global tensor-theory instance on every scheme. -/
noncomputable def chapter15TensorLineBundles {X : Scheme.{u}}
    (L M : Chapter15LineBundle X) : Chapter15LineBundle X :=
  let B := chapter04LineBundleTensor
    (chapter09AsChapter04LineBundle L) (chapter09AsChapter04LineBundle M)
  { module := B.sheaf
    isInvertible := B.isInvertible }

/- The map between the two scheme-theoretic base changes induced by a morphism
   of relative test schemes. -/
noncomputable def chapter15CurveBaseChangeMap {S : Scheme.{u}}
    {C T U : RelativeScheme S} (u : U ⟶ T) :
    pullback C.structuralMap U.structuralMap ⟶
      pullback C.structuralMap T.structuralMap :=
  pullback.lift
    (pullback.fst C.structuralMap U.structuralMap)
    (pullback.snd C.structuralMap U.structuralMap ≫ u.hom) (by
      rw [Category.assoc, u.comm]
      exact pullback.condition)

@[simp]
theorem chapter15CurveBaseChangeMap_fst {S : Scheme.{u}}
    {C T U : RelativeScheme S} (u : U ⟶ T) :
    chapter15CurveBaseChangeMap u ≫
        pullback.fst C.structuralMap T.structuralMap =
      pullback.fst C.structuralMap U.structuralMap := by
  sorry

@[simp]
theorem chapter15CurveBaseChangeMap_snd {S : Scheme.{u}}
    {C T U : RelativeScheme S} (u : U ⟶ T) :
    chapter15CurveBaseChangeMap u ≫
        pullback.snd C.structuralMap T.structuralMap =
      pullback.snd C.structuralMap U.structuralMap ≫ u.hom := by
  sorry

/- A proper, flat, finitely presented relative curve.  The relative-curve
   class from Chapter 1 is the single source of these hypotheses, including
   geometric pure dimension one. -/
structure Chapter15RelativeCurve (S : Scheme.{u}) where
  curve : RelativeScheme S
  relativeCurve : Chapter01RelativeCurve curve.structuralMap

abbrev Chapter15RelativeCurveMap {S : Scheme.{u}}
    (C : Chapter15RelativeCurve S) : C.curve.carrier ⟶ S :=
  C.curve.structuralMap

structure Chapter15ProjectiveFlatRelativeCurve (S : Scheme.{u})
    extends Chapter15RelativeCurve S where
  projective : Chapter09ProjectiveMorphism
    toChapter15RelativeCurve.curve.structuralMap
  baseNoetherian : IsNoetherian S

abbrev Chapter15ProjectiveFlatRelativeCurveMap {S : Scheme.{u}}
    (C : Chapter15ProjectiveFlatRelativeCurve S) : C.curve.carrier ⟶ S :=
  C.curve.structuralMap

/- This record is the precise field-level package used for the smooth
   symmetric-power statements.  `smoothCurve` is the canonical Book 8 class
   which also supplies quasi-projectivity for the universal-divisor theorem. -/
structure Chapter15SmoothProjectiveRelativeCurve (S : Scheme.{u})
    extends Chapter15ProjectiveFlatRelativeCurve S where
  smoothCurve : Chapter11SmoothQuasiProjectiveCurve toChapter15ProjectiveFlatRelativeCurve.curve

instance chapter15SmoothProjectiveRelativeCurve_smoothQuasiProjective
    {S : Scheme.{u}} (C : Chapter15SmoothProjectiveRelativeCurve S) :
    Chapter11SmoothQuasiProjectiveCurve C.curve :=
  C.smoothCurve

structure Chapter15ProperSmoothIntegralCurve (k : Type u) [Field k] where
  curve : RelativeScheme (chapter15FieldBase k)
  proper : IsProper curve.structuralMap
  quasiCompact : QuasiCompact curve.structuralMap
  finiteType : LocallyOfFiniteType curve.structuralMap
  smooth : SmoothOfRelativeDimension 1 curve.structuralMap
  smoothQuasiProjective : Chapter11SmoothQuasiProjectiveCurve curve
  integral : IsIntegral curve.carrier
  irreducible : IrreducibleSpace (curve.carrier : Type u)
  geometricallyConnected : GeometricallyConnected curve.structuralMap
  genus : ℕ

instance chapter15ProperSmoothIntegralCurve_irreducible
    {k : Type u} [Field k] (C : Chapter15ProperSmoothIntegralCurve k) :
    IrreducibleSpace (C.curve.carrier : Type u) :=
  C.irreducible

instance chapter15ProperSmoothIntegralCurve_smoothQuasiProjective
    {k : Type u} [Field k] (C : Chapter15ProperSmoothIntegralCurve k) :
    Chapter11SmoothQuasiProjectiveCurve C.curve :=
  C.smoothQuasiProjective

structure Chapter15RationalPointData
    {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) where
  point : RelativeScheme.Hom (RelativeScheme.base (chapter15FieldBase k)) C.curve

abbrev Chapter15FieldDivisor {k : Type u} [Field k]
    (C : Chapter15ProperSmoothIntegralCurve k) (d : ℕ) :=
  Chapter15RelativeEffectiveCartierDivisor C.curve
    (RelativeScheme.base (chapter15FieldBase k)) d

def chapter15DualNumberBase (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (DualNumber k))

def chapter15DualNumberResidueMap (k : Type u) [Field k] :
    DualNumber k →+* k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom

def chapter15DualNumberResiduePoint (k : Type u) [Field k] :
    Spec (.of k) ⟶ chapter15DualNumberBase k :=
  Scheme.Spec.map (CommRingCat.ofHom (chapter15DualNumberResidueMap k)).op

/- A locally constant numerical function on the underlying point set of a
   scheme. -/
def Chapter15LocallyConstant {α β : Type*} [TopologicalSpace α]
    (g : α → β) : Prop :=
  ∀ x, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, g y = g x

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter15
