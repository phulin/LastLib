import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Core

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

/-!
Shared interfaces for Chapter 4.

The pinned library has the stalkwise regular-local-ring and integrally-closed
predicates, localization dimension, normalization morphisms, and the
fiberwise smoothness machinery.  It does not expose a named depth/S2 package,
so depth is defined from regular sequences.  The preceding Book 11 Chapter 3
supplies the affine excellence predicate; the scheme-level profile below
packages those affine hypotheses for this chapter.
-/

/-- Regularity of a scheme in the stalkwise form used in this chapter. -/
def Chapter04RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- Normality of a locally noetherian integral scheme in stalkwise form. -/
def Chapter04NormalScheme (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Prop :=
  ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

theorem chapter04_regularScheme_iff_chapter03Regular (X : Scheme.{u}) :
    Chapter04RegularScheme X ↔ Chapter03Regular X := by
  constructor
  · intro h
    exact ⟨h⟩
  · intro h
    exact h.regular_stalk

theorem chapter04_normalScheme_iff_chapter03Normal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    Chapter04NormalScheme X ↔ Chapter03Normal X := by
  constructor
  · intro h
    exact ⟨h⟩
  · intro h
    exact h.integrallyClosed_stalk

/-- The scheme-theoretic nonregular locus. -/
def Chapter04NonRegularLocus (X : Scheme.{u}) : Set X :=
  {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}

theorem chapter04_mem_nonRegularLocus_iff {X : Scheme.{u}} {x : X} :
    x ∈ Chapter04NonRegularLocus X ↔
      ¬ IsRegularLocalRing (X.presheaf.stalk x) := by
  rfl

/-- A noetherian surface marker with the local codimension bound visible. -/
def Chapter04NoetherianSurface (X : Scheme.{u}) : Prop :=
  IsNoetherian X ∧ (∀ x : X, Order.coheight x ≤ 2) ∧
    ∃ x : X, Order.coheight x = 2

/-- The normality predicate for a noetherian ring, expressed locally. -/
def Chapter04NormalRing (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (p : Ideal A) (hp : p.IsPrime),
    letI := hp
    IsDomain (Localization.AtPrime p) ∧
      IsIntegrallyClosed (Localization.AtPrime p)

/-- The codimension-one regularity condition (R1). -/
def Chapter04R1 (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (p : Ideal A) (hp : p.IsPrime),
    p.height ≤ (1 : ℕ∞) →
      letI := hp
      IsRegularLocalRing (Localization.AtPrime p)

/- LOCAL_DEPENDENCY_GUESS: Mathlib does not currently expose depth as a named
invariant.  The following definition uses the canonical regular-sequence
description, so S2 remains an actual depth statement rather than an arbitrary
oracle supplied as extra data. -/
noncomputable def Chapter04Depth (R : Type u) [CommRing R] [IsLocalRing R] : WithBot ℕ∞ :=
  sSup {d : WithBot ℕ∞ |
    ∃ rs : List R,
      d = (rs.length : WithBot ℕ∞) ∧
        RingTheory.Sequence.IsRegular R rs ∧
          ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R}

/- The codimension-two depth condition (S2). -/
def Chapter04S2 (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (p : Ideal A) (hp : p.IsPrime),
    letI := hp
    Chapter04Depth (Localization.AtPrime p) ≥
      min (2 : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p))

/-- Membership in a height-one localization inside the fraction field. -/
def Chapter04MemHeightOneLocalization {A : Type u} [CommRing A] [IsDomain A]
    (x : FractionRing A) (p : Ideal A) (hp : p.IsPrime) : Prop :=
  letI := hp
  ∃ y : Localization.AtPrime p,
    algebraMap (Localization.AtPrime p) (FractionRing A) y = x

/-- The intersection statement used in the converse direction of Serre's criterion. -/
def Chapter04HeightOneIntersection (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] : Prop :=
  ∀ x : FractionRing A,
    (∃ a : A, algebraMap A (FractionRing A) a = x) ↔
      ∀ (p : Ideal A) (hp : p.IsPrime),
        p.height = 1 → Chapter04MemHeightOneLocalization x p hp

/- The preceding chapter supplies the affine excellence predicate, but not a
   scheme-level class.  Keep the scheme interface tied to those actual affine
   hypotheses rather than making closedness of the singular locus an input. -/
class Chapter04ExcellenceProfile (X : Scheme.{u}) : Prop where
  noetherian : IsNoetherian X
  affine_excellent : ∀ U : X.affineOpens, Chapter03Excellent Γ(X, U)

theorem chapter04_excellenceProfile_of_excellentSurface
    (X : Scheme.{u}) (hX : Chapter03ExcellentSurface X) :
    Chapter04ExcellenceProfile X := by
  exact ⟨hX.2.1, hX.2.2.2⟩

/-- A positive-dimensional closed subset contained in the singular locus. -/
def Chapter04SingularCurve (X : Scheme.{u}) (C : Set X) : Prop :=
  C.Nonempty ∧ IsClosed C ∧ C ⊆ Chapter04NonRegularLocus X ∧
    1 ≤ topologicalKrullDim C

/-- The condition that the singular locus contains no curve. -/
def Chapter04SingularLocusContainsNoCurve (X : Scheme.{u}) : Prop :=
  ¬ ∃ C : Set X, Chapter04SingularCurve X C

/- Geometric regularity is a morphism property: every field-valued fiber is
   regular.  An object property alone would forget the base and would merely
   restate ordinary regularity. -/
abbrev Chapter04GeometricallyRegular : MorphismProperty Scheme :=
  geometrically Chapter04RegularScheme

/- The preceding Chapter 1 already fixes the pinned fiberwise interface (smoothness
   of each residue-field fiber).  Keep a Chapter 4 name as an alias instead of
   introducing a second, potentially non-equivalent notion. -/
abbrev Chapter04GeometricallyRegularFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01GeometricallyRegularFibers f

/-- The local algebraic smoothness predicate used for the node example. -/
def Chapter04AlgebraSmoothAt (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (p : Ideal A) (hp : p.IsPrime) : Prop :=
  letI := hp
  Algebra.IsSmoothAt R p

theorem chapter04_normalization_factorization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    f.toNormalization ≫ f.fromNormalization = f := by
  exact f.toNormalization_fromNormalization

theorem chapter04_normalization_fromNormalization_integral
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom f.fromNormalization := by
  infer_instance

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
