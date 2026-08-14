import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Polynomial.Quotient
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section03DivisorsOnSmoothRelativeCurves
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section05SymmetricPowersAndBaseChange

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme
open scoped BigOperators Polynomial

universe u v

/-!
Shared interfaces for Chapter 6.

The finite-flat and Cartier predicates are the canonical Book 8 predicates.
The records below only package the relative test-scheme notation needed by
the present chapter, so that the statements about Hilbert points and Cartier
points have the same domain and codomain.
-/

abbrev Chapter06ClosedSubscheme (X : Scheme) := X.IdealSheafData

abbrev Chapter06FiniteFlatRank {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) : Prop :=
  Chapter11FiniteLocallyFreeOfRank q d

abbrev Chapter06FiniteFlatMorphism {X Y : Scheme} (q : X ⟶ Y) : Prop :=
  IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q

abbrev Chapter06RelativeEffectiveDivisor {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) :=
  RelativeEffectiveCartierDivisor C T d

abbrev Chapter06RelativeDivisorAmbient {S : Scheme.{u}}
    (C T : RelativeScheme S) : Scheme.{u} :=
  pullback C.structuralMap T.structuralMap

abbrev Chapter06RelativeDivisorSubscheme {S : Scheme.{u}}
    {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) : Scheme.{u} :=
  D.divisor.subscheme

abbrev Chapter06RelativeDivisorInclusion {S : Scheme.{u}}
    {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeDivisorSubscheme D ⟶ Chapter06RelativeDivisorAmbient C T :=
  D.divisor.inclusion

def chapter06RelativeDivisorProjection {S : Scheme.{u}}
    {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeDivisorSubscheme D ⟶ T.carrier :=
  D.divisor.inclusion ≫ pullback.snd C.structuralMap T.structuralMap

theorem chapter06_relativeEffectiveDivisor_rank
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) (t : T.carrier) :
    Scheme.Hom.finrank (chapter06RelativeDivisorProjection D) t = d := by
  exact D.finite_flat_rank.2.2.2 t

theorem chapter06_finiteFlatMorphism_rank_is_locally_constant
    {X Y : Scheme.{u}} {q : X ⟶ Y}
    (h : Chapter06FiniteFlatMorphism q) :
    IsLocallyConstant (Scheme.Hom.finrank q) := by
  exact @Scheme.Hom.isLocallyConstant_finrank _ _ q h.2.1 h.1 h.2.2

theorem chapter06_finiteFlatRank_is_locally_constant
    {X Y : Scheme.{u}} {q : X ⟶ Y} {d : ℕ}
    (h : Chapter06FiniteFlatRank q d) :
    IsLocallyConstant (Scheme.Hom.finrank q) := by
  exact chapter06_finiteFlatMorphism_rank_is_locally_constant
    ⟨h.1, h.2.1, h.2.2.1⟩

theorem chapter06_finiteFlatMorphism_rank_constant_on_connected_base
    {X Y : Scheme.{u}} {q : X ⟶ Y}
    (h : Chapter06FiniteFlatMorphism q)
    (hconnected : _root_.IsConnected (Set.univ : Set Y)) :
    ∀ y z : Y, Scheme.Hom.finrank q y = Scheme.Hom.finrank q z := by
  sorry

/- The length family is deliberately recorded before Cartierness.  This is
the Hilbert-side object to which the smooth-curve theorem adds one equation. -/
structure Chapter06FiniteFlatClosedFamily {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) where
  ideal : (chapter06RelativeDivisorAmbient C T).IdealSheafData
  finite_flat_rank :
    Chapter06FiniteFlatRank
      (ideal.subschemeι ≫ pullback.snd C.structuralMap T.structuralMap) d

abbrev Chapter06FiniteFlatClosedFamily.subscheme
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) : Scheme.{u} :=
  Z.ideal.subscheme

def chapter06FiniteFlatClosedFamilyProjection
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Z.subscheme ⟶ T.carrier :=
  Z.ideal.subschemeι ≫ pullback.snd C.structuralMap T.structuralMap

theorem chapter06_finiteFlatClosedFamily_rank
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) (t : T.carrier) :
    Scheme.Hom.finrank (chapter06FiniteFlatClosedFamilyProjection Z) t = d := by
  exact Z.finite_flat_rank.2.2.2 t

@[ext]
theorem chapter06FiniteFlatClosedFamily_ext
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z W : Chapter06FiniteFlatClosedFamily C T d)
    (h : Z.ideal = W.ideal) : Z = W := by
  cases Z
  cases W
  cases h
  rfl

def chapter06IsEffectiveCartierFamily
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) : Prop :=
  Z.ideal.IsEffectiveCartier

/-!
The source uses "smooth projective relative curve".  Book 8's symmetric
power API consumes the canonical quasi-projective/smooth class; projectivity
is retained as an additional field rather than weakened in the Chapter 6
statement.
-/
class Chapter06SmoothProjectiveRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S)
    extends Chapter11SmoothQuasiProjectiveCurve C where
  projective :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09ProjectiveMorphism
      C.structuralMap

instance chapter06SmoothProjectiveRelativeCurve_to_chapter10
    {S : Scheme.{u}} {C : RelativeScheme S}
    [Chapter06SmoothProjectiveRelativeCurve C] :
    Chapter10SmoothRelativeCurve C.structuralMap :=
  Chapter11SmoothQuasiProjectiveCurve.smooth (C := C)

/-!
The pinned Book 8 API exposes the Cartier line-bundle construction through
an explicit local interface.  This profile keeps the line bundle, its
canonical section, its vanishing ideal, and the already canonical fiber-rank
statement together.  The existence theorem in §6.1 is the bridge to the
earlier divisor/Picard chapters.
-/

abbrev Chapter06LineBundle (X : Scheme.{u}) := Chapter10LineBundle X

abbrev Chapter06LineBundleSection {X : Scheme.{u}}
    (L : Chapter06LineBundle X) := Chapter10LineBundleSection L

structure Chapter06AssociatedLineBundleProfile
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) where
  lineBundle : Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T)
  canonicalSection : Chapter06LineBundleSection lineBundle
  vanishingIdeal : Chapter06ClosedSubscheme (Chapter06RelativeDivisorAmbient C T)
  canonicalSection_vanishingIdeal : vanishingIdeal = D.divisor.ideal
  fiberwise_degree : ∀ t : T.carrier,
    Scheme.Hom.finrank (chapter06RelativeDivisorProjection D) t = d

/-!
The following two records describe the parameter-space language used in
§6.4 without choosing a second Hilbert-scheme implementation.  A Hilbert
space represents all finite-flat families; its Cartier locus is represented
by an open immersion and the displayed subtype.
-/

structure Chapter06LengthDHilbertSpaceData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) where
  carrier : RelativeScheme S
  represents : ∀ T : RelativeScheme S,
    (T ⟶ carrier) ≃ Chapter06FiniteFlatClosedFamily C T d

structure Chapter06CartierDivisorOpenLocusData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d) where
  locus : RelativeScheme S
  inclusion : locus ⟶ H.carrier
  isOpen : IsOpenImmersion inclusion.hom
  represents : ∀ T : RelativeScheme S,
    (T ⟶ locus) ≃
      {Z : Chapter06FiniteFlatClosedFamily C T d //
        chapter06IsEffectiveCartierFamily Z}
  inclusion_compatibility : ∀ (T : RelativeScheme S) (f : T ⟶ locus),
    H.represents T (f ≫ inclusion) = (represents T f).1

/- LOCAL_DEPENDENCY_GUESS (6.4): Mathlib and the earlier LastLib chapters do
not expose a single canonical predicate for geometrically reduced fibers with
ordinary double points.  Keep those two geometric hypotheses as named fields
until the nodal-curve interface is available. -/
structure Chapter06NodalRelativeCurveData {S : Scheme.{u}}
    (C : RelativeScheme S) where
  proper : IsProper C.structuralMap
  flat : Flat C.structuralMap
  finite_presentation : LocallyOfFinitePresentation C.structuralMap
  separated : IsSeparated C.structuralMap
  geometrically_reduced_fibers : Prop
  ordinary_double_points : Prop

abbrev Chapter06NodalRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S) : Prop :=
  Nonempty (Chapter06NodalRelativeCurveData C)

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
