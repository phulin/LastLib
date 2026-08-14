import Mathlib.FieldTheory.IsAlgClosed.Basic

import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section03NormalizedBlowups
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05.Section02ExceptionalCurveAndItsNormalBundle

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u v

/-! ### 5.3 Numerical recognition of inverse point blowups -/

structure Chapter05InversePointBlowup {X Y : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    (P : Chapter05RegularPoint X) where
  contraction : Y ⟶ X
  target_regular : Chapter05RegularNoetherianSurface Y
  blowup : Chapter05PointBlowupConstruction P
  identification : Y ≅ blowup.carrier
  identification_over_X : identification.hom ≫ blowup.projection = contraction

def chapter05InversePointBlowupSignature
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map] : Prop :=
  Nonempty
      { e : E.carrier ≅ chapter05ProjectiveLine (X.residueField P.point) //
        e.hom ≫
            chapter02ProjectiveSpaceProjection
              (AlgebraicGeometry.Spec (.of (X.residueField P.point))) 1 =
          E.structure_map } ∧
    chapter05LineBundleIsomorphic N.normal_bundle N.tautological_minus_one ∧
    chapter05Degree (k := ↑(X.residueField P.point))
      (f := E.structure_map) N.normal_bundle = -1

theorem chapter05_inverse_point_blowup_has_signature
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map]
    (hdegree :
      chapter05Degree (k := ↑(X.residueField P.point))
          (f := E.structure_map) N.tautological_minus_one = -1) :
    chapter05InversePointBlowupSignature E N := by
  refine ⟨⟨E.projective_line_iso, E.projective_line_iso_over_base⟩,
    chapter05_exceptional_normal_bundle_is_O_minus_one N, ?_⟩
  exact chapter05_exceptional_selfIntersection_eq_neg_one_over_center_field N hdegree

def chapter05AlgebraicallyClosedExceptionalSignature
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map] : Prop :=
  Nonempty
      { e : E.carrier ≅ chapter05ProjectiveLine (X.residueField P.point) //
        e.hom ≫
            chapter02ProjectiveSpaceProjection
              (AlgebraicGeometry.Spec (.of (X.residueField P.point))) 1 =
          E.structure_map } ∧
    chapter05Degree (k := ↑(X.residueField P.point))
      (f := E.structure_map) N.normal_bundle = -1

theorem chapter05_algebraically_closed_exceptional_signature
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [IsAlgClosed (X.residueField P.point)]
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map]
    (hdegree :
      chapter05Degree (k := ↑(X.residueField P.point))
          (f := E.structure_map) N.tautological_minus_one = -1) :
    chapter05AlgebraicallyClosedExceptionalSignature E N := by
  exact ⟨⟨E.projective_line_iso, E.projective_line_iso_over_base⟩,
    chapter05_exceptional_selfIntersection_eq_neg_one_over_center_field N hdegree⟩

/-!
The form of the exceptional curve and the normal line bundle are retained in the signature.  The
definition does not replace them by a bare integer when the residue field is not algebraically
closed.
-/

def chapter05NonclosedExceptionalSignature
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map] : Prop :=
  ¬ IsAlgClosed (X.residueField P.point) ∧
    Nonempty
      { e : E.carrier ≅ chapter05ProjectiveLine (X.residueField P.point) //
        e.hom ≫
            chapter02ProjectiveSpaceProjection
              (AlgebraicGeometry.Spec (.of (X.residueField P.point))) 1 =
          E.structure_map } ∧
    chapter05LineBundleIsomorphic N.normal_bundle N.tautological_minus_one ∧
    chapter05Degree (k := ↑(X.residueField P.point))
      (f := E.structure_map) N.normal_bundle = -1

theorem chapter05_nonclosed_exceptional_signature
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map]
    (hnot : ¬ IsAlgClosed (X.residueField P.point))
    (hdegree :
      chapter05Degree (k := ↑(X.residueField P.point))
          (f := E.structure_map) N.tautological_minus_one = -1) :
    chapter05NonclosedExceptionalSignature E N := by
  exact ⟨hnot, chapter05_inverse_point_blowup_has_signature E N hdegree⟩

structure Chapter05ConstantFieldProjectiveLineSignature
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Module.Finite k L] where
  carrier : Scheme.{u}
  structure_map : carrier ⟶ AlgebraicGeometry.Spec (.of k)
  proper : IsProper structure_map
  curve_iso : carrier ≅ chapter05ProjectiveLine L
  curve_iso_over_base :
    curve_iso.hom ≫
        chapter02ProjectiveSpaceProjection (AlgebraicGeometry.Spec (.of L)) 1 ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap k L)).op = structure_map
  normal_bundle : Chapter05LineBundle carrier
  tautological_minus_one : Chapter05LineBundle carrier
  normal_bundle_is_minus_one :
    chapter05LineBundleIsomorphic normal_bundle tautological_minus_one
  self_intersection : ℤ
  self_intersection_eq_neg_finrank :
    self_intersection = -(Module.finrank k L : ℤ)

theorem chapter05_constant_field_selfIntersection_formula
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (C : Chapter05ConstantFieldProjectiveLineSignature k L) :
    C.self_intersection = -(Module.finrank k L : ℤ) :=
  C.self_intersection_eq_neg_finrank

theorem chapter05_constant_field_degree_is_residue_degree
    {X S : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [Chapter05ArithmeticSurface X S f]
    (p : Chapter05PointOverBase f)
    {L : Type u} [Field L]
    [Algebra (S.residueField (f p.point.point)) L]
    [Module.Finite (S.residueField (f p.point.point)) L]
    (hfin : Module.finrank (S.residueField (f p.point.point)) L =
      chapter05ResidueDegree p) :
    -(Module.finrank (S.residueField (f p.point.point)) L : ℤ) =
      -(chapter05ResidueDegree p : ℤ) := by
  rw [hfin]

/-! ### Negative self-intersection is not a converse criterion -/

theorem chapter05_minus_two_curve_is_not_a_point_blowup_signature
    {k : Type u} [Field k]
    (C : Chapter05CurveNumericalData k)
    (hC : C.selfIntersection = -2) :
    ¬ chapter05PointBlowupNumericalSignature C := by
  sorry

theorem chapter05_positive_genus_curve_is_not_a_point_blowup_signature
    {k : Type u} [Field k]
    (C : Chapter05CurveNumericalData k)
    (hgenus : 0 < C.genus) :
    ¬ chapter05PointBlowupNumericalSignature C := by
  intro h
  exact (Nat.ne_of_gt hgenus) h.1

structure Chapter05CurveGeometricSignature
    {k : Type u} [Field k] (C : Chapter05CurveNumericalData k) where
  projective_line : C.carrier ≅ chapter05ProjectiveLine k
  projective_line_over_base :
    projective_line.hom ≫ chapter02ProjectiveSpaceProjection
        (AlgebraicGeometry.Spec (.of k)) 1 = C.structureMap
  normal_bundle : Chapter05LineBundle C.carrier
  tautological_minus_one : Chapter05LineBundle C.carrier
  normal_bundle_is_minus_one :
    chapter05LineBundleIsomorphic normal_bundle tautological_minus_one

def Chapter05RecognitionDataNeedsGeometry
    {k : Type u} [Field k] (C : Chapter05CurveNumericalData k) : Prop :=
  chapter05PointBlowupNumericalSignature C ∧
    Nonempty (Chapter05CurveGeometricSignature C)

/-!
`Chapter05RecognitionDataNeedsGeometry` is deliberately a data requirement, not a converse
theorem: a negative square does not construct an inverse morphism.  The next structure records
the separate situation in which a regular point-blowup sequence and inverse maps have already
been supplied.
-/

structure Chapter05PointBlowupSequence where
  length : ℕ
  surface : ℕ → Scheme.{u}
  map : ∀ i, i < length → (surface (i + 1) ⟶ surface i)
  regular_surface : ∀ i, Chapter05RegularNoetherianSurface (surface i)
  center : ∀ i (_hi : i < length),
    @Chapter05RegularPoint (surface i) (regular_surface i)
  step_is_regular_point_blowup : ∀ i (hi : i < length),
    @Chapter05PointBlowupConstruction (surface i) (regular_surface i) (center i hi)
  step_target_identification : ∀ i (hi : i < length),
    surface (i + 1) ≅ (step_is_regular_point_blowup i hi).carrier
  step_map_is_blowup : ∀ i (hi : i < length),
    (step_target_identification i hi).hom ≫
        (step_is_regular_point_blowup i hi).projection = map i hi

def chapter05PointBlowupSequenceCompositeMap
    (S : Chapter05PointBlowupSequence) :
    ∀ n, n ≤ S.length → (S.surface n ⟶ S.surface 0)
  | 0, _ => 𝟙 _
  | n + 1, h =>
      S.map n (Nat.lt_of_succ_le h) ≫
        chapter05PointBlowupSequenceCompositeMap S n
          (Nat.le_of_lt (Nat.lt_of_succ_le h))

structure Chapter05SuppliedPointBlowupSequence where
  sequence : Chapter05PointBlowupSequence
  inverse_morphism : ∀ i (hi : i < sequence.length),
    letI : Chapter05RegularNoetherianSurface (sequence.surface i) :=
      sequence.regular_surface i
    (sequence.step_is_regular_point_blowup i hi).carrier ⟶ sequence.surface i
  inverse_is_blowup_projection : ∀ i (hi : i < sequence.length),
    letI : Chapter05RegularNoetherianSurface (sequence.surface i) :=
      sequence.regular_surface i
    inverse_morphism i hi = (sequence.step_is_regular_point_blowup i hi).projection
  all_intermediate_surfaces_regular :
    ∀ i, Chapter05RegularNoetherianSurface (sequence.surface i)

theorem chapter05_supplied_sequence_reduces_to_one_step_api
    (S : Chapter05SuppliedPointBlowupSequence) :
    ∀ i (hi : i < S.sequence.length),
      Nonempty
        (@Chapter05PointBlowupConstruction (S.sequence.surface i)
          (S.sequence.regular_surface i) (S.sequence.center i hi)) := by
  sorry

/-! ### Normalized common dominations are kept separate from point-blowup sequences -/

/- LOCAL_DEPENDENCY_GUESS: the earlier intersection-pairing and projection-formula API is not
available in the assigned tree, so this interface records the regular domination maps and leaves
their numerical comparison to that later API. -/
structure Chapter05NormalizedBlowupDomination where
  source : Scheme.{u}
  normalized_blowup : Scheme.{u}
  final_regular_domination : Scheme.{u}
  source_is_normal_integral :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07NormalIntegralScheme
      source
  normalized_blowup_ideal :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07CoherentIdeal
      source
  normalized_blowup_data :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07NormalizedBlowup
      normalized_blowup_ideal source_is_normal_integral
  normalized_blowup_identification :
    normalized_blowup ≅ normalized_blowup_data.carrier
  source_map : normalized_blowup ⟶ source
  normalized_blowup_map_identification :
    normalized_blowup_identification.hom ≫
        LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.chapter07NormalizedBlowupMap
          normalized_blowup_data =
      source_map
  regular_map : final_regular_domination ⟶ normalized_blowup
  normalized_is_normal :
    LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Chapter07NormalIntegralScheme
      normalized_blowup
  source_map_is_projective : Chapter05ProjectiveMorphism source_map
  source_map_is_birational : Scheme.Birational normalized_blowup source
  regular_map_is_projective : Chapter05ProjectiveMorphism regular_map
  regular_map_is_birational :
    Scheme.Birational final_regular_domination normalized_blowup
  final_surface_regular :
    Chapter05RegularNoetherianSurface final_regular_domination

def Chapter05IsPresentedAsRegularPointBlowups
    (D : Chapter05NormalizedBlowupDomination) : Prop :=
  ∃ S : Chapter05SuppliedPointBlowupSequence,
    ∃ e₀ : S.sequence.surface 0 ≅ D.normalized_blowup,
      ∃ eₗ : S.sequence.surface S.sequence.length ≅ D.final_regular_domination,
        eₗ.hom ≫ D.regular_map =
          chapter05PointBlowupSequenceCompositeMap S.sequence S.sequence.length
            (Nat.le_refl _) ≫ e₀.hom

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05
