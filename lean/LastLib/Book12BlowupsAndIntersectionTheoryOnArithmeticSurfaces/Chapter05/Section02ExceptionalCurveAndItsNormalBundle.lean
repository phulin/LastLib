import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05.Section01RegularityOfTheNewSurface

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/-! ### 5.2 The exceptional curve and its normal bundle -/

def chapter05ExceptionalBaseMap
    {X S : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [Chapter05ArithmeticSurface X S f]
    (p : Chapter05PointOverBase f)
    (B : Chapter05PointBlowupConstruction p.point)
    (E : Chapter05ExceptionalDivisor B) :
    E.carrier ⟶ AlgebraicGeometry.Spec (S.residueField (f p.point.point)) :=
  E.structure_map ≫ Scheme.Spec.map (f.residueFieldMap p.point.point)

/- LOCAL_DEPENDENCY_GUESS: the normal line bundle and the restrictions of the exceptional Cartier
divisor are not currently bundled by Mathlib's closed-immersion API. -/
structure Chapter05ExceptionalNormalData
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    (B : Chapter05PointBlowupConstruction P)
    (E : Chapter05ExceptionalDivisor B) where
  normal_bundle : Chapter05LineBundle E.carrier
  conormal_bundle : Chapter05LineBundle E.carrier
  restriction_of_exceptional_divisor : Chapter05LineBundle E.carrier
  restriction_of_negative_exceptional_divisor : Chapter05LineBundle E.carrier
  tautological_one : Chapter05LineBundle E.carrier
  tautological_minus_one : Chapter05LineBundle E.carrier

theorem chapter05_exceptional_normal_bundle_is_restriction
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E) :
    chapter05LineBundleIsomorphic N.normal_bundle
      N.restriction_of_exceptional_divisor := by
  sorry

theorem chapter05_exceptional_conormal_bundle_is_negative_restriction
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E) :
    chapter05LineBundleIsomorphic N.conormal_bundle
      N.restriction_of_negative_exceptional_divisor := by
  sorry

theorem chapter05_exceptional_restriction_is_O_minus_one
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E) :
    chapter05LineBundleIsomorphic N.restriction_of_exceptional_divisor
      N.tautological_minus_one := by
  sorry

theorem chapter05_negative_exceptional_restriction_is_O_one
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E) :
    chapter05LineBundleIsomorphic N.restriction_of_negative_exceptional_divisor
      N.tautological_one := by
  sorry

theorem chapter05_exceptional_normal_bundle_is_O_minus_one
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E) :
    chapter05LineBundleIsomorphic N.normal_bundle N.tautological_minus_one := by
  exact chapter05_lineBundleIsomorphic_trans
    (chapter05_exceptional_normal_bundle_is_restriction N)
    (chapter05_exceptional_restriction_is_O_minus_one N)

theorem chapter05_exceptional_conormal_bundle_is_O_one
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E) :
    chapter05LineBundleIsomorphic N.conormal_bundle N.tautological_one := by
  exact chapter05_lineBundleIsomorphic_trans
    (chapter05_exceptional_conormal_bundle_is_negative_restriction N)
    (chapter05_negative_exceptional_restriction_is_O_one N)

/- LOCAL_DEPENDENCY_GUESS: existence of the normal-bundle package is the missing effective-Cartier
restriction bridge; it is independent of the numerical degree theorem below. -/
theorem chapter05_exceptional_normal_data_exists
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    (B : Chapter05PointBlowupConstruction P)
    (E : Chapter05ExceptionalDivisor B) :
    Nonempty (Chapter05ExceptionalNormalData B E) := by
  sorry

noncomputable def chapter05ExceptionalNormalData
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    (B : Chapter05PointBlowupConstruction P)
    (E : Chapter05ExceptionalDivisor B) :
    Chapter05ExceptionalNormalData B E :=
  Classical.choice (chapter05_exceptional_normal_data_exists B E)

theorem chapter05_exceptional_normal_degree_over_base
    {X S : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [Chapter05ArithmeticSurface X S f]
    (p : Chapter05PointOverBase f)
    (B : Chapter05PointBlowupConstruction p.point)
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (S.residueField (f p.point.point))
      (chapter05ExceptionalBaseMap p B E)] :
    chapter05Degree (f := chapter05ExceptionalBaseMap p B E) N.normal_bundle =
      -(chapter05ResidueDegree p : ℤ) := by
  sorry

def chapter05ExceptionalSelfIntersection
    {X S : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [Chapter05ArithmeticSurface X S f]
    (p : Chapter05PointOverBase f)
    (B : Chapter05PointBlowupConstruction p.point)
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (S.residueField (f p.point.point))
      (chapter05ExceptionalBaseMap p B E)] : ℤ :=
  chapter05Degree (f := chapter05ExceptionalBaseMap p B E) N.normal_bundle

/-- The arithmetic-surface self-intersection formula for the exceptional curve. -/
theorem chapter05_exceptional_selfIntersection_formula
    {X S : Scheme.{u}}
    [Chapter05RegularNoetherianSurface X]
    {f : X ⟶ S} [Chapter05ArithmeticSurface X S f]
    (p : Chapter05PointOverBase f)
    (B : Chapter05PointBlowupConstruction p.point)
    (E : Chapter05ExceptionalDivisor B)
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (S.residueField (f p.point.point))
      (chapter05ExceptionalBaseMap p B E)] :
    chapter05ExceptionalSelfIntersection p B E N =
      -(chapter05ResidueDegree p : ℤ) := by
  exact chapter05_exceptional_normal_degree_over_base p B E N

theorem chapter05_exceptional_selfIntersection_eq_neg_one_over_center_field
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05CurveDegreeTheory E.carrier (X.residueField P.point)
      E.structure_map] :
    chapter05Degree (f := E.structure_map) N.normal_bundle = -1 := by
  sorry

theorem chapter05_exceptional_h0_of_O_minus_one
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05GlobalSectionsTheory E.carrier (X.residueField P.point)
      E.structure_map] :
    chapter05H0Finrank (f := E.structure_map) N.tautological_minus_one = 0 := by
  sorry

theorem chapter05_exceptional_normal_bundle_has_no_infinitesimal_deformations
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05GlobalSectionsTheory E.carrier (X.residueField P.point)
      E.structure_map] :
    chapter05H0Finrank (f := E.structure_map) N.normal_bundle = 0 := by
  sorry

def Chapter05InfinitesimalDeformationSpace
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    [Chapter05GlobalSectionsTheory E.carrier (X.residueField P.point)
      E.structure_map] : ℕ :=
  chapter05H0Finrank (f := E.structure_map)
    (chapter05ExceptionalNormalData B E).normal_bundle

theorem chapter05_exceptional_curve_is_rigid
    {X : Scheme.{u}} [Chapter05RegularNoetherianSurface X]
    {P : Chapter05RegularPoint X}
    {B : Chapter05PointBlowupConstruction P}
    {E : Chapter05ExceptionalDivisor B}
    (N : Chapter05ExceptionalNormalData B E)
    [Chapter05GlobalSectionsTheory E.carrier (X.residueField P.point)
      E.structure_map] :
    chapter05H0Finrank (f := E.structure_map) N.normal_bundle = 0 :=
  chapter05_exceptional_normal_bundle_has_no_infinitesimal_deformations N

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter05
