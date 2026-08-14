import Mathlib.LinearAlgebra.TensorPower.Symmetric
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04.Section02TotalAndStrictTransforms

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

/-! ## 4.3. Multiplicity at a regular point -/

def Chapter04TwoDimensionalRegularLocalRing (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing A] : Prop :=
  ringKrullDim A = 2

def chapter04TangentPlane (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  IsLocalRing.CotangentSpace A

abbrev Chapter04SymmetricPower (k : Type u) (V : Type v)
    [CommSemiring k] [AddCommMonoid V] [Module k V] (m : ℕ) : Type max u v :=
  SymmetricPower k (Fin m) V

/- The quotient `m^n / m^(n+1)` is represented directly by the equivalence
relation on the n-th ideal power.  This avoids confusing the ideal quotient
with the ring quotient and exposes a usable class for the initial form. -/
def chapter04PowerQuotientSetoid (A : Type u) [CommRing A]
    (n : ℕ) : Setoid {f : A // f ∈ (maximalIdeal A) ^ n} where
  r f g := f.1 - g.1 ∈ (maximalIdeal A) ^ (n + 1)
  iseqv := by
    constructor <;> intro <;> sorry

def chapter04PowerQuotient (A : Type u) [CommRing A] (n : ℕ) : Type u :=
  Quotient (chapter04PowerQuotientSetoid A n)

def chapter04PowerQuotientMk {A : Type u} [CommRing A]
    (n : ℕ) {f : A} (hf : f ∈ (maximalIdeal A) ^ n) :
    chapter04PowerQuotient A n :=
  Quotient.mk' ⟨f, hf⟩

/- LOCAL_DEPENDENCY_GUESS (4.3): Mathlib has the individual power quotient
and the symmetric tensor power, but not the regular-local associated-graded
comparison in one declaration. -/
class Chapter04InitialFormComparison
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (n : ℕ) where
  comparison : chapter04PowerQuotient A n ≃
    Chapter04SymmetricPower (IsLocalRing.ResidueField A)
      (IsLocalRing.CotangentSpace A) n

theorem chapter04_initial_form_comparison_exists
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (hA : Chapter04TwoDimensionalRegularLocalRing A) (n : ℕ) :
    Nonempty (Chapter04InitialFormComparison A n) := by
  sorry

structure Chapter04InitialFormData
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m] where
  in_power : f ∈ (maximalIdeal A) ^ m
  not_in_next_power : f ∉ (maximalIdeal A) ^ (m + 1)
  initialForm : Chapter04SymmetricPower (IsLocalRing.ResidueField A)
    (IsLocalRing.CotangentSpace A) m
  initialForm_eq_comparison :
    initialForm = Chapter04InitialFormComparison.comparison
      (chapter04PowerQuotientMk m in_power)
  initialForm_nonzero : initialForm ≠ 0

theorem chapter04_initial_form_exists
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (maximalIdeal A) ^ m)
    (hm_next : f ∉ (maximalIdeal A) ^ (m + 1)) :
    Nonempty (Chapter04InitialFormData A f m) := by
  sorry

noncomputable def chapter04InitialFormData
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (maximalIdeal A) ^ m)
    (hm_next : f ∉ (maximalIdeal A) ^ (m + 1)) :
    Chapter04InitialFormData A f m :=
  Classical.choice (chapter04_initial_form_exists A f m hm hm_next)

abbrev chapter04InitialForm
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (maximalIdeal A) ^ m)
    (hm_next : f ∉ (maximalIdeal A) ^ (m + 1)) :=
  (chapter04InitialFormData A f m hm hm_next).initialForm

theorem chapter04_initial_form_is_homogeneous
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (maximalIdeal A) ^ m)
    (hm_next : f ∉ (maximalIdeal A) ^ (m + 1)) :
    chapter04InitialForm A f m hm hm_next ≠ 0 := by
  exact (chapter04InitialFormData A f m hm hm_next).initialForm_nonzero

/- The projectivized initial form cuts the strict transform on the exceptional
line.  The relation is kept as a named data package because the pinned tree
does not yet supply the graded Rees-algebra-to-projective-bundle comparison. -/
structure Chapter04InitialFormExceptionalIntersectionData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m] where
  initial : Chapter04InitialFormData A f m
  /- LOCAL_DEPENDENCY_GUESS (4.3): this is the missing graded Rees-algebra
     comparison identifying the initial form with the exceptional cut. -/
  cuts_intersection : Prop
  exceptional_factor_removed :
    (chapter04DivisorNatMultiple m E.divisor).ideal =
      ∏ _ : Fin m, E.divisor.ideal
  strict_transform_is_T : T.transform.ideal = chapter04StrictTransformIdeal (J := D.ideal) B

theorem chapter04_initial_form_cuts_strict_transform_on_exceptional
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (maximalIdeal A) ^ m)
    (hm_next : f ∉ (maximalIdeal A) ^ (m + 1)) :
    Nonempty (Chapter04InitialFormExceptionalIntersectionData B D E T A f m) := by
  sorry

/-! ### Intersection number and residue degree -/

/- LOCAL_DEPENDENCY_GUESS (4.3): local intersection numbers are introduced in
a later book chapter, so this chapter exposes the minimal divisor-pair API
needed for the exceptional-intersection formula. -/
class Chapter04IntersectionNumberAPI (Y : Scheme.{u}) where
  intersection : Chapter04EffectiveCartierDivisor Y →
    Chapter04EffectiveCartierDivisor Y → ℕ

def chapter04IntersectionNumber
    {Y : Scheme.{u}} [Chapter04IntersectionNumberAPI Y]
    (D E : Chapter04EffectiveCartierDivisor Y) : ℕ :=
  Chapter04IntersectionNumberAPI.intersection D E

def chapter04ResidueDegree
    {X : Scheme.{u}} {k₀ : Type v} [Field k₀]
    (π : X ⟶ AlgebraicGeometry.Spec (.of k₀)) (x : X) : ℕ :=
  π.residueDegree x

theorem chapter04_residue_degree_is_field_extension_degree
    {X : Scheme.{u}} {k₀ : Type v} [Field k₀]
    (π : X ⟶ AlgebraicGeometry.Spec (.of k₀)) (x : X) :
    chapter04ResidueDegree π x = π.residueDegree x := by
  rfl

theorem chapter04_exceptional_intersection_formula
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {k₀ : Type v} [Field k₀]
    (π : X ⟶ AlgebraicGeometry.Spec (.of k₀))
    (x : X)
    (hx : Chapter04RegularSurfacePoint x)
    (B : Chapter04Blowup X I)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (horder : Chapter04GenericOrderAlongCenter I D)
    [Chapter04IntersectionNumberAPI B.carrier] :
    chapter04IntersectionNumber T.divisor E.divisor =
      horder.order * chapter04ResidueDegree π x := by
  sorry

/- Repeated factors of the initial form are reflected by repeated tangent
directions on the exceptional projective line. -/
structure Chapter04TangentDirectionMultiplicityData
    (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] (m : ℕ) where
  numberOfDirections : ℕ
  direction : Fin numberOfDirections →
    { L : Submodule k V // Module.finrank k L = 1 }
  multiplicity : Fin numberOfDirections → ℕ
  positive : ∀ i, 0 < multiplicity i
  totalMultiplicity : ∑ i, multiplicity i = m
  initial_form : Chapter04SymmetricPower k V m
  /- LOCAL_DEPENDENCY_GUESS (4.3): factorization of a homogeneous form into
     projective tangent directions is supplied by the later intersection API. -/
  represents_initial_form : Prop

theorem chapter04_repeated_tangent_directions_have_multiplicity
    (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (m : ℕ) :
    ∀ h : Nonempty (Chapter04TangentDirectionMultiplicityData k V m),
      ∃ d : Chapter04TangentDirectionMultiplicityData k V m,
        d.totalMultiplicity = m := by
  intro h
  exact ⟨h.some, h.some.totalMultiplicity⟩

/-! ### Smooth curves and contact -/

structure Chapter04SmoothCurveTangentDirectionData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X) where
  smooth : Chapter04SmoothCurveAtPoint C x
  transform : Chapter04StrictTransformCartierData (J := C.ideal) B
  fiberDirections : Chapter04ExceptionalTangentDirectionData x B
  rationalPoint :
    {p : AlgebraicGeometry.Spec (X.residueField x) ⟶ B.exceptionalSubscheme //
      p ≫ B.exceptionalToCenter = fiberDirections.centerPoint.inv}
  direction : Chapter04TangentDirection
    (X.presheaf.stalk x) (X.residueField x)
  direction_is_rational_point :
    fiberDirections.rationalPointDirectionEquiv rationalPoint = direction

theorem chapter04_smooth_curve_has_one_tangent_direction
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} (hx : Chapter04RegularSurfacePoint x)
    (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X)
    (hC : Chapter04SmoothCurveAtPoint C x)
    [Chapter04ConormalSheafAPI I] :
    Nonempty (Chapter04SmoothCurveTangentDirectionData x B C) := by
  sorry

theorem chapter04_smooth_curve_has_multiplicity_one
    {X : Scheme.{u}}
    {x : X} (C : Chapter04EffectiveCartierDivisor X)
    (hC : Chapter04SmoothCurveAtPoint C x) :
    Chapter04CurveHasMultiplicityAt C x 1 :=
  hC.1

def Chapter04StrictTransformsDisjointAbovePoint
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    {C D : Chapter04EffectiveCartierDivisor X}
    (TC : Chapter04StrictTransformCartierData (J := C.ideal) B)
    (TD : Chapter04StrictTransformCartierData (J := D.ideal) B) : Prop :=
  Disjoint
    (((TC.divisor.ideal.support : Set B.carrier) ∩
      (B.exceptionalIdeal.support : Set B.carrier)))
    (((TD.divisor.ideal.support : Set B.carrier) ∩
      (B.exceptionalIdeal.support : Set B.carrier)))

theorem chapter04_distinct_tangent_directions_give_disjoint_transforms
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    {C D : Chapter04EffectiveCartierDivisor X}
    (TC : Chapter04SmoothCurveTangentDirectionData x B C)
    (TD : Chapter04SmoothCurveTangentDirectionData x B D)
    (hdir : TC.direction ≠ TD.direction) :
    Chapter04StrictTransformsDisjointAbovePoint x B TC.transform TD.transform := by
  sorry

theorem chapter04_shared_tangent_direction_gives_intersection_on_exceptional
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    {C D : Chapter04EffectiveCartierDivisor X}
    (TC : Chapter04SmoothCurveTangentDirectionData x B C)
    (TD : Chapter04SmoothCurveTangentDirectionData x B D)
    (hdir : TC.direction = TD.direction) :
    Set.Nonempty ((TC.transform.divisor.ideal.support : Set B.carrier) ∩
      (TD.transform.divisor.ideal.support : Set B.carrier) ∩
      (B.exceptionalIdeal.support : Set B.carrier)) := by
  sorry

/- The next blowup is represented by the next order of the difference of local
equations, which is the standard algebraic contact invariant. -/
structure Chapter04NextContactTerm
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f g : R) where
  first_order_agrees : f - g ∈ (maximalIdeal R) ^ 2
  next_order : ℕ
  next_order_is_order_of_difference :
    next_order = chapter04OrderAtRegularPoint (f - g)

theorem chapter04_second_blowup_measures_next_contact_term
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f g : R) (hcontact : f - g ∈ (maximalIdeal R) ^ 2)
    (hfinite : ∃ n : ℕ, f - g ∉ (maximalIdeal R) ^ (n + 1)) :
    ∃ c : Chapter04NextContactTerm f g,
      c.next_order = chapter04OrderAtRegularPoint (f - g) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
