import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.RingTheory.Length
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04.Section02TotalAndStrictTransforms

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

/-! ## 4.3. Multiplicity at a regular point -/

def Chapter04TwoDimensionalRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] : Prop :=
  ringKrullDim A = 2

def chapter04TangentPlane (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  IsLocalRing.CotangentSpace A

abbrev Chapter04SymmetricPower (k : Type u) (V : Type v)
    [CommSemiring k] [AddCommMonoid V] [Module k V] (m : ℕ) : Type max u v :=
  SymmetricPower k (ULift.{u} (Fin m)) V

/- The degree-n associated-graded piece is the residue-field module quotient
`m^n / m^(n+1)`, represented as the canonical quotient of the ideal power by
`m • top`. -/
abbrev chapter04PowerQuotient (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Type u :=
  ((IsLocalRing.maximalIdeal A) ^ n : Ideal A) ⧸
    (IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A ((IsLocalRing.maximalIdeal A) ^ n : Ideal A)))

noncomputable instance chapter04PowerQuotient_residueFieldModule
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Module (IsLocalRing.ResidueField A) (chapter04PowerQuotient A n) :=
  Module.IsTorsionBySet.module
    (Module.isTorsionBySet_quotient_ideal_smul
      ((IsLocalRing.maximalIdeal A) ^ n : Ideal A)
      (IsLocalRing.maximalIdeal A))

def chapter04PowerQuotientMk {A : Type u} [CommRing A] [IsLocalRing A]
    (n : ℕ) {f : A} (hf : f ∈ (IsLocalRing.maximalIdeal A) ^ n) :
    chapter04PowerQuotient A n :=
  Submodule.Quotient.mk
    (p := IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A ((IsLocalRing.maximalIdeal A) ^ n : Ideal A)))
    (⟨f, hf⟩ : ((IsLocalRing.maximalIdeal A) ^ n : Ideal A))

def chapter04PowerQuotientZero
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    chapter04PowerQuotient A n :=
  chapter04PowerQuotientMk n
    ((IsLocalRing.maximalIdeal A) ^ n).zero_mem

/- LOCAL_DEPENDENCY_GUESS (4.3): Mathlib has the individual power quotient
and the symmetric tensor power, but not the regular-local associated-graded
comparison in one declaration. -/
class Chapter04InitialFormComparison
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
  (n : ℕ) where
  comparison : chapter04PowerQuotient A n ≃ₗ[IsLocalRing.ResidueField A]
    Chapter04SymmetricPower (IsLocalRing.ResidueField A)
      (IsLocalRing.CotangentSpace A) n
  comparison_preserves_nonzero :
    ∀ q, q ≠ chapter04PowerQuotientZero A n ↔ comparison q ≠ 0

theorem chapter04_initial_form_comparison_exists
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter04TwoDimensionalRegularLocalRing A) (n : ℕ) :
    Nonempty (Chapter04InitialFormComparison A n) := by
  sorry

structure Chapter04InitialFormData
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m] where
  in_power : f ∈ (IsLocalRing.maximalIdeal A) ^ m
  not_in_next_power : f ∉ (IsLocalRing.maximalIdeal A) ^ (m + 1)
  initialForm : Chapter04SymmetricPower (IsLocalRing.ResidueField A)
    (IsLocalRing.CotangentSpace A) m
  initialForm_eq_comparison :
    initialForm = Chapter04InitialFormComparison.comparison (A := A) (n := m)
      (chapter04PowerQuotientMk (A := A) m in_power)
  initialForm_nonzero : initialForm ≠ 0

theorem chapter04_initial_form_exists
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (IsLocalRing.maximalIdeal A) ^ m)
    (hm_next : f ∉ (IsLocalRing.maximalIdeal A) ^ (m + 1)) :
    Nonempty (Chapter04InitialFormData A f m) := by
  sorry

noncomputable def chapter04InitialFormData
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (IsLocalRing.maximalIdeal A) ^ m)
    (hm_next : f ∉ (IsLocalRing.maximalIdeal A) ^ (m + 1)) :
    Chapter04InitialFormData A f m :=
  Classical.choice (chapter04_initial_form_exists A f m hm hm_next)

abbrev chapter04InitialForm
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (IsLocalRing.maximalIdeal A) ^ m)
    (hm_next : f ∉ (IsLocalRing.maximalIdeal A) ^ (m + 1)) :=
  (chapter04InitialFormData A f m hm hm_next).initialForm

theorem chapter04_initial_form_is_nonzero
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (f : A) (m : ℕ) [Chapter04InitialFormComparison A m]
    (hm : f ∈ (IsLocalRing.maximalIdeal A) ^ m)
    (hm_next : f ∉ (IsLocalRing.maximalIdeal A) ^ (m + 1)) :
    chapter04InitialForm A f m hm hm_next ≠ 0 := by
  exact (chapter04InitialFormData A f m hm hm_next).initialForm_nonzero

/- The projectivized initial form cuts the strict transform on the exceptional
line.  The relation is kept as a named data package because the pinned tree
does not yet supply the graded Rees-algebra-to-projective-bundle comparison. -/
/- A local equation witness ties the algebraic initial form to the divisor on
the surface, rather than allowing an unrelated element of an unrelated ring. -/
def Chapter04CurveLocalEquationAtPoint
    {X : Scheme.{u}} (D : Chapter04EffectiveCartierDivisor X)
    (x : X) (f : X.presheaf.stalk x) : Prop :=
  ∃ (U : X.affineOpens) (hx : x ∈ U.1) (g : Γ(X, U.1)),
    D.ideal.ideal U = Ideal.span ({g} : Set Γ(X, U.1)) ∧
      f = (X.presheaf.germ U.1 x hx).hom g

/- The pinned projective-bundle API does not yet expose the zero divisor of a
 homogeneous form on the exceptional projective line.  Keep that missing
 comparison as an explicit vanishing-locus interface, but only for nonzero
 forms: the zero form does not define an effective Cartier divisor. -/
abbrev Chapter04NonzeroInitialForm
    (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] (m : ℕ) : Type max u v :=
  {q : Chapter04SymmetricPower k V m // q ≠ 0}

class Chapter04InitialFormCutAPI
    (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] (m : ℕ) (E : Scheme.{u}) where
  cut : Chapter04NonzeroInitialForm k V m → Chapter04EffectiveCartierDivisor E
  vanishingLocus : Chapter04NonzeroInitialForm k V m → Set E
  cut_support : ∀ q, (cut q).ideal.support = vanishingLocus q

structure Chapter04InitialFormExceptionalIntersectionData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (f : X.presheaf.stalk x) (m : ℕ)
    [IsRegularLocalRing (X.presheaf.stalk x)]
    [Chapter04InitialFormComparison (X.presheaf.stalk x) m]
    [Chapter04InitialFormCutAPI
      (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) m B.exceptionalSubscheme] where
  point_closed : IsClosed ({x} : Set X)
  centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x)
  centerPoint_over :
    centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x
  localEquation : Chapter04CurveLocalEquationAtPoint D x f
  initial : Chapter04InitialFormData (X.presheaf.stalk x) f m
  initialFormCut : Chapter04EffectiveCartierDivisor B.exceptionalSubscheme
  initialFormCut_eq_intersection :
    initialFormCut.ideal = T.transform.ideal.comap B.exceptionalInclusion
  initialFormCut_eq_initialForm_cut :
    initialFormCut.ideal =
      (Chapter04InitialFormCutAPI.cut
        (k := IsLocalRing.ResidueField (X.presheaf.stalk x))
        (V := IsLocalRing.CotangentSpace (X.presheaf.stalk x))
        (m := m) (E := B.exceptionalSubscheme)
        ⟨initial.initialForm, initial.initialForm_nonzero⟩).ideal
  exceptional_factor_removed :
    (chapter04DivisorNatMultiple m E.divisor).ideal =
      ∏ _ : Fin m, E.divisor.ideal
  strict_transform_is_T : T.transform.ideal = chapter04StrictTransformIdeal (J := D.ideal) B

theorem chapter04_initial_form_cuts_strict_transform_on_exceptional
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X)
    (hx : Chapter04RegularSurfacePoint x)
    (hx_closed : IsClosed ({x} : Set X))
    (hcenter : Chapter04RegularClosedCenter I)
    (B : Chapter04Blowup X I)
    (D : Chapter04EffectiveCartierDivisor X)
    (centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x))
    (centerPoint_over : centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (f : X.presheaf.stalk x) (m : ℕ)
    (hlocal : Chapter04CurveLocalEquationAtPoint D x f)
    (hm : f ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ^ m)
    (hm_next : f ∉ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ^ (m + 1))
    [IsRegularLocalRing (X.presheaf.stalk x)]
    [Chapter04InitialFormComparison (X.presheaf.stalk x) m]
    [Chapter04InitialFormCutAPI
      (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) m B.exceptionalSubscheme] :
    Nonempty (Chapter04InitialFormExceptionalIntersectionData x B D E T f m) := by
  sorry

/-! ### Intersection number and residue degree -/

def chapter04LocalIntersectionIdeal {A : Type u} [CommRing A]
    (f g : A) : Ideal A :=
  Ideal.span ({f, g} : Set A)

noncomputable def chapter04LocalIntersectionLength {A : Type u} [CommRing A]
    (f g : A) : ℕ∞ :=
  Module.length A (A ⧸ chapter04LocalIntersectionIdeal f g)

structure Chapter04ProperIntersectionData
    {Y : Scheme.{u}} (D E : Chapter04EffectiveCartierDivisor Y) where
  point : Y
  point_closed : IsClosed ({point} : Set Y)
  surface_point : Chapter04RegularSurfacePoint point
  affineOpen : Y.affineOpens
  point_mem_affineOpen : point ∈ affineOpen.1
  firstSection : Γ(Y, affineOpen.1)
  secondSection : Γ(Y, affineOpen.1)
  first_ideal_eq_span :
    D.ideal.ideal affineOpen = Ideal.span ({firstSection} : Set Γ(Y, affineOpen.1))
  second_ideal_eq_span :
    E.ideal.ideal affineOpen = Ideal.span ({secondSection} : Set Γ(Y, affineOpen.1))
  firstEquation : Y.presheaf.stalk point
  firstEquation_eq_germ :
    firstEquation =
      (Y.presheaf.germ affineOpen.1 point point_mem_affineOpen).hom firstSection
  secondEquation : Y.presheaf.stalk point
  secondEquation_eq_germ :
    secondEquation =
      (Y.presheaf.germ affineOpen.1 point point_mem_affineOpen).hom secondSection
  proper :
    (chapter04LocalIntersectionIdeal firstEquation secondEquation).radical =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk point)
  length : ℕ∞
  length_eq_local_quotient :
    length = chapter04LocalIntersectionLength firstEquation secondEquation
  length_finite : length ≠ ⊤
  /- A local length is the whole global intersection only when this is the
     unique intersection point. -/
  unique_support :
    ((D.ideal.support : Set Y) ∩ (E.ideal.support : Set Y)) = {point}

class Chapter04IntersectionNumberAPI (Y : Scheme.{u}) where
  /- Intersection numbers on an arithmetic surface are fiberwise: the base
     morphism is part of the datum, because residue-field degrees change when
     the same closed point is viewed over a different field. -/
  intersection : ∀ {k₀ : Type u} [Field k₀],
    (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀)) →
      Chapter04EffectiveCartierDivisor Y →
      Chapter04EffectiveCartierDivisor Y → ℕ
  symmetric : ∀ {k₀ : Type u} [Field k₀]
    (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀)) D E,
      intersection π D E = intersection π E D
  congr_ideal : ∀ {k₀ : Type u} [Field k₀]
    (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀))
    {D D' E E'}, D.ideal = D'.ideal → E.ideal = E'.ideal →
      intersection π D E = intersection π D' E'
  additive_left : ∀ {k₀ : Type u} [Field k₀]
    (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀)) D E F,
      intersection π (chapter04DivisorAdd D E) F =
        intersection π D F + intersection π E F
  additive_right : ∀ {k₀ : Type u} [Field k₀]
    (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀)) D E F,
      intersection π D (chapter04DivisorAdd E F) =
        intersection π D E + intersection π D F
  properIntersectionLength :
    ∀ (D E : Chapter04EffectiveCartierDivisor Y),
      Chapter04ProperIntersectionData D E → ℕ∞
  properIntersectionLength_eq_local_quotient :
    ∀ (D E : Chapter04EffectiveCartierDivisor Y)
      (p : Chapter04ProperIntersectionData D E),
      properIntersectionLength D E p =
        chapter04LocalIntersectionLength p.firstEquation p.secondEquation
  properIntersectionLength_finite :
    ∀ (D E : Chapter04EffectiveCartierDivisor Y)
      (p : Chapter04ProperIntersectionData D E),
      properIntersectionLength D E p ≠ ⊤
  /- Over a rational intersection point, the fiberwise number is the local
     quotient length itself.  The residue-degree-weighted version below is the
     form used over an arbitrary base field. -/
  intersection_eq_properIntersectionLength :
    ∀ {k₀ : Type u} [Field k₀]
      (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀))
      (D E : Chapter04EffectiveCartierDivisor Y)
      (p : Chapter04ProperIntersectionData D E),
      (hp : ((D.ideal.support : Set Y) ∩ (E.ideal.support : Set Y)) = {p.point}) →
      (hdegree_one : π.residueDegree p.point = 1) →
      (intersection π D E : ℕ∞) = properIntersectionLength D E p
  intersection_residueDegree_compatibility :
    ∀ {k₀ : Type u} [Field k₀]
      (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀))
      (D E : Chapter04EffectiveCartierDivisor Y)
      (p : Chapter04ProperIntersectionData D E),
      (hp : ((D.ideal.support : Set Y) ∩ (E.ideal.support : Set Y)) = {p.point}) →
      (hdegree : 0 < π.residueDegree p.point) →
      intersection π D E =
        (properIntersectionLength D E p).toNat * π.residueDegree p.point

def chapter04IntersectionNumber
    {Y : Scheme.{u}} [Chapter04IntersectionNumberAPI Y]
    {k₀ : Type u} [Field k₀]
    (π : Y ⟶ AlgebraicGeometry.Spec (.of k₀))
    (D E : Chapter04EffectiveCartierDivisor Y) : ℕ :=
  Chapter04IntersectionNumberAPI.intersection π D E

def chapter04ResidueDegree
    {X : Scheme.{u}} {k₀ : Type u} [Field k₀]
    (π : X ⟶ AlgebraicGeometry.Spec (.of k₀)) (x : X) : ℕ :=
  π.residueDegree x

theorem chapter04_residue_degree_is_field_extension_degree
    {X : Scheme.{u}} {k₀ : Type u} [Field k₀]
    (π : X ⟶ AlgebraicGeometry.Spec (.of k₀)) (x : X) :
    chapter04ResidueDegree π x = π.residueDegree x := by
  rfl

theorem chapter04_exceptional_intersection_formula
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {k₀ : Type u} [Field k₀]
    (π : X ⟶ AlgebraicGeometry.Spec (.of k₀))
    (x : X)
    (hx : Chapter04RegularSurfacePoint x)
    (hx_closed : IsClosed ({x} : Set X))
    (hX : IsIntegral X)
    (hcenter : Chapter04RegularClosedCenter I)
    (hdegree : 0 < π.residueDegree x)
    (B : Chapter04Blowup X I)
    (hB_regular : ∀ y : B.carrier,
      IsRegularLocalRing (B.carrier.presheaf.stalk y))
    (centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x))
    (centerPoint_over : centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (horder : Chapter04GenericOrderAlongCenter I D)
    (hgeneric : horder.genericPoint = x)
    [Chapter04IntersectionNumberAPI B.carrier] :
    chapter04IntersectionNumber (B.morphism ≫ π) T.divisor E.divisor =
      horder.order * chapter04ResidueDegree π x := by
  sorry

/- When the initial form splits over the residue field, repeated factors are
reflected by repeated tangent directions on the exceptional projective line.
This data is intentionally conditional: over a non-algebraically closed field,
an irreducible tangent factor need not define a k-rational direction. -/
structure Chapter04TangentDirectionMultiplicityData
    (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] (m : ℕ) where
  numberOfDirections : ℕ
  direction : Fin numberOfDirections →
    { L : Submodule k V // Module.finrank k L = 1 }
  direction_injective : Function.Injective direction
  multiplicity : Fin numberOfDirections → ℕ
  positive : ∀ i, 0 < multiplicity i
  totalMultiplicity : ∑ i, multiplicity i = m
  initial_form : Chapter04SymmetricPower k V m
  factorIndex : Fin m → Fin numberOfDirections
  factor : Fin m → V
  factor_mem_direction :
    ∀ j, factor j ∈ (direction (factorIndex j)).1
  factor_ne_zero : ∀ j, factor j ≠ 0
  factorIndex_fiber_card :
    ∀ i, Fintype.card {j : Fin m // factorIndex j = i} = multiplicity i
  factorScalar : k
  factorScalar_ne_zero : factorScalar ≠ 0
  factorization :
    initial_form = factorScalar •
      (⨂ₛ[k] i : ULift.{u} (Fin m), factor (ULift.down i))

theorem chapter04_tangent_direction_multiplicities_sum_to_degree
    (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (m : ℕ) (d : Chapter04TangentDirectionMultiplicityData k V m) :
    (∑ i, d.multiplicity i) = m :=
  d.totalMultiplicity

/-! ### Smooth curves and contact -/

structure Chapter04SmoothCurveTangentDirectionData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X) where
  point_closed : IsClosed ({x} : Set X)
  smooth : Chapter04SmoothCurveAtPoint C x
  exceptional : Chapter04ExceptionalDivisorData B
  transform : Chapter04StrictTransformCartierData (J := C.ideal) B
  fiberDirections : Chapter04ExceptionalTangentDirectionData x B
  rationalPoint :
    {p : AlgebraicGeometry.Spec (X.residueField x) ⟶ B.exceptionalSubscheme //
      p ≫ B.exceptionalToCenter = fiberDirections.centerPoint.inv}
  direction : Chapter04TangentDirection (X.presheaf.stalk x)
  direction_is_rational_point :
    fiberDirections.rationalPointDirectionEquiv rationalPoint = direction
  rationalPoint_on_transform :
    Set.range (rationalPoint.1 ≫ B.exceptionalInclusion) ⊆
      (transform.divisor.ideal.support : Set B.carrier)
  transform_exceptional_intersection_is_rationalPoint :
    ((transform.divisor.ideal.support : Set B.carrier) ∩
      (B.exceptionalIdeal.support : Set B.carrier)) =
      Set.range (rationalPoint.1 ≫ B.exceptionalInclusion)

/- The numerical intersection statement is a theorem rather than a field of
the tangent-direction data: otherwise downstream results could assume the
very conclusion they are meant to establish. -/
theorem chapter04_smooth_curve_transform_intersects_exceptional_once
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} (hx : Chapter04RegularSurfacePoint x)
    (hcenter : Chapter04RegularClosedCenter I)
    {B : Chapter04Blowup X I}
    (π : B.carrier ⟶ AlgebraicGeometry.Spec (.of (X.residueField x)))
    {C : Chapter04EffectiveCartierDivisor X}
    (T : Chapter04SmoothCurveTangentDirectionData x B C)
    (hB_regular : ∀ y : B.carrier,
      IsRegularLocalRing (B.carrier.presheaf.stalk y))
    (hπ : ∀ y : B.carrier,
      y ∈ Set.range (T.rationalPoint.1 ≫ B.exceptionalInclusion) →
        π.residueDegree y = 1)
    [Chapter04IntersectionNumberAPI B.carrier] :
    chapter04IntersectionNumber π T.transform.divisor T.exceptional.divisor = 1 := by
  sorry

theorem chapter04_smooth_curve_has_one_tangent_direction
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    {x : X} (hx : Chapter04RegularSurfacePoint x)
    (hx_closed : IsClosed ({x} : Set X))
    (hcenter : Chapter04RegularClosedCenter I)
    (hX : IsIntegral X)
    (hI_ne_zero : I ≠ (⊥ : X.IdealSheafData))
    (B : Chapter04Blowup X I)
    (centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x))
    (centerPoint_over : centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x)
    (C : Chapter04EffectiveCartierDivisor X)
    (hC_coherent : Chapter04CoherentIdeal C.ideal)
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
    (_x : X) (B : Chapter04Blowup X I)
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
    (hcenter : TC.fiberDirections.centerPoint = TD.fiberDirections.centerPoint)
    (hfiberDirections : TC.fiberDirections = TD.fiberDirections)
    (hdir : TC.direction ≠ TD.direction) :
    Chapter04StrictTransformsDisjointAbovePoint x B TC.transform TD.transform := by
  sorry

theorem chapter04_shared_tangent_direction_gives_intersection_on_exceptional
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    {C D : Chapter04EffectiveCartierDivisor X}
    (TC : Chapter04SmoothCurveTangentDirectionData x B C)
    (TD : Chapter04SmoothCurveTangentDirectionData x B D)
    (hcenter : TC.fiberDirections.centerPoint = TD.fiberDirections.centerPoint)
    (hfiberDirections : TC.fiberDirections = TD.fiberDirections)
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
  first_order_agrees : f - g ∈ (IsLocalRing.maximalIdeal R) ^ 2
  next_order : ℕ
  next_order_is_order_of_difference :
    next_order = chapter04OrderAtRegularPoint (f - g)

theorem chapter04_next_contact_term_is_order_of_difference
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f g : R) (hcontact : f - g ∈ (IsLocalRing.maximalIdeal R) ^ 2)
    (hfinite : ∃ n : ℕ, f - g ∉ (IsLocalRing.maximalIdeal R) ^ (n + 1)) :
    ∃ c : Chapter04NextContactTerm f g,
      c.next_order = chapter04OrderAtRegularPoint (f - g) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
