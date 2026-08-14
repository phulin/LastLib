import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open WithZero AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
### 2.4 Orders along a curve
-/

/- The DVR condition at closed points is the precise local consequence of the
   regular integral noetherian curve hypotheses used by the order API. -/
class Chapter02RegularIntegralNoetherianCurve (X : Scheme.{u})
    extends IsIntegral X, IsNoetherian X where
  regular_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  one_dimensional : ∀ x : X, coheight x ≤ 1
  closedPoint_coheight_one : ∀ x : X, IsClosed ({x} : Set X) → coheight x = 1
  /- LOCAL_DEPENDENCY_GUESS: the DVR consequence of regularity and
     one-dimensionality is not exposed by the pinned scheme API. -/
  closedPoint_isDVR : ∀ (x : X), IsClosed ({x} : Set X) →
    IsDiscreteValuationRing (X.presheaf.stalk x)

abbrev Chapter02ClosedPoint (X : Scheme.{u}) :=
  {x : X // IsClosed ({x} : Set X)}

theorem chapter02_closed_point_coheight_one
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    coheight x.1 = 1 :=
  C.closedPoint_coheight_one x.1 x.2

theorem chapter02_closed_point_stalk_is_DVR
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x.1) :=
  C.closedPoint_isDVR x.1 x.2

noncomputable def chapter02OrderHom
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    X.functionField →*₀ ℤᵐ⁰ :=
  X.ordHom x.1 (C.closedPoint_coheight_one x.1 x.2)

noncomputable def chapter02OrderOfRationalFunction
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) (f : X.functionField) : ℤ :=
  X.ord f x.1

theorem chapter02_order_of_unit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (U : X.Opens) [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f)
    (x : Chapter02ClosedPoint X) (hx : x.1 ∈ U) :
    chapter02OrderOfRationalFunction X x (X.germToFunctionField U f) = 0 := by
  exact Scheme.ord_of_isUnit hf hx

theorem chapter02_order_mul
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    chapter02OrderOfRationalFunction X x (f * g) =
      chapter02OrderOfRationalFunction X x f +
        chapter02OrderOfRationalFunction X x g := by
  exact Scheme.ord_mul hf hg

theorem chapter02_order_unchanged_by_regular_unit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (U : X.Opens) [Nonempty U] {f u : X.functionField}
    (hf : f ≠ 0) (hu : u ≠ 0)
    (hu_unit : ∃ s : Γ(X, U), IsUnit s ∧
      u = X.germToFunctionField U s) (x : Chapter02ClosedPoint X) :
    chapter02OrderOfRationalFunction X x (f * u) =
      chapter02OrderOfRationalFunction X x f := by
  obtain ⟨s, hs, rfl⟩ := hu_unit
  rw [chapter02_order_mul X x hf (by simpa using hu)]
  rw [chapter02_order_of_unit X U hs x]
  simp

def chapter02OrderOfRationalFunctionUnit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) : X.functionFieldˣ → ℤ :=
  fun f => chapter02OrderOfRationalFunction X x (f : X.functionField)

theorem chapter02OrderOfRationalFunctionUnit_mul
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) (f g : X.functionFieldˣ) :
    chapter02OrderOfRationalFunctionUnit X x (f * g) =
      chapter02OrderOfRationalFunctionUnit X x f +
        chapter02OrderOfRationalFunctionUnit X x g := by
  exact chapter02_order_mul X x (Units.ne_zero f) (Units.ne_zero g)

def chapter02OrderHomOnFunctionFieldUnits
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) : X.functionFieldˣ →* ℤ where
  toFun := chapter02OrderOfRationalFunctionUnit X x
  map_one' := by sorry
  map_mul' := by
    intro f g
    exact chapter02OrderOfRationalFunctionUnit_mul X x f g

noncomputable def chapter02StalkAddValuation
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    AddValuation (X.presheaf.stalk x.1) ℕ∞ :=
  letI := C.closedPoint_isDVR x.1 x.2
  IsDiscreteValuationRing.addVal (X.presheaf.stalk x.1)

theorem chapter02_stalk_addVal_uniformizer
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) {ϖ : X.presheaf.stalk x.1}
    (hϖ : Irreducible ϖ) :
    chapter02StalkAddValuation X x ϖ = 1 := by
  letI := C.closedPoint_isDVR x.1 x.2
  exact IsDiscreteValuationRing.addVal_uniformizer hϖ

noncomputable def chapter02NormalizedOrderHom
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) :
    X.functionField →*₀ ℤᵐ⁰ :=
  X.ordHom x.1 (C.closedPoint_coheight_one x.1 x.2)

theorem chapter02_normalized_order_hom_of_unit
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (U : X.Opens) [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f)
    (x : Chapter02ClosedPoint X) (hx : x.1 ∈ U) :
    chapter02NormalizedOrderHom X x (X.germToFunctionField U f) = 1 := by
  exact Scheme.ordHom_of_isUnit hf (C.closedPoint_coheight_one x.1 x.2) hx

/- LOCAL_DEPENDENCY_GUESS: identify sections of the chosen total quotient
   sheaf with rational functions so that the canonical Mathlib order can be
   applied to a Cartier equation. -/
class Chapter02MeromorphicFunctionFieldMap (X : Scheme.{u})
    [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] where
  toFunctionField : ∀ U : X.Opens,
    Chapter02MeromorphicSection X U →+* X.functionField

def chapter02MeromorphicSectionOrder
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    (U : X.Opens) (s : Chapter02MeromorphicSection X U)
    (x : Chapter02ClosedPoint X) : ℤ :=
  X.ord (F.toFunctionField U s) x.1

class Chapter02CurveCartierOrderAPI (X : Scheme.{u})
    [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X]
    [F : Chapter02MeromorphicFunctionFieldMap X] where
  order : Chapter02CartierDivisor X → Chapter02ClosedPoint X → ℤ
  local_formula : ∀ (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X),
    ∃ i : D.index, ∃ hx : x.1 ∈ D.openSet i,
      order D x = chapter02MeromorphicSectionOrder X (D.openSet i)
        (D.equation i) x

def chapter02CartierOrder
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) : ℤ :=
  A.order D x

theorem chapter02_cartier_order_local_formula
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) :
    ∃ i : D.index, ∃ hx : x.1 ∈ D.openSet i,
      chapter02CartierOrder X D x = chapter02MeromorphicSectionOrder X (D.openSet i)
        (D.equation i) x := by
  exact A.local_formula D x

def chapter02CartierOrderSupport
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) : Set (Chapter02ClosedPoint X) :=
  {x | chapter02CartierOrder X D x ≠ 0}

theorem chapter02_cartier_order_support_finite
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) :
    Set.Finite (chapter02CartierOrderSupport X D) := by
  sorry

theorem chapter02_principal_order_support_finite
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionField) :
    Set.Finite {x : Chapter02ClosedPoint X |
      chapter02OrderOfRationalFunction X x f ≠ 0} := by
  sorry

def chapter02Order
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) : ℤ :=
  chapter02CartierOrder X D x

abbrev Chapter02FormalDivisor (X : Scheme.{u})
    [C : Chapter02RegularIntegralNoetherianCurve X] :=
  Chapter02ClosedPoint X →₀ ℤ

def chapter02PointCycle
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (x : Chapter02ClosedPoint X) (n : ℤ) : Chapter02FormalDivisor X :=
  Finsupp.single x n

noncomputable def chapter02FormalDivisorOfCartier
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) : Chapter02FormalDivisor X :=
  Finsupp.onFinset
    (Set.Finite.toFinset (chapter02_cartier_order_support_finite X D))
    (fun x => chapter02CartierOrder X D x) (by sorry)

theorem chapter02_formal_divisor_of_cartier_apply
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) (x : Chapter02ClosedPoint X) :
    chapter02FormalDivisorOfCartier X D x = chapter02CartierOrder X D x := by
  sorry

theorem chapter02_cartier_divisor_formal_sum
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    [K : Chapter02MeromorphicSheaf X] [F : Chapter02MeromorphicFunctionFieldMap X]
    [A : Chapter02CurveCartierOrderAPI X]
    (D : Chapter02CartierDivisor X) :
    chapter02FormalDivisorOfCartier X D =
      ∑ x in (chapter02FormalDivisorOfCartier X D).support,
        chapter02PointCycle X x
          (chapter02Order X D x) := by
  sorry

noncomputable def chapter02PrincipalDivisor
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionFieldˣ) : Chapter02FormalDivisor X :=
  Finsupp.onFinset
    (Set.Finite.toFinset (chapter02_principal_order_support_finite X (f : X.functionField)))
    (fun x => chapter02OrderOfRationalFunction X x (f : X.functionField)) (by sorry)

theorem chapter02_principal_divisor_apply
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionFieldˣ) (x : Chapter02ClosedPoint X) :
    chapter02PrincipalDivisor X f x =
      chapter02OrderOfRationalFunction X x (f : X.functionField) := by
  sorry

theorem chapter02_principal_divisor_mul
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f g : X.functionFieldˣ) :
    chapter02PrincipalDivisor X (f * g) =
      chapter02PrincipalDivisor X f + chapter02PrincipalDivisor X g := by
  sorry

theorem chapter02_principal_divisor_formal_sum
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (f : X.functionFieldˣ) :
    chapter02PrincipalDivisor X f =
      ∑ x in (chapter02PrincipalDivisor X f).support,
        chapter02PointCycle X x
          (chapter02OrderOfRationalFunction X x (f : X.functionField)) := by
  sorry

def chapter02LinearlyEquivalent
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D E : Chapter02FormalDivisor X) : Prop :=
  ∃ f : X.functionFieldˣ, E = D + chapter02PrincipalDivisor X f

theorem chapter02_linearly_equivalent_refl
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D : Chapter02FormalDivisor X) :
    chapter02LinearlyEquivalent X D D := by
  exact ⟨1, by simp⟩

theorem chapter02_linearly_equivalent_symm
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D E : Chapter02FormalDivisor X)
    (hDE : chapter02LinearlyEquivalent X D E) :
    chapter02LinearlyEquivalent X E D := by
  sorry

theorem chapter02_linearly_equivalent_trans
    (X : Scheme.{u}) [C : Chapter02RegularIntegralNoetherianCurve X]
    (D E F : Chapter02FormalDivisor X)
    (hDE : chapter02LinearlyEquivalent X D E)
    (hEF : chapter02LinearlyEquivalent X E F) :
    chapter02LinearlyEquivalent X D F := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
