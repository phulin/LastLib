import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04.Section03MultiplicityAtARegularPoint

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 4.4. Transforming a boundary -/

/-- A finite effective Cartier boundary with a nonnegative integer coefficient
on each component. -/
structure Chapter04Boundary (X : Scheme.{u}) (n : ℕ) where
  component : Fin n → Chapter04EffectiveCartierDivisor X
  coefficient : Fin n → ℕ

def chapter04BoundaryIdeal
    {X : Scheme.{u}} {n : ℕ} (B : Chapter04Boundary X n) : X.IdealSheafData :=
  ∏ i, (B.component i).ideal ^ B.coefficient i

def chapter04BoundaryDivisor
    {X : Scheme.{u}} {n : ℕ} (B : Chapter04Boundary X n) :
    Chapter04EffectiveCartierDivisor X :=
  { ideal := chapter04BoundaryIdeal B
    isEffectiveCartier := by
      sorry }

def chapter04ReducedBoundary
    {X : Scheme.{u}} {n : ℕ} (B : Chapter04Boundary X n) : Chapter04Boundary X n :=
  { component := B.component
    coefficient := fun _ => 1 }

@[simp]
theorem chapter04ReducedBoundary_coefficient
    {X : Scheme.{u}} {n : ℕ} (B : Chapter04Boundary X n) (i : Fin n) :
    (chapter04ReducedBoundary B).coefficient i = 1 :=
  rfl

theorem chapter04BoundaryIdeal_reduced
    {X : Scheme.{u}} {n : ℕ} (B : Chapter04Boundary X n) :
    chapter04BoundaryIdeal (chapter04ReducedBoundary B) =
      ∏ i, (B.component i).ideal := by
  simp [chapter04BoundaryIdeal, chapter04ReducedBoundary]

/- The data needed to transform all boundary components through the same
point blowup.  `pointMultiplicity` is the exact coefficient m_x(B_i) from the
source formula, and its local-order field prevents it from being an
unrelated numerical label. -/
structure Chapter04BoundaryTransformData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} (B : Chapter04Blowup X I)
    (boundary : Chapter04Boundary X n) (x : X) where
  point_closed : IsClosed ({x} : Set X)
  source_integral : IsIntegral X
  exceptional : Chapter04ExceptionalDivisorData B
  centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x)
  centerPoint_over :
    centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x
  center_regular_integral : Chapter04IntegralRegularClosedCenter I
  blowup_integral : IsIntegral B.carrier
  strictTransform : ∀ i, Chapter04StrictTransformCartierData
    (J := (boundary.component i).ideal) B
  component_order : ∀ i,
    Chapter04GenericOrderAlongCenter I (boundary.component i)
  component_order_genericPoint : ∀ i,
    (component_order i).genericPoint = x
  pointMultiplicity : Fin n → ℕ
  pointMultiplicity_is_order : ∀ i,
    Chapter04CurveHasMultiplicityAt (boundary.component i) x (pointMultiplicity i)
  pointMultiplicity_eq_component_order : ∀ i,
    pointMultiplicity i = (component_order i).order

def chapter04TransformedReducedBoundary
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) :
    Chapter04Boundary B.carrier (n + 1) :=
  { component := Fin.cases T.exceptional.divisor (fun i => (T.strictTransform i).divisor)
    coefficient := fun _ => 1 }

def chapter04TransformedTotalBoundary
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) :
    Chapter04Boundary B.carrier (n + 1) :=
  { component := Fin.cases T.exceptional.divisor (fun i => (T.strictTransform i).divisor)
    coefficient := Fin.cases
      (∑ i, boundary.coefficient i * T.pointMultiplicity i)
      (fun i => boundary.coefficient i) }

@[simp]
theorem chapter04TransformedReducedBoundary_exceptional_coefficient
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) :
    (chapter04TransformedReducedBoundary T).coefficient 0 = 1 :=
  rfl

@[simp]
theorem chapter04TransformedReducedBoundary_strict_coefficient
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) (i : Fin n) :
    (chapter04TransformedReducedBoundary T).coefficient i.succ = 1 :=
  rfl

@[simp]
theorem chapter04TransformedTotalBoundary_exceptional_coefficient
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) :
    (chapter04TransformedTotalBoundary T).coefficient 0 =
      ∑ i, boundary.coefficient i * T.pointMultiplicity i :=
  rfl

@[simp]
theorem chapter04TransformedTotalBoundary_strict_coefficient
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) (i : Fin n) :
    (chapter04TransformedTotalBoundary T).coefficient i.succ =
      boundary.coefficient i :=
  rfl

theorem chapter04_reduced_boundary_transform_formula
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) :
    chapter04BoundaryIdeal (chapter04TransformedReducedBoundary T) =
      T.exceptional.divisor.ideal *
        ∏ i, (T.strictTransform i).divisor.ideal := by
  sorry

theorem chapter04_total_boundary_transform_formula
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) :
    chapter04BoundaryIdeal (chapter04TransformedTotalBoundary T) =
      (∏ i, (T.strictTransform i).divisor.ideal ^ boundary.coefficient i) *
        T.exceptional.divisor.ideal ^
          (∑ i, boundary.coefficient i * T.pointMultiplicity i) := by
  sorry

/- Reduced and total transforms deliberately have different coefficient
profiles.  The former is the normal-crossings support, while the latter is the
pullback divisor with its exceptional multiplicity. -/
structure Chapter04ReducedAndTotalBoundaryViews
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {n : ℕ} {B : Chapter04Blowup X I} {boundary : Chapter04Boundary X n} {x : X}
    (T : Chapter04BoundaryTransformData B boundary x) where
  reduced : Chapter04Boundary B.carrier (n + 1)
  total : Chapter04Boundary B.carrier (n + 1)
  reduced_eq : reduced = chapter04TransformedReducedBoundary T
  total_eq : total = chapter04TransformedTotalBoundary T
  reduced_support_view :
    ∀ i, reduced.coefficient i = 1
  total_multiplicity_view :
    total.coefficient 0 = ∑ i, boundary.coefficient i * T.pointMultiplicity i

/-! ### Transverse and single-component examples -/

structure Chapter04TransverseBoundaryPair
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    (C D : Chapter04EffectiveCartierDivisor X) where
  surface_point : Chapter04RegularSurfacePoint x
  coefficientC : ℕ
  coefficientD : ℕ
  exceptional : Chapter04ExceptionalDivisorData B
  C_data : Chapter04SmoothCurveTangentDirectionData x B C
  D_data : Chapter04SmoothCurveTangentDirectionData x B D
  C_exceptional_eq : C_data.exceptional = exceptional
  D_exceptional_eq : D_data.exceptional = exceptional
  transverse : C_data.direction ≠ D_data.direction
  C_multiplicity : Chapter04CurveHasMultiplicityAt C x 1
  D_multiplicity : Chapter04CurveHasMultiplicityAt D x 1
  sourceBoundary : Chapter04Boundary X 2
  sourceBoundary_component_zero : sourceBoundary.component 0 = C
  sourceBoundary_component_one : sourceBoundary.component 1 = D
  sourceBoundary_coefficient_zero : sourceBoundary.coefficient 0 = coefficientC
  sourceBoundary_coefficient_one : sourceBoundary.coefficient 1 = coefficientD
  boundaryTransform : Chapter04BoundaryTransformData B sourceBoundary x

def chapter04TransversePairExceptionalMultiplicity
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} {B : Chapter04Blowup X I}
    {C D : Chapter04EffectiveCartierDivisor X}
    (P : Chapter04TransverseBoundaryPair x B C D) : ℕ :=
  (chapter04TransformedTotalBoundary P.boundaryTransform).coefficient 0

theorem chapter04_transverse_pair_exceptional_multiplicity
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} {B : Chapter04Blowup X I}
    {C D : Chapter04EffectiveCartierDivisor X}
    (P : Chapter04TransverseBoundaryPair x B C D) :
    chapter04TransversePairExceptionalMultiplicity P =
      P.coefficientC + P.coefficientD := by
  sorry

theorem chapter04_transverse_pair_meets_each_strict_transform_once
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} {B : Chapter04Blowup X I}
    {C D : Chapter04EffectiveCartierDivisor X}
    (P : Chapter04TransverseBoundaryPair x B C D)
    (π : B.carrier ⟶ AlgebraicGeometry.Spec (.of (X.residueField x)))
    (hB_regular : ∀ y : B.carrier,
      IsRegularLocalRing (B.carrier.presheaf.stalk y))
    (hπC : ∀ y : B.carrier,
      y ∈ Set.range (P.C_data.rationalPoint.1 ≫ B.exceptionalInclusion) →
        π.residueDegree y = 1)
    (hπD : ∀ y : B.carrier,
      y ∈ Set.range (P.D_data.rationalPoint.1 ≫ B.exceptionalInclusion) →
        π.residueDegree y = 1)
    [Chapter04IntersectionNumberAPI B.carrier] :
    chapter04IntersectionNumber π P.C_data.transform.divisor
        P.exceptional.divisor = 1 ∧
      chapter04IntersectionNumber π P.D_data.transform.divisor
        P.exceptional.divisor = 1 := by
  sorry

structure Chapter04SingleBoundaryComponent
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X) where
  coefficient : ℕ
  data : Chapter04SmoothCurveTangentDirectionData x B C
  multiplicity : Chapter04CurveHasMultiplicityAt C x 1
  sourceBoundary : Chapter04Boundary X 1
  sourceBoundary_component_zero : sourceBoundary.component 0 = C
  sourceBoundary_coefficient_zero : sourceBoundary.coefficient 0 = coefficient
  boundaryTransform : Chapter04BoundaryTransformData B sourceBoundary x

def chapter04SingleComponentExceptionalMultiplicity
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} {B : Chapter04Blowup X I}
    {C : Chapter04EffectiveCartierDivisor X}
    (P : Chapter04SingleBoundaryComponent x B C) : ℕ :=
  (chapter04TransformedTotalBoundary P.boundaryTransform).coefficient 0

theorem chapter04_single_component_exceptional_multiplicity
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} {B : Chapter04Blowup X I}
    {C : Chapter04EffectiveCartierDivisor X}
    (P : Chapter04SingleBoundaryComponent x B C) :
    chapter04SingleComponentExceptionalMultiplicity P = P.coefficient := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
