import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04.Section01TheExceptionalIdealAndNormalDirections

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 4.2. Total and strict transforms -/

/-- The inverse-image ideal of a closed subscheme along the blowup map. -/
def chapter04InverseImageIdeal
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) : B.carrier.IdealSheafData :=
  J.comap B.morphism

@[simp]
theorem chapter04InverseImageIdeal_def
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04InverseImageIdeal B = J.comap B.morphism :=
  rfl

/-- Pullback of an effective Cartier divisor along the blowup morphism.  The
integrality hypothesis is the no-component-mapped-into-the-divisor condition
under which the Cartier pullback is effective. -/
def chapter04TotalTransform
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hY : IsIntegral B.carrier)
    (D : Chapter04EffectiveCartierDivisor X) :
    Chapter04EffectiveCartierDivisor B.carrier :=
  { ideal := D.ideal.comap B.morphism
    isEffectiveCartier := by
      sorry }

@[simp]
theorem chapter04TotalTransform_ideal
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hY : IsIntegral B.carrier)
    (D : Chapter04EffectiveCartierDivisor X) :
    (chapter04TotalTransform B hY D).ideal = D.ideal.comap B.morphism :=
  rfl

/-- A local equation of an effective Cartier divisor on an affine open. -/
structure Chapter04LocalEquation
    {X : Scheme.{u}} (D : Chapter04EffectiveCartierDivisor X) where
  open : X.affineOpens
  section : Γ(X, open.1)
  ideal_eq_span : D.ideal.ideal open = Ideal.span ({section} : Set Γ(X, open.1))
  section_nonZeroDivisor : section ∈ nonZeroDivisors Γ(X, open.1)

/- The equation on the target is carried by the same rational function; the
pullback operation on sections is deliberately kept in the local-equation
record because the canonical morphism of affine charts is supplied by the
blowup construction. -/
structure Chapter04TotalTransformLocalEquation
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) (hY : IsIntegral B.carrier)
    {D : Chapter04EffectiveCartierDivisor X}
    (e : Chapter04LocalEquation D) where
  source : Chapter04LocalEquation D
  source_eq : source = e
  target_ideal : (chapter04TotalTransform B hY D).ideal = D.ideal.comap B.morphism
  /- LOCAL_DEPENDENCY_GUESS (4.2): the pinned tree lacks the rational-function
     Cartier-divisor pullback object, so this field is the missing comparison
     between the section on the source chart and its pullback. -/
  same_rational_function : Prop

theorem chapter04_total_transform_same_local_equation
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) (hY : IsIntegral B.carrier)
    {D : Chapter04EffectiveCartierDivisor X}
    (e : Chapter04LocalEquation D) :
    Nonempty (Chapter04TotalTransformLocalEquation B hY e) := by
  sorry

/- Saturation by the exceptional ideal is defined affine-locally using the
canonical ideal colon operation.  This is the algebraic operation that
removes sections annihilated by a power of the exceptional ideal. -/
def chapter04IdealSaturation {R : Type u} [CommRing R]
    (J K : Ideal R) : Ideal R :=
  sSup (Set.range (fun n : ℕ => J.colon ((K ^ n : Ideal R) : Set R)))

def chapter04IdealSheafSaturation
    {X : Scheme.{u}} (J K : X.IdealSheafData) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals
    (fun U => chapter04IdealSaturation (J.ideal U) (K.ideal U))

@[simp]
theorem chapter04IdealSheafSaturation_ideal
    {X : Scheme.{u}} (J K : X.IdealSheafData) (U : X.affineOpens) :
    (chapter04IdealSheafSaturation J K).ideal U =
      chapter04IdealSaturation (J.ideal U) (K.ideal U) := by
  sorry

/-- The scheme-theoretic strict-transform ideal of a closed subscheme. -/
def chapter04StrictTransformIdeal
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) : B.carrier.IdealSheafData :=
  chapter04IdealSheafSaturation (J.comap B.morphism) B.exceptionalIdeal

@[simp]
theorem chapter04StrictTransformIdeal_def
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04StrictTransformIdeal B =
      chapter04IdealSheafSaturation (J.comap B.morphism) B.exceptionalIdeal :=
  rfl

structure Chapter04StrictTransformData
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) where
  ideal : B.carrier.IdealSheafData
  ideal_eq_saturation : ideal = chapter04StrictTransformIdeal (J := J) B
  support_is_closure :
    (ideal.support : Set B.carrier) =
      closure (B.morphism ⁻¹' ((J.support : Set X) \ (I.support : Set X)))

abbrev Chapter04StrictTransformSubscheme
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    {B : Chapter04Blowup X I}
    (T : Chapter04StrictTransformData (J := J) B) : Scheme.{u} :=
  T.ideal.subscheme

theorem chapter04_strict_transform_exists
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    Nonempty (Chapter04StrictTransformData (J := J) B) := by
  sorry

noncomputable def chapter04StrictTransform
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) : Chapter04StrictTransformData (J := J) B :=
  Classical.choice (chapter04_strict_transform_exists B)

theorem chapter04_strict_transform_is_saturated
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    (chapter04StrictTransform (J := J) B).ideal =
      chapter04IdealSheafSaturation (J.comap B.morphism) B.exceptionalIdeal := by
  exact (chapter04StrictTransform (J := J) B).ideal_eq_saturation

theorem chapter04_strict_transform_support_is_closure
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    ((chapter04StrictTransform (J := J) B).ideal.support : Set B.carrier) =
      closure (B.morphism ⁻¹' ((J.support : Set X) \ (I.support : Set X))) := by
  exact (chapter04StrictTransform (J := J) B).support_is_closure

/- Taking the inverse image without saturation gives the total transform. -/
theorem chapter04_inverse_image_is_total_transform
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04InverseImageIdeal B = J.comap B.morphism :=
  rfl

theorem chapter04_strict_transform_removes_exceptional_sections
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04StrictTransformIdeal B =
      chapter04IdealSheafSaturation (chapter04InverseImageIdeal B)
        B.exceptionalIdeal := by
  rfl

/-! ### Integral strict transforms -/

structure Chapter04IntegralClosedSubscheme (X : Scheme.{u}) where
  ideal : X.IdealSheafData
  integral : IsIntegral ideal.subscheme

def Chapter04ClosedSubschemeNotContainedInCenter
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (W : Chapter04IntegralClosedSubscheme X) : Prop :=
  ¬ I ≤ W.ideal

structure Chapter04IntegralStrictTransformData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X) where
  transform : Chapter04StrictTransformData (J := W.ideal) B
  integral : IsIntegral transform.ideal.subscheme
  not_contained_in_center : Chapter04ClosedSubschemeNotContainedInCenter W

theorem chapter04_integral_strict_transform_exists
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X)
    (hW : Chapter04ClosedSubschemeNotContainedInCenter W) :
    Nonempty (Chapter04IntegralStrictTransformData B W) := by
  sorry

noncomputable def chapter04IntegralStrictTransform
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X)
    (hW : Chapter04ClosedSubschemeNotContainedInCenter W) :
    Chapter04IntegralStrictTransformData B W :=
  Classical.choice (chapter04_integral_strict_transform_exists B W hW)

theorem chapter04_integral_strict_transform_is_integral
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X)
    (hW : Chapter04ClosedSubschemeNotContainedInCenter W) :
    IsIntegral (chapter04IntegralStrictTransform B W hW).transform.ideal.subscheme := by
  exact (chapter04IntegralStrictTransform B W hW).integral

/- The strict transform of a Cartier divisor is again represented by an
effective Cartier divisor under the regular-center hypotheses used in the
transform formula. -/
structure Chapter04StrictTransformCartierData
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) where
  transform : Chapter04StrictTransformData (J := J) B
  divisor : Chapter04EffectiveCartierDivisor B.carrier
  divisor_ideal_eq_transform : divisor.ideal = transform.ideal

/- The order condition is the generic form of “in the m-th power but not
generically in the next power.”  The second field is intentionally not
replaced by the stronger global non-membership condition. -/
structure Chapter04GenericOrderAlongCenter
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (D : Chapter04EffectiveCartierDivisor X) where
  order : ℕ
  in_power : D.ideal ≤ I ^ order
  /- LOCAL_DEPENDENCY_GUESS (4.2): replace this field by the canonical generic
     stalk membership predicate when the center's generic-point API is merged. -/
  not_generically_in_next_power : Prop

abbrev Chapter04MultiplicityAlongCenter
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (D : Chapter04EffectiveCartierDivisor X)
    (h : Chapter04GenericOrderAlongCenter I D) : ℕ :=
  h.order

def chapter04DivisorNatMultiple
    {X : Scheme.{u}} (n : ℕ) (D : Chapter04EffectiveCartierDivisor X) :
    Chapter04EffectiveCartierDivisor X :=
  Chapter04EffectiveCartierDivisor.sum (fun _ : Fin n => D)

def chapter04DivisorAdd
    {X : Scheme.{u}} (D E : Chapter04EffectiveCartierDivisor X) :
    Chapter04EffectiveCartierDivisor X :=
  Chapter04EffectiveCartierDivisor.add D E

theorem chapter04_divisor_natMultiple_ideal
    {X : Scheme.{u}} (n : ℕ) (D : Chapter04EffectiveCartierDivisor X) :
    (chapter04DivisorNatMultiple n D).ideal = ∏ _ : Fin n, D.ideal := by
  rfl

theorem chapter04_total_transform_decomposition
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hY : IsIntegral B.carrier)
    (hcenter : Chapter04IntegralRegularClosedCenter I)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (horder : Chapter04GenericOrderAlongCenter I D) :
    chapter04TotalTransform B hY D =
      chapter04DivisorAdd T.divisor
        (chapter04DivisorNatMultiple horder.order E.divisor) := by
  sorry

/- A less dependent form of the same equality is useful to downstream
chapters: the named strict transform and the exceptional divisor are chosen
from their canonical data packages. -/
theorem chapter04_blowup_cartier_transform_formula
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hY : IsIntegral B.carrier)
    (hcenter : Chapter04IntegralRegularClosedCenter I)
    (D : Chapter04EffectiveCartierDivisor X)
    (E : Chapter04ExceptionalDivisorData B)
    (horder : Chapter04GenericOrderAlongCenter I D) :
    ∃ T : Chapter04StrictTransformCartierData (J := D.ideal) B,
      T.transform.ideal = chapter04StrictTransformIdeal (J := D.ideal) B ∧
      chapter04TotalTransform B hY D =
        chapter04DivisorAdd
          T.divisor (chapter04DivisorNatMultiple horder.order E.divisor) := by
  sorry

/-! ### Pointwise order -/

def chapter04OrderAtRegularPoint {R : Type u} [CommRing R]
    [IsLocalRing R] (f : R) : ℕ :=
  sSup {m : ℕ | f ∈ (maximalIdeal R) ^ m}

theorem chapter04_orderAtRegularPoint_is_max
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R) (hfinite : ∃ m : ℕ, f ∉ (maximalIdeal R) ^ (m + 1)) :
    chapter04OrderAtRegularPoint f =
      sSup {m : ℕ | f ∈ (maximalIdeal R) ^ m} := by
  rfl

theorem chapter04_orderAtRegularPoint_characterization
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R) (m : ℕ)
    (hm : f ∈ (maximalIdeal R) ^ m)
    (hm_next : f ∉ (maximalIdeal R) ^ (m + 1)) :
    chapter04OrderAtRegularPoint f = m := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
