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
    chapter04InverseImageIdeal (J := J) B = J.comap B.morphism :=
  rfl

/-- Pullback of an effective Cartier divisor along the blowup morphism.  The
integrality hypothesis is the no-component-mapped-into-the-divisor condition
under which the Cartier pullback is effective. -/
def Chapter04PullbackIsEffectiveCartier
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (D : Chapter04EffectiveCartierDivisor X) : Prop :=
  (D.ideal.comap B.morphism).IsEffectiveCartier

def chapter04TotalTransform
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (_hY : IsIntegral B.carrier)
    (D : Chapter04EffectiveCartierDivisor X)
    (hD : Chapter04PullbackIsEffectiveCartier B D) :
    Chapter04EffectiveCartierDivisor B.carrier :=
  { ideal := D.ideal.comap B.morphism
    isEffectiveCartier := hD }

@[simp]
theorem chapter04TotalTransform_ideal
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hY : IsIntegral B.carrier)
    (D : Chapter04EffectiveCartierDivisor X)
    (hD : Chapter04PullbackIsEffectiveCartier B D) :
    (chapter04TotalTransform B hY D hD).ideal = D.ideal.comap B.morphism :=
  rfl

/-- A local equation of an effective Cartier divisor on an affine open. -/
structure Chapter04LocalEquation
    {X : Scheme.{u}} (D : Chapter04EffectiveCartierDivisor X) where
  affineOpen : X.affineOpens
  localSection : Γ(X, affineOpen.1)
  ideal_eq_span : D.ideal.ideal affineOpen =
    Ideal.span ({localSection} : Set Γ(X, affineOpen.1))
  section_nonZeroDivisor : localSection ∈ nonZeroDivisors Γ(X, affineOpen.1)

structure Chapter04TotalTransformLocalEquation
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) (hY : IsIntegral B.carrier)
    {D : Chapter04EffectiveCartierDivisor X}
    (hD : Chapter04PullbackIsEffectiveCartier B D)
    (e : Chapter04LocalEquation D) where
  source : Chapter04LocalEquation D
  source_eq : source = e
  target_ideal : (chapter04TotalTransform B hY D hD).ideal = D.ideal.comap B.morphism
  pullbackSection : Γ(B.carrier, B.morphism ⁻¹ᵁ e.affineOpen.1)
  pullbackSection_eq :
    pullbackSection = (B.morphism.app e.affineOpen.1).hom e.localSection

theorem chapter04_total_transform_same_local_equation
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I) (hY : IsIntegral B.carrier)
    {D : Chapter04EffectiveCartierDivisor X}
    (hD : Chapter04PullbackIsEffectiveCartier B D)
    (e : Chapter04LocalEquation D) :
    Nonempty (Chapter04TotalTransformLocalEquation B hY hD e) := by
  sorry

/- Saturation by the exceptional ideal is defined affine-locally using the
canonical ideal colon operation.  This is the algebraic operation that
removes sections annihilated by a power of the exceptional ideal. -/
def chapter04IdealSaturation {R : Type u} [CommRing R]
    (J K : Ideal R) : Ideal R :=
  sSup (Set.range (fun n : ℕ => J.colon ((K ^ n : Ideal R) : Set R)))

/- `IdealSheafData.ofIdeals` is only the largest ideal sheaf contained in an
   arbitrary affine family.  Saturation is defined by its compatible affine
   family, so retain the missing gluing comparison explicitly rather than
   silently replacing saturation by the smaller `ofIdeals` construction. -/
structure Chapter04IdealSheafSaturationData
    {X : Scheme.{u}} (J K : X.IdealSheafData) where
  ideal : X.IdealSheafData
  ideal_eq_affine_saturation :
    ∀ U : X.affineOpens,
      ideal.ideal U = chapter04IdealSaturation (J.ideal U) (K.ideal U)

theorem chapter04_ideal_sheaf_saturation_exists
    {X : Scheme.{u}} (J K : X.IdealSheafData) :
    Nonempty (Chapter04IdealSheafSaturationData J K) := by
  sorry

noncomputable def chapter04IdealSheafSaturationData
    {X : Scheme.{u}} (J K : X.IdealSheafData) :
    Chapter04IdealSheafSaturationData J K :=
  Classical.choice (chapter04_ideal_sheaf_saturation_exists J K)

def chapter04IdealSheafSaturation
    {X : Scheme.{u}} (J K : X.IdealSheafData) : X.IdealSheafData :=
  (chapter04IdealSheafSaturationData J K).ideal

theorem chapter04IdealSheafSaturation_ideal_eq_affine_saturation
    {X : Scheme.{u}} (J K : X.IdealSheafData) (U : X.affineOpens) :
    (chapter04IdealSheafSaturation J K).ideal U =
      chapter04IdealSaturation (J.ideal U) (K.ideal U) := by
  exact (chapter04IdealSheafSaturationData J K).ideal_eq_affine_saturation U

theorem chapter04IdealSheafSaturation_ideal_le
    {X : Scheme.{u}} (J K : X.IdealSheafData) :
    (chapter04IdealSheafSaturation J K).ideal ≤
      (fun U => chapter04IdealSaturation (J.ideal U) (K.ideal U)) := by
  intro U
  rw [chapter04IdealSheafSaturation_ideal_eq_affine_saturation J K U]

/-- The scheme-theoretic strict-transform ideal of a closed subscheme. -/
def chapter04StrictTransformIdeal
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) : B.carrier.IdealSheafData :=
  chapter04IdealSheafSaturation (J.comap B.morphism) B.exceptionalIdeal

@[simp]
theorem chapter04StrictTransformIdeal_def
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04StrictTransformIdeal (J := J) B =
      chapter04IdealSheafSaturation (J.comap B.morphism) B.exceptionalIdeal :=
  rfl

/- The tangent-cone data is stated after the strict-transform ideal so that
the scheme-theoretic intersection with the exceptional subscheme can be
recorded explicitly. -/
structure Chapter04ProjectivizedTangentConeData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (x : X) (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X) where
  point_closed : IsClosed ({x} : Set X)
  centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x)
  centerPoint_over :
    centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x
  tangentCone : Chapter04EffectiveCartierDivisor B.exceptionalSubscheme
  strictTransformIdeal : B.carrier.IdealSheafData
  strictTransformIdeal_eq :
    strictTransformIdeal = chapter04StrictTransformIdeal (J := C.ideal) B
  tangentCone_ideal_eq_restriction :
    tangentCone.ideal = strictTransformIdeal.comap B.exceptionalInclusion
  multiplicity : ℕ
  tangentCone_degree : ℕ
  tangentCone_degree_eq_multiplicity : tangentCone_degree = multiplicity

theorem chapter04_curve_meets_exceptional_in_tangent_cone
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} (hx : Chapter04RegularSurfacePoint x)
    (hx_closed : IsClosed ({x} : Set X))
    (hcenter : Chapter04RegularClosedCenter I)
    (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X)
    (centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x))
    (centerPoint_over : centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x)
    (m : ℕ)
    (hC_multiplicity : Chapter04CurveHasMultiplicityAt C x m)
    [Chapter04ConormalSheafAPI I] :
    ∃ T : Chapter04ProjectivizedTangentConeData x B C,
      T.multiplicity = m ∧ T.tangentCone_degree = m := by
  sorry

theorem chapter04_smooth_curve_tangent_cone_degree_one
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} (hx : Chapter04RegularSurfacePoint x)
    (hx_closed : IsClosed ({x} : Set X))
    (hcenter : Chapter04RegularClosedCenter I)
    (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X)
    (centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x))
    (centerPoint_over : centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x)
    (hC_smooth : Chapter04SmoothCurveAtPoint C x)
    [Chapter04ConormalSheafAPI I] :
    ∃ T : Chapter04ProjectivizedTangentConeData x B C,
      T.multiplicity = 1 ∧ T.tangentCone_degree = 1 := by
  sorry

theorem chapter04_curve_tangent_cone_degree_multiplicity
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {x : X} (hx : Chapter04RegularSurfacePoint x)
    (hx_closed : IsClosed ({x} : Set X))
    (hcenter : Chapter04RegularClosedCenter I)
    (B : Chapter04Blowup X I)
    (C : Chapter04EffectiveCartierDivisor X)
    (centerPoint : B.center ≅ AlgebraicGeometry.Spec (X.residueField x))
    (centerPoint_over : centerPoint.inv ≫ B.centerι = X.fromSpecResidueField x)
    (m : ℕ) (hC_multiplicity : Chapter04CurveHasMultiplicityAt C x m)
    [Chapter04ConormalSheafAPI I] :
    ∃ T : Chapter04ProjectivizedTangentConeData x B C,
      T.multiplicity = m ∧ T.tangentCone_degree = m := by
  sorry

def Chapter04StrictTransformSupportCompatibility
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) : Prop :=
  ((chapter04StrictTransformIdeal (J := J) B).support : Set B.carrier) =
    closure (B.morphism ⁻¹' ((J.support : Set X) \ (I.support : Set X)))

structure Chapter04StrictTransformData
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) where
  ideal : B.carrier.IdealSheafData
  ideal_eq_saturation : ideal = chapter04StrictTransformIdeal (J := J) B
  /- The affine colon construction is the actual saturation, rather than
     merely an upper bound supplied by `IdealSheafData.ofIdeals`. -/
  ideal_eq_affine_saturation :
    ∀ U : B.carrier.affineOpens,
      ideal.ideal U =
        chapter04IdealSaturation
          ((J.comap B.morphism).ideal U) (B.exceptionalIdeal.ideal U)
  support_is_closure :
    (ideal.support : Set B.carrier) =
      closure (B.morphism ⁻¹' ((J.support : Set X) \ (I.support : Set X)))

abbrev Chapter04StrictTransformSubscheme
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    {B : Chapter04Blowup X I}
    (T : Chapter04StrictTransformData (J := J) B) : Scheme.{u} :=
  T.ideal.subscheme

theorem chapter04_strict_transform_exists
    {X : Scheme.{u}} [IsNoetherian X] {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hJ : Chapter04CoherentIdeal J) :
    Nonempty (Chapter04StrictTransformData (J := J) B) := by
  sorry

noncomputable def chapter04StrictTransform
    {X : Scheme.{u}} [IsNoetherian X] {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hJ : Chapter04CoherentIdeal J) :
    Chapter04StrictTransformData (J := J) B :=
  Classical.choice (chapter04_strict_transform_exists B hJ)

theorem chapter04_strict_transform_is_saturated
    {X : Scheme.{u}} [IsNoetherian X] {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hJ : Chapter04CoherentIdeal J) :
    (chapter04StrictTransform (J := J) B hJ).ideal =
      chapter04IdealSheafSaturation (J.comap B.morphism) B.exceptionalIdeal := by
  exact (chapter04StrictTransform (J := J) B hJ).ideal_eq_saturation

theorem chapter04_strict_transform_is_affine_saturated
    {X : Scheme.{u}} [IsNoetherian X] {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hJ : Chapter04CoherentIdeal J)
    (U : B.carrier.affineOpens) :
    (chapter04StrictTransform (J := J) B hJ).ideal.ideal U =
      chapter04IdealSaturation
        ((J.comap B.morphism).ideal U) (B.exceptionalIdeal.ideal U) := by
  exact (chapter04StrictTransform (J := J) B hJ).ideal_eq_affine_saturation U

theorem chapter04_strict_transform_support_is_closure
    {X : Scheme.{u}} [IsNoetherian X] {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hJ : Chapter04CoherentIdeal J) :
    ((chapter04StrictTransform (J := J) B hJ).ideal.support : Set B.carrier) =
      closure (B.morphism ⁻¹' ((J.support : Set X) \ (I.support : Set X))) := by
  exact (chapter04StrictTransform (J := J) B hJ).support_is_closure

/- Taking the inverse image without saturation gives the total transform. -/
theorem chapter04_inverse_image_is_total_transform
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04InverseImageIdeal (J := J) B = J.comap B.morphism :=
  rfl

theorem chapter04_strict_transform_removes_exceptional_sections
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) :
    chapter04StrictTransformIdeal (J := J) B =
      chapter04IdealSheafSaturation (chapter04InverseImageIdeal (J := J) B)
        B.exceptionalIdeal := by
  rfl

/-! ### Integral strict transforms -/

structure Chapter04IntegralClosedSubscheme (X : Scheme.{u}) where
  ideal : X.IdealSheafData
  integral : IsIntegral ideal.subscheme

def Chapter04ClosedSubschemeNotContainedInCenter
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (W : Chapter04IntegralClosedSubscheme X) : Prop :=
  ¬ ((W.ideal.support : Set X) ⊆ (I.support : Set X))

structure Chapter04IntegralStrictTransformData
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X) where
  carrier_integral : IsIntegral B.carrier
  transform : Chapter04StrictTransformData (J := W.ideal) B
  integral : IsIntegral transform.ideal.subscheme
  not_contained_in_center :
    Chapter04ClosedSubschemeNotContainedInCenter (I := I) W

theorem chapter04_integral_strict_transform_exists
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X)
    (hB : IsIntegral B.carrier)
    (hW : Chapter04ClosedSubschemeNotContainedInCenter (I := I) W)
    (hJ : Chapter04CoherentIdeal W.ideal)
    :
    Nonempty (Chapter04IntegralStrictTransformData B W) := by
  sorry

noncomputable def chapter04IntegralStrictTransform
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X)
    (hB : IsIntegral B.carrier)
    (hW : Chapter04ClosedSubschemeNotContainedInCenter (I := I) W)
    (hJ : Chapter04CoherentIdeal W.ideal) :
    Chapter04IntegralStrictTransformData B W :=
  Classical.choice (chapter04_integral_strict_transform_exists B W hB hW hJ)

theorem chapter04_integral_strict_transform_is_integral
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (W : Chapter04IntegralClosedSubscheme X)
    (hB : IsIntegral B.carrier)
    (hW : Chapter04ClosedSubschemeNotContainedInCenter (I := I) W)
    (hJ : Chapter04CoherentIdeal W.ideal) :
    IsIntegral (chapter04IntegralStrictTransform B W hB hW hJ).transform.ideal.subscheme := by
  exact (chapter04IntegralStrictTransform B W hB hW hJ).integral

/- The strict transform of a Cartier divisor is again represented by an
effective Cartier divisor under the regular-center hypotheses used in the
transform formula. -/
structure Chapter04StrictTransformCartierData
    {X : Scheme.{u}} {I J : X.IdealSheafData}
    (B : Chapter04Blowup X I) where
  transform : Chapter04StrictTransformData (J := J) B
  divisor : Chapter04EffectiveCartierDivisor B.carrier
  divisor_ideal_eq_transform : divisor.ideal = transform.ideal

structure Chapter04GenericOrderAlongCenter
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (D : Chapter04EffectiveCartierDivisor X) where
  order : ℕ
  genericPoint : X
  genericPoint_is_generic :
    IsGenericPoint genericPoint (I.support : Set X)
  affineOpen : X.affineOpens
  genericPoint_mem_affineOpen : genericPoint ∈ affineOpen.1
  localSection : Γ(X, affineOpen.1)
  local_equation :
    D.ideal.ideal affineOpen = Ideal.span ({localSection} : Set Γ(X, affineOpen.1))
  genericStalkSection : X.presheaf.stalk genericPoint
  genericStalkSection_eq_germ :
    genericStalkSection =
      (X.presheaf.germ affineOpen.1 genericPoint genericPoint_mem_affineOpen).hom localSection
  in_generic_stalk_power :
    genericStalkSection ∈
      (I.ideal affineOpen).map
        (X.presheaf.germ affineOpen.1 genericPoint genericPoint_mem_affineOpen).hom ^ order
  not_in_generic_stalk_next_power :
    genericStalkSection ∉
      (I.ideal affineOpen).map
        (X.presheaf.germ affineOpen.1 genericPoint genericPoint_mem_affineOpen).hom ^ (order + 1)

abbrev Chapter04MultiplicityAlongCenter
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (D : Chapter04EffectiveCartierDivisor X)
    (h : Chapter04GenericOrderAlongCenter I D) : ℕ :=
  h.order

def chapter04DivisorNatMultiple
    {X : Scheme.{u}} (n : ℕ) (D : Chapter04EffectiveCartierDivisor X) :
    Chapter04EffectiveCartierDivisor X :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.EffectiveCartierDivisor.sum
    (fun _ : Fin n => D)

def chapter04DivisorAdd
    {X : Scheme.{u}} (D E : Chapter04EffectiveCartierDivisor X) :
    Chapter04EffectiveCartierDivisor X :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.EffectiveCartierDivisor.add D E

theorem chapter04_divisor_natMultiple_ideal
    {X : Scheme.{u}} (n : ℕ) (D : Chapter04EffectiveCartierDivisor X) :
    (chapter04DivisorNatMultiple n D).ideal = ∏ _ : Fin n, D.ideal := by
  rfl

theorem chapter04_total_transform_decomposition
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hX : IsIntegral X)
    (hX_regular : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y))
    (hY : IsIntegral B.carrier)
    (hcenter : Chapter04IntegralRegularClosedCenter I)
    (D : Chapter04EffectiveCartierDivisor X)
    (hD : Chapter04PullbackIsEffectiveCartier B D)
    (E : Chapter04ExceptionalDivisorData B)
    (T : Chapter04StrictTransformCartierData (J := D.ideal) B)
    (horder : Chapter04GenericOrderAlongCenter I D) :
    (chapter04TotalTransform B hY D hD).ideal =
      (chapter04DivisorAdd T.divisor
        (chapter04DivisorNatMultiple horder.order E.divisor)).ideal := by
  sorry

/- A less dependent form of the same equality is useful to downstream
chapters: the named strict transform and the exceptional divisor are chosen
from their canonical data packages. -/
theorem chapter04_blowup_cartier_transform_formula
    {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
    (B : Chapter04Blowup X I)
    (hX : IsIntegral X)
    (hX_regular : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y))
    (hY : IsIntegral B.carrier)
    (hcenter : Chapter04IntegralRegularClosedCenter I)
    (D : Chapter04EffectiveCartierDivisor X)
    (hD : Chapter04PullbackIsEffectiveCartier B D)
    (E : Chapter04ExceptionalDivisorData B)
    (hD_coherent : Chapter04CoherentIdeal D.ideal)
    (horder : Chapter04GenericOrderAlongCenter I D) :
    ∃ T : Chapter04StrictTransformCartierData (J := D.ideal) B,
      T.transform.ideal = chapter04StrictTransformIdeal (J := D.ideal) B ∧
      (chapter04TotalTransform B hY D hD).ideal =
        (chapter04DivisorAdd
          T.divisor (chapter04DivisorNatMultiple horder.order E.divisor)).ideal := by
  sorry

/-! ### Pointwise order -/

def chapter04OrderAtRegularPoint {R : Type u} [CommRing R]
    [IsLocalRing R] (f : R) : ℕ :=
  sSup {m : ℕ | f ∈ (IsLocalRing.maximalIdeal R) ^ m}

theorem chapter04_orderAtRegularPoint_is_max
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R) (hfinite : ∃ m : ℕ, f ∉ (IsLocalRing.maximalIdeal R) ^ (m + 1)) :
    f ∈ (IsLocalRing.maximalIdeal R) ^ chapter04OrderAtRegularPoint f ∧
      f ∉ (IsLocalRing.maximalIdeal R) ^ (chapter04OrderAtRegularPoint f + 1) := by
  sorry

theorem chapter04_orderAtRegularPoint_characterization
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R) (m : ℕ)
    (hm : f ∈ (IsLocalRing.maximalIdeal R) ^ m)
    (hm_next : f ∉ (IsLocalRing.maximalIdeal R) ^ (m + 1)) :
    chapter04OrderAtRegularPoint f = m := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter04
