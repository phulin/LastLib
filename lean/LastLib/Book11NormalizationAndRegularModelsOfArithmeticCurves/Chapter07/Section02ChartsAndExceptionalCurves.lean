import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section01TheUniversalRemedyForAnIdeal

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ## 7.2. Charts and exceptional curves -/

/- The ratio charts are represented in the appropriate localization, so the notation does not
introduce an unconstrained polynomial variable. -/
def chapter07RatioSubalgebra
    (A : Type u) [CommRing A] (a b : A) :
    Subalgebra A (Localization.Away a) :=
  Algebra.adjoin A
    ({IsLocalization.mk' (Localization.Away a) b
        (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)} :
      Set (Localization.Away a))

def chapter07FirstRatioChart
    (A : Type u) [CommRing A] (a b : A) : Scheme :=
  Spec (.of (chapter07RatioSubalgebra A a b))

def chapter07SecondRatioChart
    (A : Type u) [CommRing A] (a b : A) : Scheme :=
  Spec (.of (chapter07RatioSubalgebra A b a))

def chapter07FirstRatio
    (A : Type u) [CommRing A] (a b : A) : Localization.Away a :=
  IsLocalization.mk' (Localization.Away a) b
    (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)

def chapter07SecondRatio
    (A : Type u) [CommRing A] (a b : A) : Localization.Away b :=
  IsLocalization.mk' (Localization.Away b) a
    (⟨b, Submonoid.mem_powers _⟩ : Submonoid.powers b)

theorem chapter07_first_ratio_relation
    (A : Type u) [CommRing A] (a b : A) :
    algebraMap A (Localization.Away a) a * chapter07FirstRatio A a b =
      algebraMap A (Localization.Away a) b := by
  sorry

theorem chapter07_second_ratio_relation
    (A : Type u) [CommRing A] (a b : A) :
    algebraMap A (Localization.Away b) b * chapter07SecondRatio A a b =
      algebraMap A (Localization.Away b) a := by
  sorry

structure Chapter07TwoGeneratorBlowupCharts
    (A : Type u) [CommRing A]
    (I : Ideal A) (a b : A) (hI : I = Ideal.span {a, b}) where
  blowup : Chapter07Blowup
    (chapter07AffineCoherentIdeal A I (by sorry))
  firstOpen : blowup.carrier.Opens
  firstAffine : IsAffineOpen firstOpen
  firstIso : firstOpen.toScheme ≅ chapter07FirstRatioChart A a b
  secondOpen : blowup.carrier.Opens
  secondAffine : IsAffineOpen secondOpen
  secondIso : secondOpen.toScheme ≅ chapter07SecondRatioChart A a b
  cover : firstOpen ⊔ secondOpen = ⊤

theorem chapter07_two_generator_blowup_charts
    (A : Type u) [CommRing A]
    (I : Ideal A) (a b : A) (hI : I = Ideal.span {a, b}) :
    Nonempty (Chapter07TwoGeneratorBlowupCharts I a b hI) := by
  sorry

theorem chapter07_two_generator_chart_is_subalgebra_of_localization
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b =
      Algebra.adjoin A
        ({IsLocalization.mk' (Localization.Away a) b
          (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)} :
          Set (Localization.Away a)) :=
  rfl

/-! ### The affine plane example -/

abbrev chapter07PlaneRing (k : Type u) := MvPolynomial (Fin 2) k

def chapter07PlaneX (k : Type u) [CommRing k] : chapter07PlaneRing k :=
  MvPolynomial.X 0

def chapter07PlaneY (k : Type u) [CommRing k] : chapter07PlaneRing k :=
  MvPolynomial.X 1

def chapter07PlaneOriginIdeal (k : Type u) [CommRing k] : Ideal (chapter07PlaneRing k) :=
  Ideal.span {chapter07PlaneX k, chapter07PlaneY k}

def chapter07PlaneFirstChartModel (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

def chapter07PlaneSecondChartModel (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

def chapter07PlaneFirstChartX (k : Type u) [CommRing k] : chapter07PlaneFirstChartModel k :=
  MvPolynomial.X 0

def chapter07PlaneFirstChartT (k : Type u) [CommRing k] : chapter07PlaneFirstChartModel k :=
  MvPolynomial.X 1

def chapter07PlaneFirstChartY (k : Type u) [CommRing k] : chapter07PlaneFirstChartModel k :=
  chapter07PlaneFirstChartX k * chapter07PlaneFirstChartT k

def chapter07PlaneSecondChartS (k : Type u) [CommRing k] : chapter07PlaneSecondChartModel k :=
  MvPolynomial.X 0

def chapter07PlaneSecondChartY (k : Type u) [CommRing k] : chapter07PlaneSecondChartModel k :=
  MvPolynomial.X 1

def chapter07PlaneSecondChartX (k : Type u) [CommRing k] : chapter07PlaneSecondChartModel k :=
  chapter07PlaneSecondChartS k * chapter07PlaneSecondChartY k

theorem chapter07_plane_first_chart_equation (k : Type u) [CommRing k] :
    chapter07PlaneFirstChartY k =
      chapter07PlaneFirstChartX k * chapter07PlaneFirstChartT k :=
  rfl

theorem chapter07_plane_second_chart_equation (k : Type u) [CommRing k] :
    chapter07PlaneSecondChartX k =
      chapter07PlaneSecondChartS k * chapter07PlaneSecondChartY k :=
  rfl

theorem chapter07_plane_first_chart_is_affine_two_variable_ring
    (k : Type u) [Field k] :
    Nonempty (chapter07PlaneFirstChartModel k ≃ₐ[k] MvPolynomial (Fin 2) k) := by
  exact ⟨AlgEquiv.refl _ _⟩

theorem chapter07_plane_second_chart_is_affine_two_variable_ring
    (k : Type u) [Field k] :
    Nonempty (chapter07PlaneSecondChartModel k ≃ₐ[k] MvPolynomial (Fin 2) k) := by
  exact ⟨AlgEquiv.refl _ _⟩

theorem chapter07_plane_first_ratio_chart_is_polynomial_affine
    (k : Type u) [Field k] :
    Nonempty
      (chapter07FirstRatioChart (chapter07PlaneRing k) (chapter07PlaneX k) (chapter07PlaneY k) ≅
        Spec (.of (chapter07PlaneFirstChartModel k))) := by
  sorry

theorem chapter07_plane_second_ratio_chart_is_polynomial_affine
    (k : Type u) [Field k] :
    Nonempty
      (chapter07SecondRatioChart (chapter07PlaneRing k) (chapter07PlaneX k) (chapter07PlaneY k) ≅
        Spec (.of (chapter07PlaneSecondChartModel k))) := by
  sorry

noncomputable def chapter07PlaneOriginPoint
    (k : Type u) [Field k] : Spec (.of (chapter07PlaneRing k)) := by
  sorry

noncomputable def chapter07PlaneBlowup
    (k : Type u) [Field k] :
    Chapter07Blowup
      (chapter07AffineCoherentIdeal (chapter07PlaneRing k)
        (chapter07PlaneOriginIdeal k) (by sorry)) :=
  chapter07Blowup _

def chapter07PlaneExceptionalFiber (k : Type u) [Field k] : Scheme :=
  (chapter07PlaneBlowup k).projection.fiber (chapter07PlaneOriginPoint k)

theorem chapter07_plane_origin_exceptional_fiber_is_projective_line
    (k : Type u) [Field k] :
    Nonempty
      (chapter07PlaneExceptionalFiber k ≅ chapter04ProjectiveLine k) := by
  sorry

/-! ### Regular surfaces and residue-field forms of the exceptional curve -/

noncomputable def chapter07PointIdeal {X : Scheme.{u}} (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.singleton x)

theorem chapter07_blowup_of_regular_surface_at_regular_point_is_regular
    {X : Scheme.{u}} (hX : Chapter07RegularSurface X) (x : X)
    (hx : Chapter07ClosedRegularPoint x)
    (I : Chapter07CoherentIdeal X)
    (hI : I.ideal = chapter07PointIdeal x) :
    Chapter07RegularSurface (chapter07Blowup I).carrier := by
  sorry

def chapter07FirstChartParameterA
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b :=
  algebraMap A _ a

def chapter07FirstChartParameterB
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b :=
  algebraMap A _ b

def chapter07FirstChartParameterT
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A a b :=
  ⟨chapter07FirstRatio A a b,
    Algebra.subset_adjoin (Set.mem_singleton (chapter07FirstRatio A a b))⟩

theorem chapter07_first_chart_parameter_relation
    (A : Type u) [CommRing A] (a b : A) :
    chapter07FirstChartParameterA A a b * chapter07FirstChartParameterT A a b =
      chapter07FirstChartParameterB A a b := by
  sorry

def chapter07SecondChartParameterA
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A b a :=
  algebraMap A _ a

def chapter07SecondChartParameterB
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A b a :=
  algebraMap A _ b

def chapter07SecondChartParameterS
    (A : Type u) [CommRing A] (a b : A) :
    chapter07RatioSubalgebra A b a :=
  ⟨chapter07SecondRatio A a b,
    Algebra.subset_adjoin (Set.mem_singleton (chapter07SecondRatio A a b))⟩

theorem chapter07_second_chart_parameter_relation
    (A : Type u) [CommRing A] (a b : A) :
    chapter07SecondChartParameterB A a b * chapter07SecondChartParameterS A a b =
      chapter07SecondChartParameterA A a b := by
  sorry

def chapter07ExceptionalCurveAtPoint
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) (x : X) : Scheme :=
  B.projection.fiber x

theorem chapter07_exceptional_curve_is_projective_line_over_residue_field
    {X : Scheme.{u}} (hX : Chapter07RegularSurface X) (x : X)
    (hx : Chapter07ClosedRegularPoint x)
    (I : Chapter07CoherentIdeal X)
    (hI : I.ideal = chapter07PointIdeal x) :
    Nonempty
      (chapter07ExceptionalCurveAtPoint (chapter07Blowup I) x ≅
        chapter04ProjectiveLine (X.residueField x)) := by
  sorry

def chapter07ExceptionalDirection
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) (x : X) :=
  (chapter07ExceptionalCurveAtPoint B x).carrier

theorem chapter07_exceptional_curve_records_tangent_directions
    {X : Scheme.{u}} (hX : Chapter07RegularSurface X) (x : X)
    (hx : Chapter07ClosedRegularPoint x)
    (I : Chapter07CoherentIdeal X)
    (hI : I.ideal = chapter07PointIdeal x) :
    Nonempty
      (chapter07ExceptionalDirection (chapter07Blowup I) x ≃ₜ
        (chapter04ProjectiveLine (X.residueField x)).carrier) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
