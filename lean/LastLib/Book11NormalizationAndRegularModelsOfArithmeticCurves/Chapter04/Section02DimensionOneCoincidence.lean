import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ### 4.2 The dimension-one coincidence -/

/-- The dimension-one hypothesis for a local noetherian domain. -/
def Chapter04OneDimensionalLocalDomain (A : Type u) [CommRing A]
    [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] : Prop :=
  ringKrullDim A = 1

/-- In dimension one, normality gives a discrete valuation ring. -/
theorem chapter04_one_dimensional_local_domain_normal_iff_DVR
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : Chapter04OneDimensionalLocalDomain A) :
    IsIntegrallyClosed A ↔ IsDiscreteValuationRing A := by
  sorry

/-- A one-dimensional noetherian local domain is a DVR exactly when it is regular. -/
theorem chapter04_one_dimensional_local_domain_DVR_iff_regular
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : Chapter04OneDimensionalLocalDomain A) :
    IsDiscreteValuationRing A ↔ IsRegularLocalRing A := by
  sorry

/-- The three standard dimension-one conditions are equivalent. -/
theorem chapter04_one_dimensional_local_domain_normal_DVR_regular
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : Chapter04OneDimensionalLocalDomain A) :
    (IsIntegrallyClosed A ↔ IsDiscreteValuationRing A) ∧
      (IsDiscreteValuationRing A ↔ IsRegularLocalRing A) ∧
      (IsRegularLocalRing A ↔ IsIntegrallyClosed A) := by
  sorry

/-- The regularity predicate used for a curve over a field. -/
def Chapter04RegularCurve (X : Scheme.{u}) : Prop :=
  Chapter04RegularScheme X

/-- The normality predicate used for a curve over a field. -/
def Chapter04NormalCurve (X : Scheme.{u}) : Prop :=
  Chapter04NormalScheme X

/-- A normal noetherian curve over a perfect field is regular. -/
theorem chapter04_normal_curve_over_perfect_field_is_regular
    (k : Type u) [Field k] [PerfectField k]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : Chapter04NormalCurve X)
    (hcurve : ∀ x : X, Order.coheight x ≤ 1) :
    Chapter04RegularCurve X := by
  sorry

/-- A regular finite-presentation curve over a perfect field is smooth. -/
theorem chapter04_regular_curve_over_perfect_field_is_smooth
    (k : Type u) [Field k] [PerfectField k]
    (X : Scheme.{u}) (f : X ⟶ Scheme.Spec (CommRingCat.of k))
    [LocallyOfFinitePresentation f]
    (hregular : Chapter04RegularCurve X) :
    Smooth f := by
  sorry

theorem chapter04_normal_curve_over_perfect_field_is_smooth
    (k : Type u) [Field k] [PerfectField k]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Scheme.Spec (CommRingCat.of k))
    [LocallyOfFinitePresentation f]
    (hnormal : Chapter04NormalCurve X)
    (hcurve : ∀ x : X, Order.coheight x ≤ 1) :
    Smooth f := by
  sorry

/-- Geometric regularity is the property that survives arbitrary field extension. -/
def Chapter04RegularityAfterFieldExtension {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  geometrically Chapter04RegularScheme f

/-- The failure mode separating regularity from smoothness over imperfect fields. -/
def Chapter04RegularButNotGeometricallyRegular {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter04RegularScheme X ∧ ¬ Chapter04RegularityAfterFieldExtension f

def Chapter04RegularButNotSmooth {X S : Scheme.{u}} (f : X ⟶ S)
    (hfp : LocallyOfFinitePresentation f) : Prop :=
  Chapter04RegularScheme X ∧ ¬ Smooth f ∧ ¬ Chapter04RegularityAfterFieldExtension f

/-- Failure of geometric regularity after a specified purely inseparable field extension. -/
def Chapter04PurelyInseparableBaseChangeFailure
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (hpi : IsPurelyInseparable k K)
    {X : Scheme.{u}} (f : X ⟶ Scheme.Spec (CommRingCat.of k))
    (hfp : LocallyOfFinitePresentation f) : Prop :=
  Chapter04RegularScheme X ∧
    ¬ Chapter04RegularScheme
      (pullback f (Scheme.Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- An imperfect field admits a regular curve whose geometric regularity fails. -/
theorem chapter04_regular_need_not_be_smooth_over_imperfect_field :
    ∃ (k : Type u) (hk : Field k),
      letI := hk
      ¬ PerfectField k ∧
        ∃ (X : Scheme.{u}) (f : X ⟶ Scheme.Spec (CommRingCat.of k)),
          ∃ hfp : LocallyOfFinitePresentation f, Chapter04RegularButNotSmooth f hfp := by
  sorry

/-- The obstruction can be witnessed on a purely inseparable field extension. -/
theorem chapter04_regular_curve_purely_inseparable_base_change_can_fail :
    ∃ (k K : Type u) (hk : Field k) (hK : Field K) (hAlg : Algebra k K),
      letI := hk
      letI := hK
      letI := hAlg
      ∃ (hpi : IsPurelyInseparable k K),
        ¬ PerfectField k ∧
          ∃ (X : Scheme.{u})
            (f : X ⟶ Scheme.Spec (CommRingCat.of k)),
            ∃ hfp : LocallyOfFinitePresentation f,
              Chapter04PurelyInseparableBaseChangeFailure k K hpi f hfp := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
