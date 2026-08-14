import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ### 4.1 Depth and codimension -/

/-- Serre's `(R1)` and `(S2)` conditions bundled for the canonical depth. -/
def Chapter04SerreConditions (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  Chapter04R1 A ∧ Chapter04S2 A

/-- Cohen--Macaulayness expressed through the canonical depth. -/
def Chapter04CohenMacaulay (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (p : Ideal A) (hp : p.IsPrime),
    letI := hp
    Chapter04Depth (Localization.AtPrime p) = ringKrullDim (Localization.AtPrime p)

theorem chapter04_cohenMacaulay_implies_S2
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hCM : Chapter04CohenMacaulay A) :
    Chapter04S2 A := by
  sorry

/-- Serre's criterion for a noetherian ring. -/
theorem chapter04_serre_criterion
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    : Chapter04NormalRing A ↔ IsReduced A ∧ Chapter04SerreConditions A := by
  sorry

/-- Domain form of Serre's criterion, where the fraction field is available. -/
theorem chapter04_serre_criterion_domain
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    : IsIntegrallyClosed A ↔ IsReduced A ∧ Chapter04SerreConditions A := by
  sorry

/-- A regular integral locally noetherian scheme is normal. -/
theorem chapter04_regular_integral_scheme_is_normal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hregular : Chapter04RegularScheme X) :
    Chapter04NormalScheme X := by
  sorry

/-- A noetherian normal local domain of dimension at least two has depth at least two. -/
theorem chapter04_normal_local_domain_depth_ge_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hnormal : IsIntegrallyClosed A)
    (hmax : (IsLocalRing.maximalIdeal A).IsPrime)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    Chapter04Depth A ≥ (2 : WithBot ℕ∞) := by
  sorry

/-- A height-one noetherian normal local domain is a discrete valuation ring. -/
theorem chapter04_height_one_normal_local_isDVR
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (hnormal : IsIntegrallyClosed A)
    (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A := by
  sorry

/-- The height-one localizations of a normal noetherian domain are DVRs. -/
theorem chapter04_normal_domain_height_one_localizations_are_DVRs
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hnormal : IsIntegrallyClosed A)
    (p : Ideal A) (hp : p.IsPrime)
    (hheight : p.height = 1) :
    letI := hp
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  sorry

/-- An S2 noetherian domain satisfies the height-one intersection property. -/
theorem chapter04_height_one_intersection_of_S2
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hS2 : Chapter04S2 A) :
    Chapter04HeightOneIntersection A := by
  sorry

/-- An element integral over a domain lies in every height-one localization. -/
theorem chapter04_integral_mem_height_one_localization
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hR1 : Chapter04R1 A)
    {x : FractionRing A} (hx : IsIntegral A x)
    (p : Ideal A) (hp : p.IsPrime) (hheight : p.height = 1) :
    Chapter04MemHeightOneLocalization x p hp := by
  sorry

/-- The height-one intersection property forces integral closedness. -/
theorem chapter04_height_one_intersection_integrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hR1 : Chapter04R1 A)
    (hinter : Chapter04HeightOneIntersection A) :
    IsIntegrallyClosed A := by
  sorry

/-- Normality on a noetherian surface forces the nonregular locus into codimension two. -/
def Chapter04NonRegularLocusCodimensionAtLeastTwo (X : Scheme.{u}) : Prop :=
  ∀ x : X, x ∈ Chapter04NonRegularLocus X → 2 ≤ Order.coheight x

theorem chapter04_normal_surface_nonregular_locus_codim_ge_two
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : Chapter04NormalScheme X)
    (hsurface : Chapter04NoetherianSurface X) :
    Chapter04NonRegularLocusCodimensionAtLeastTwo X := by
  sorry

def Chapter04ClosedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsClosed ({x} : Set X)

theorem chapter04_normal_surface_nonregular_points_are_closed
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (hnormal : Chapter04NormalScheme X)
    (hsurface : Chapter04NoetherianSurface X) :
    ∀ x : X, x ∈ Chapter04NonRegularLocus X → Chapter04ClosedPoint X x := by
  sorry

/-- Excellence makes the singular locus closed in the form needed here. -/
theorem chapter04_excellence_closes_singular_locus
    (X : Scheme.{u}) [Chapter04ExcellenceProfile X] :
    IsClosed (Chapter04NonRegularLocus X) := by
  sorry

/-- On a quasi-compact noetherian surface, no singular curve leaves finitely many singular points. -/
theorem chapter04_quasiCompact_surface_singular_locus_finite
    (X : Scheme.{u}) [Chapter04ExcellenceProfile X]
    (hsurface : Chapter04NoetherianSurface X)
    (hqc : IsCompact (Set.univ : Set X))
    (hnoCurve : Chapter04SingularLocusContainsNoCurve X) :
    (Chapter04NonRegularLocus X).Finite := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
