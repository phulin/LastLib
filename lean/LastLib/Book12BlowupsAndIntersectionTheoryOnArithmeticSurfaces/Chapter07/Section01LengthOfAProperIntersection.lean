import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07

universe u

/-- In a two-dimensional regular local ring, parameters cut out an Artinian quotient. -/
theorem chapter07_regular_surface_is_cohenMacaulay
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A) :
    Chapter07CohenMacaulaySurfaceCriterion A := by
  sorry

/-- No common one-dimensional component through a closed point forces the two equations to be
m-primary, hence to have zero-dimensional support. -/
theorem chapter07_mprimary_of_no_common_curve_component
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07PassesThrough C) (hD : Chapter07PassesThrough D)
    (hCD : Chapter07NoCommonCurveComponentAt C D) :
    Chapter07MPrimaryIntersection C D := by
  sorry

/-- The two local equations form the regular sequence underlying the length
calculation. -/
theorem chapter07_intersection_equations_are_regular_sequence
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07PassesThrough C) (hD : Chapter07PassesThrough D)
    (hCD : Chapter07ProperIntersectionAt C D) :
    RingTheory.Sequence.IsRegular A [C.equation, D.equation] := by
  sorry

theorem chapter07_proper_intersection_at_of_no_common_curve_component
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07PassesThrough C) (hD : Chapter07PassesThrough D)
    (hCD : Chapter07NoCommonCurveComponentAt C D) :
    Chapter07ProperIntersectionAt C D := by
  sorry

/-- A proper local intersection has finite module length. -/
theorem chapter07_proper_intersection_quotient_is_artinian
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hCD : Chapter07ProperIntersectionAt C D) :
    IsArtinianRing (A ⧸ Chapter07IntersectionIdeal C D) := by
  sorry

theorem chapter07_proper_intersection_quotient_has_zero_dimension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07PassesThrough C) (hD : Chapter07PassesThrough D)
    (hCD : Chapter07ProperIntersectionAt C D) :
    ringKrullDim (A ⧸ Chapter07IntersectionIdeal C D) = (0 : WithBot ℕ∞) := by
  sorry

theorem chapter07_local_intersection_multiplicity_ne_top
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hCD : Chapter07ProperIntersectionAt C D) :
    Chapter07LocalIntersectionMultiplicity C D ≠ ⊤ := by
  sorry

/-- Formula (7.1), with Mathlib's canonical module length as the target. -/
theorem chapter07_local_intersection_formula
    {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) :
    Chapter07LocalIntersectionMultiplicity C D =
      Module.length A (Chapter07SchemeTheoreticIntersectionRing C D) := by
  rfl

/-- The quotient in (7.1) is the local scheme-theoretic intersection. -/
theorem chapter07_scheme_theoretic_intersection_ring
    {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) :
    Chapter07SchemeTheoreticIntersectionRing C D =
      (A ⧸ Chapter07IntersectionIdeal C D) := by
  rfl

/-- Properness identifies the `ℕ`-valued presentation with the canonical `ℕ∞` length. -/
theorem chapter07_local_intersection_number_cast
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hCD : Chapter07ProperIntersectionAt C D) :
    (Chapter07LocalIntersectionNumber C D : ℕ∞) =
      Chapter07LocalIntersectionMultiplicity C D := by
  sorry

/-- Replacing a local equation by an associated equation does not change the intersection ideal. -/
theorem chapter07_intersection_ideal_eq_of_associated_left
    {A : Type u} [CommRing A]
    (C C' D : Chapter07LocalEffectiveCartierCurve A)
    (h : Associated C.equation C'.equation) :
    Chapter07IntersectionIdeal C D = Chapter07IntersectionIdeal C' D := by
  sorry

theorem chapter07_intersection_ideal_eq_of_associated_right
    {A : Type u} [CommRing A]
    (C D D' : Chapter07LocalEffectiveCartierCurve A)
    (h : Associated D.equation D'.equation) :
    Chapter07IntersectionIdeal C D = Chapter07IntersectionIdeal C D' := by
  sorry

/-- Unit changes of either Cartier equation leave the local length unchanged. -/
theorem chapter07_local_intersection_multiplicity_eq_of_associated_left
    {A : Type u} [CommRing A]
    (C C' D : Chapter07LocalEffectiveCartierCurve A)
    (h : Associated C.equation C'.equation) :
    Chapter07LocalIntersectionMultiplicity C D =
      Chapter07LocalIntersectionMultiplicity C' D := by
  sorry

theorem chapter07_local_intersection_multiplicity_eq_of_associated_right
    {A : Type u} [CommRing A]
    (C D D' : Chapter07LocalEffectiveCartierCurve A)
    (h : Associated D.equation D'.equation) :
    Chapter07LocalIntersectionMultiplicity C D =
      Chapter07LocalIntersectionMultiplicity C D' := by
  sorry

/-- The formal group of signed local Cartier divisors. -/
abbrev Chapter07SignedLocalCartierDivisor (A : Type u) [CommRing A] :=
  Chapter07LocalEffectiveCartierCurve A →₀ ℤ

/-- Supportwise properness for a pair of signed divisors. -/
noncomputable def Chapter07ProperSignedPair
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D E : Chapter07SignedLocalCartierDivisor A) : Prop := by
  classical
  exact ∀ C ∈ D.support, ∀ C' ∈ E.support, Chapter07ProperIntersectionAt C C'

/-- Bilinear extension of local intersection from effective terms to signed divisors. -/
noncomputable def Chapter07SignedLocalIntersection
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D E : Chapter07SignedLocalCartierDivisor A) : ℤ := by
  classical
  exact ∑ C ∈ D.support, ∑ C' ∈ E.support,
    (D C) * (E C') * Int.ofNat (Chapter07LocalIntersectionNumber C C')

theorem chapter07_signed_local_intersection_add_left
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D₁ D₂ E : Chapter07SignedLocalCartierDivisor A)
    (h : Chapter07ProperSignedPair (D₁ + D₂) E) :
    Chapter07SignedLocalIntersection (D₁ + D₂) E =
      Chapter07SignedLocalIntersection D₁ E + Chapter07SignedLocalIntersection D₂ E := by
  sorry

theorem chapter07_signed_local_intersection_add_right
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (D E₁ E₂ : Chapter07SignedLocalCartierDivisor A)
    (h : Chapter07ProperSignedPair D (E₁ + E₂)) :
    Chapter07SignedLocalIntersection D (E₁ + E₂) =
      Chapter07SignedLocalIntersection D E₁ + Chapter07SignedLocalIntersection D E₂ := by
  sorry

theorem chapter07_local_intersection_multiplicity_comm
    {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) :
    Chapter07LocalIntersectionMultiplicity C D =
      Chapter07LocalIntersectionMultiplicity D C := by
  sorry

/-- Product of local equations, representing the sum of effective Cartier curves. -/
def Chapter07SumOfEffectiveCurves
    {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) :
    Chapter07LocalEffectiveCartierCurve A :=
  { equation := C.equation * D.equation
    equation_is_regular := by sorry }

@[simp]
theorem chapter07_sum_of_effective_curves_equation
    {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) :
    (Chapter07SumOfEffectiveCurves C D).equation = C.equation * D.equation :=
  rfl

/-- Additivity in the second divisor, as in the exact sequence on `A/(f)`. -/
theorem chapter07_local_intersection_multiplicity_add_right
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D₁ D₂ : Chapter07LocalEffectiveCartierCurve A)
    (h₁ : Chapter07ProperIntersectionAt C D₁)
    (h₂ : Chapter07ProperIntersectionAt C D₂)
    (h₁₂ : Chapter07ProperIntersectionAt C (Chapter07SumOfEffectiveCurves D₁ D₂)) :
    Chapter07LocalIntersectionMultiplicity C (Chapter07SumOfEffectiveCurves D₁ D₂) =
      Chapter07LocalIntersectionMultiplicity C D₁ +
        Chapter07LocalIntersectionMultiplicity C D₂ := by
  sorry

theorem chapter07_local_intersection_multiplicity_add_left
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C₁ C₂ D : Chapter07LocalEffectiveCartierCurve A)
    (h₁ : Chapter07ProperIntersectionAt C₁ D)
    (h₂ : Chapter07ProperIntersectionAt C₂ D)
    (h₁₂ : Chapter07ProperIntersectionAt
      (Chapter07SumOfEffectiveCurves C₁ C₂) D) :
    Chapter07LocalIntersectionMultiplicity
        (Chapter07SumOfEffectiveCurves C₁ C₂) D =
      Chapter07LocalIntersectionMultiplicity C₁ D +
        Chapter07LocalIntersectionMultiplicity C₂ D := by
  sorry

/-- The symmetric version of the local intersection number. -/
theorem chapter07_local_intersection_number_comm
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hCD : Chapter07ProperIntersectionAt C D) :
    Chapter07LocalIntersectionNumber C D = Chapter07LocalIntersectionNumber D C := by
  sorry

/-! ### Adapter laws for later divisor-level theories

The later arithmetic-surface chapters work with their own signed divisor and
point types.  This interface keeps the Chapter 7 content reusable without
importing those later chapters: a concrete instance supplies the local module
length and Tor Euler characteristic, while the laws below expose the
symmetry, additivity, and positivity needed by the divisor-level API.
-/

class Chapter07LocalIntersectionTheoryAdapter
    (Divisor P : Type u) [AddCommGroup Divisor]
    (noCommon : Divisor → Divisor → Prop)
    (effective : Divisor → Prop)
    (passesThrough : Divisor → P → Prop) where
  localIntersection :
    ∀ (D G : Divisor), noCommon D G → P → ℤ
  symmetric :
    ∀ (D G : Divisor) (h : noCommon D G) (h' : noCommon G D) (p : P),
      localIntersection D G h p = localIntersection G D h' p
  moduleLength :
    ∀ (C G : Divisor), effective C → effective G → noCommon C G → P → ℕ∞
  torEulerCharacteristic :
    ∀ (C G : Divisor), effective C → effective G → noCommon C G → P → ℤ
  moduleLength_eq_torEulerCharacteristic :
    ∀ (C G : Divisor) (hC : effective C) (hG : effective G)
      (h : noCommon C G) (p : P),
      torEulerCharacteristic C G hC hG h p =
        Int.ofNat (moduleLength C G hC hG h p).toNat
  localIntersection_eq_moduleLength :
    ∀ (C G : Divisor) (hC : effective C) (hG : effective G)
      (h : noCommon C G) (p : P),
      localIntersection C G h p =
        Int.ofNat (moduleLength C G hC hG h p).toNat
  localIntersection_eq_torEulerCharacteristic :
    ∀ (C G : Divisor) (hC : effective C) (hG : effective G)
      (h : noCommon C G) (p : P),
      localIntersection C G h p = torEulerCharacteristic C G hC hG h p
  add_left :
    ∀ (D₁ D₂ G : Divisor) (h₁ : noCommon D₁ G) (h₂ : noCommon D₂ G)
      (h₁₂ : noCommon (D₁ + D₂) G) (p : P),
      localIntersection (D₁ + D₂) G h₁₂ p =
        localIntersection D₁ G h₁ p + localIntersection D₂ G h₂ p
  add_right :
    ∀ (D E₁ E₂ : Divisor) (h₁ : noCommon D E₁) (h₂ : noCommon D E₂)
      (h₁₂ : noCommon D (E₁ + E₂)) (p : P),
      localIntersection D (E₁ + E₂) h₁₂ p =
        localIntersection D E₁ h₁ p + localIntersection D E₂ h₂ p
  positive_iff :
    ∀ (C G : Divisor) (_hC : effective C) (_hG : effective G)
      (h : noCommon C G) (p : P),
      0 < localIntersection C G h p ↔
        passesThrough C p ∧ passesThrough G p

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
