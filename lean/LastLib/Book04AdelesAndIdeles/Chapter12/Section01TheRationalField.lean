import LastLib.Book04AdelesAndIdeles.Chapter12.Core

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Filter Set NumberField
open scoped BigOperators NNReal RestrictedProduct

/-! # Book 4, Chapter 12, §12.1: The rational field -/

/-- The single real-place portrait of the rational infinite adele ring. -/
structure Chapter12RationalInfinitePortrait where
  equiv : chapter12InfiniteAdeleRing ℚ ≃+* ℝ

theorem chapter12_rational_has_one_real_place :
    Nonempty Chapter12RationalInfinitePortrait := by
  sorry

/-- The finite rational adeles written as the canonical restricted product over `ℤ`. -/
abbrev chapter12RationalFiniteRestrictedProduct :=
  Πʳ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]

theorem chapter12_rational_finite_adele_restricted_product :
    Nonempty (chapter12RationalFiniteAdeleRing ≃+*
      chapter12RationalFiniteRestrictedProduct) := by
  exact ⟨RingEquiv.refl _⟩

theorem chapter12_rational_finite_places_are_prime_indexed :
    Nonempty (IsDedekindDomain.HeightOneSpectrum ℤ ≃ Nat.Primes) := by
  sorry

theorem chapter12_rational_ideles_split_into_infinite_and_finite_units :
    Nonempty (chapter12RationalIdeles ≃*
      (chapter12InfiniteAdeleRing ℚ)ˣ × chapter12RationalFiniteIdeles) := by
  sorry

/-- The displayed product portrait of the rational adele ring. -/
def chapter12RationalAdeleProductPortrait
    (P : Chapter12RationalInfinitePortrait) :
    chapter12RationalAdeleRing ≃+*
      ℝ × chapter12RationalFiniteRestrictedProduct :=
  RingEquiv.prodCongr P.equiv (RingEquiv.refl _)

theorem chapter12_rational_adele_ring_product_portrait :
    Nonempty (chapter12RationalAdeleRing ≃+*
      ℝ × chapter12RationalFiniteRestrictedProduct) := by
  obtain ⟨P⟩ := chapter12_rational_has_one_real_place
  exact ⟨chapter12RationalAdeleProductPortrait P⟩

/-- The rational profinite integral coordinates embedded in the finite adeles. -/
def chapter12RationalIntegralFiniteAdeleSet :
    Set chapter12RationalFiniteAdeleRing :=
  {x | ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    x v ∈ v.adicCompletionIntegers ℚ}

theorem chapter12_rational_integral_finite_adele_iff
    (x : chapter12RationalFiniteAdeleRing) :
    x ∈ chapter12RationalIntegralFiniteAdeleSet ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        x v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

/-- The closed additive fundamental set `[0,1] × Ẑ` in the rational portrait. -/
def chapter12RationalAdditiveFundamentalSet
    (P : Chapter12RationalInfinitePortrait) :
    Set chapter12RationalAdeleRing :=
  {x | P.equiv x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    x.2 ∈ chapter12RationalIntegralFiniteAdeleSet}

/-- Strong approximation gives the stated additive cover. -/
theorem chapter12_rational_additive_fundamental_set_covers
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalAdeleRing) :
    ∃ q : ℚ, x - algebraMap ℚ chapter12RationalAdeleRing q ∈
      chapter12RationalAdditiveFundamentalSet P := by
  sorry

/-- The rational additive quotient by diagonal principal adeles. -/
abbrev chapter12RationalAdditiveQuotient :=
  chapter12RationalAdeleRing ⧸ NumberField.AdeleRing.principalSubgroup ℤ ℚ

def chapter12RationalAdditiveQuotientMk :
    chapter12RationalAdeleRing →+ chapter12RationalAdditiveQuotient :=
  QuotientAddGroup.mk'
    (NumberField.AdeleRing.principalSubgroup ℤ ℚ)

theorem chapter12_rational_additive_quotient_is_covered
    (P : Chapter12RationalInfinitePortrait) :
    ∀ c : chapter12RationalAdditiveQuotient,
      ∃ x ∈ chapter12RationalAdditiveFundamentalSet P,
        chapter12RationalAdditiveQuotientMk x = c := by
  sorry

/-! ## Valuation normalization of rational ideles -/

abbrev Chapter12RationalPrime := {p : ℕ // p.Prime}

/- The integer-valued exponent read from a finite rational-idele coordinate. -/
def chapter12RationalFiniteValuationExponent
    (x : chapter12RationalIdeles) (p : Chapter12RationalPrime) : ℤ :=
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
  let z := Valued.v (x.1.2 v)
  if hz : z = 0 then 0 else -(WithZero.unzero hz).toAdd

/- A finite valuation profile is the precise finite-product datum in the text. -/
structure Chapter12RationalValuationProfile where
  exponent : Chapter12RationalPrime → ℤ
  support : Finset Chapter12RationalPrime
  support_spec : ∀ p, p ∉ support → exponent p = 0

namespace Chapter12RationalValuationProfile

/-- The positive rational number obtained from a finite valuation profile. -/
def q (a : Chapter12RationalValuationProfile) : ℚ :=
  Finset.prod a.support (fun p => (p.1 : ℚ) ^ a.exponent p)

theorem q_pos (a : Chapter12RationalValuationProfile) : 0 < a.q := by
  sorry

@[simp]
theorem q_def (a : Chapter12RationalValuationProfile) :
    a.q = Finset.prod a.support (fun p => (p.1 : ℚ) ^ a.exponent p) :=
  rfl

end Chapter12RationalValuationProfile

/-- The finite component of an idele after division by a rational scalar. -/
def chapter12RationalFinitePartAfterDivision
    (x : chapter12RationalIdeles) (q : ℚ) :
    chapter12RationalFiniteAdeleRing :=
  x.1.2 * algebraMap ℚ (chapter12FiniteAdeleRing ℤ ℚ) q⁻¹

/-- All finite coordinates are units after the indicated scalar division. -/
def chapter12RationalFinitePartIsUnit
    (x : chapter12RationalIdeles) (q : ℚ) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    IsUnit (chapter12RationalFinitePartAfterDivision x q v)

/-- The real coordinate of a rational idele in a chosen one-place portrait. -/
def chapter12RationalRealCoordinate
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) : ℝ :=
  P.equiv x.1.1

structure Chapter12RationalIdeleNormalization
    (x : chapter12RationalIdeles) where
  profile : Chapter12RationalValuationProfile
  profile_matches_idele :
    ∀ p, profile.exponent p = chapter12RationalFiniteValuationExponent x p
  finite_unit_after_division :
    chapter12RationalFinitePartIsUnit x profile.q
  real_coordinate_ne_zero :
    ∀ P : Chapter12RationalInfinitePortrait,
      chapter12RationalRealCoordinate P x ≠ 0

theorem chapter12_rational_idele_has_finite_valuation_normalization
    (x : chapter12RationalIdeles) :
    Nonempty (Chapter12RationalIdeleNormalization x) := by
  sorry

theorem chapter12_rational_normalization_scalar_is_positive
    {x : chapter12RationalIdeles}
    (N : Chapter12RationalIdeleNormalization x) :
    0 < N.profile.q :=
  Chapter12RationalValuationProfile.q_pos N.profile

/-- The positive real coordinate after removing the finite valuation profile. -/
def chapter12RationalNormalizedRealCoordinate
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) (q : ℚ) : ℝ :=
  |chapter12RationalRealCoordinate P x| / (q : ℝ)

/-- The extra principal sign correction used to make the real coordinate positive. -/
def chapter12RationalSignCorrectedNormalizer (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) (q : ℚ) : ℚ :=
  if 0 ≤ chapter12RationalRealCoordinate P x / (q : ℝ) then q else -q

theorem chapter12_rational_normalized_real_coordinate_pos
    (P : Chapter12RationalInfinitePortrait)
    (x : chapter12RationalIdeles) (q : ℚ) (hq : 0 < q)
    (hx : chapter12RationalRealCoordinate P x ≠ 0) :
    0 < chapter12RationalNormalizedRealCoordinate P x q := by
  sorry

theorem chapter12_rational_finite_coordinates_become_units
    (x : chapter12RationalIdeles) (q : ℚ)
    (hfinite : chapter12RationalFinitePartIsUnit x q) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      IsUnit (chapter12RationalFinitePartAfterDivision x q v) := by
  exact hfinite

/-! ## The rational idele class portraits -/

/-- A finite-place unit coordinate in the rational finite ideles. -/
def chapter12RationalFiniteUnitCoordinates :
    Set chapter12RationalFiniteIdeles :=
  {x | ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    ∃ u : (v.adicCompletionIntegers ℚ)ˣ,
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) u = x.1 v}

theorem chapter12_rational_finite_unit_coordinates_iff
    (x : chapter12RationalFiniteIdeles) :
    x ∈ chapter12RationalFiniteUnitCoordinates ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        ∃ u : (v.adicCompletionIntegers ℚ)ˣ,
          algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) u = x.1 v :=
  Iff.rfl

abbrev chapter12RationalClassTarget :=
  ℝ≥0ˣ × chapter12RationalProfiniteUnitGroup

structure Chapter12RationalClassPortrait
    (M : Chapter12IdeleModuleData ℤ ℚ) where
  equivalence : chapter12IdeleClassGroup ℤ ℚ ≃* chapter12RationalClassTarget
  first_coordinate_is_module :
    ∀ x : chapter12RationalIdeles,
      (equivalence (chapter12IdeleClassMk ℤ ℚ x)).1 =
        chapter12IdeleModuleUnit M x

theorem chapter12_rational_finite_coordinate_is_profinite_unit
    (M : Chapter12IdeleModuleData ℤ ℚ)
    (P : Chapter12RationalClassPortrait M)
    (x : chapter12RationalIdeles) :
    ∃ u : chapter12RationalProfiniteUnitGroup,
      (P.equivalence (chapter12IdeleClassMk ℤ ℚ x)).2 = u := by
  exact ⟨_, rfl⟩

theorem chapter12_rational_idele_class_group_portrait
    (M : Chapter12IdeleModuleData ℤ ℚ) :
    Nonempty (Chapter12RationalClassPortrait M) := by
  sorry

abbrev chapter12RationalNormOneClassCarrier
    (M : Chapter12IdeleModuleData ℤ ℚ) :=
  {c : chapter12IdeleClassGroup ℤ ℚ // c ∈ chapter12NormOneIdeleClasses M}

theorem chapter12_rational_norm_one_class_group_portrait
    (M : Chapter12IdeleModuleData ℤ ℚ) :
    Nonempty (chapter12RationalNormOneClassCarrier M ≃
      chapter12RationalProfiniteUnitGroup) := by
  sorry

def chapter12RationalGlobalUnitValues : Set ℤ :=
  {1, -1}

theorem chapter12_rational_global_units_are_signs :
    Set.range (fun u : ℤˣ => (u : ℤ)) = chapter12RationalGlobalUnitValues := by
  sorry

/-! ## Rational ray class quotients -/

def chapter12RationalRaySignSubgroup (N : ℕ) : Subgroup (ZMod N)ˣ :=
  Subgroup.closure ({(1 : (ZMod N)ˣ), (-1 : (ZMod N)ˣ)} : Set (ZMod N)ˣ)

abbrev chapter12RationalRayClassWithInfinity (N : ℕ) := (ZMod N)ˣ

abbrev chapter12RationalRayClassWithoutInfinity (N : ℕ) :=
  (ZMod N)ˣ ⧸ chapter12RationalRaySignSubgroup N

theorem chapter12_rational_ray_class_group_with_infinity
    (N : ℕ) (_hN : 0 < N) :
    Nonempty (chapter12RationalRayClassWithInfinity N ≃*
      (ZMod N)ˣ) := by
  exact ⟨MulEquiv.refl _⟩

theorem chapter12_rational_ray_class_group_without_infinity
    (N : ℕ) (_hN : 0 < N) :
    Nonempty (chapter12RationalRayClassWithoutInfinity N ≃*
      (ZMod N)ˣ ⧸ chapter12RationalRaySignSubgroup N) := by
  exact ⟨MulEquiv.refl _⟩

end
end LastLib.Book04AdelesAndIdeles.Chapter12
