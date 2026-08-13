import LastLib.Book04AdelesAndIdeles.Chapter12.Core

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Set
open scoped BigOperators nonZeroDivisors

/-! # Book 4, Chapter 12, §12.4: A nonprincipal ideal as an idele -/

abbrev chapter12MinusFiveIntegers := Zsqrtd (-5)

abbrev chapter12MinusFiveField := FractionRing chapter12MinusFiveIntegers

def chapter12MinusFiveSqrt : chapter12MinusFiveIntegers :=
  Zsqrtd.sqrtd

def chapter12MinusFiveIdeal : Ideal chapter12MinusFiveIntegers :=
  Ideal.span ({(2 : chapter12MinusFiveIntegers),
    1 + chapter12MinusFiveSqrt} : Set chapter12MinusFiveIntegers)

def chapter12MinusFiveNormForm (a b : ℤ) : ℤ :=
  a ^ 2 + 5 * b ^ 2

theorem chapter12_minus_five_norm_form_formula (a b : ℤ) :
    chapter12MinusFiveNormForm a b = a ^ 2 + 5 * b ^ 2 :=
  rfl

theorem chapter12_minus_five_norm_form_ne_two (a b : ℤ) :
    chapter12MinusFiveNormForm a b ≠ 2 := by
  sorry

theorem chapter12_minus_five_ideal_norm_two
    [IsDedekindDomain chapter12MinusFiveIntegers]
    [Module.Free ℤ chapter12MinusFiveIntegers] :
    Ideal.absNorm chapter12MinusFiveIdeal = 2 := by
  sorry

theorem chapter12_minus_five_ideal_square
    [IsDedekindDomain chapter12MinusFiveIntegers] :
    chapter12MinusFiveIdeal ^ 2 =
      Ideal.span ({(2 : chapter12MinusFiveIntegers)} : Set chapter12MinusFiveIntegers) := by
  sorry

theorem chapter12_minus_five_ideal_is_not_principal :
    ¬chapter12MinusFiveIdeal.IsPrincipal := by
  sorry

def chapter12MinusFiveIdealClassOrderTwo : Prop :=
  chapter12MinusFiveIdeal ^ 2 =
      Ideal.span ({(2 : chapter12MinusFiveIntegers)} : Set chapter12MinusFiveIntegers) ∧
    ¬chapter12MinusFiveIdeal.IsPrincipal

theorem chapter12_minus_five_ideal_represents_nontrivial_order_two_class
    [IsDedekindDomain chapter12MinusFiveIntegers] :
    chapter12MinusFiveIdealClassOrderTwo := by
  exact ⟨chapter12_minus_five_ideal_square, chapter12_minus_five_ideal_is_not_principal⟩

theorem chapter12_minus_five_class_group_element_has_order_two
    [IsDedekindDomain chapter12MinusFiveIntegers]
    (hI₀ : chapter12MinusFiveIdeal ∈
      (Ideal chapter12MinusFiveIntegers)⁰) :
    let c := ClassGroup.mk0 ⟨chapter12MinusFiveIdeal, hI₀⟩
    c ^ 2 = 1 ∧ c ≠ 1 := by
  sorry

/-! ## The single-place finite idele -/

structure Chapter12SinglePlaceFiniteIdele
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (π : p.adicCompletionIntegers K) where
  x : chapter12FiniteIdeles R K
  uniformizer : chapter12UniformizerAt p π
  value_at : x.1 p = (π : p.adicCompletion K)
  value_away : ∀ v, v ≠ p → x.1 v = 1
  ideal_eq : D.idealOf x = (p.asIdeal : FractionalIdeal R⁰ K)

theorem chapter12_single_place_finite_idele_mem_ideal
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (π : p.adicCompletionIntegers K)
    (h : Chapter12SinglePlaceFiniteIdele D p π) :
    D.idealOf h.x = (p.asIdeal : FractionalIdeal R⁰ K) := by
  exact h.ideal_eq

theorem chapter12_nonprincipal_idele_cannot_be_principal
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (x : chapter12FiniteIdeles R K)
    (I : FractionalIdeal R⁰ K)
    (hx : D.idealOf x = I)
    (hI : ¬(I : Submodule R K).IsPrincipal) :
    ¬∃ u : Kˣ,
      chapter12SameFiniteIdeleValuation D x
        (chapter12PrincipalFiniteIdeleHom R K u) := by
  sorry

theorem chapter12_ideal_map_forgets_local_unit_changes
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (x y : chapter12FiniteIdeles R K)
    (hxy : D.idealOf x = D.idealOf y) :
    chapter12SameFiniteIdeleValuation D x y :=
  hxy

/- A ray invariant refines the ordinary ideal invariant: equal ray values
   force equal valuation ideals. -/
theorem chapter12_ray_quotient_refines_ideal_valuation
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12RayDetectionData R K)
    {x y : chapter12FiniteIdeles R K}
    (hray : D.rayMap x = D.rayMap y) :
    chapter12SameFiniteIdeleValuation D.idealData x y := by
  change D.idealData.idealOf x = D.idealData.idealOf y
  exact D.rayMap_sees_ideal x y hray

end
end LastLib.Book04AdelesAndIdeles.Chapter12
