import LastLib.Book04AdelesAndIdeles.Chapter12.Core

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Set NumberField
open scoped BigOperators nonZeroDivisors

/-! # Book 4, Chapter 12, §12.4: A nonprincipal ideal as an idele -/

abbrev chapter12MinusFiveIntegers := Zsqrtd (-5)

abbrev chapter12MinusFiveField := FractionRing chapter12MinusFiveIntegers

def chapter12MinusFiveSqrt : chapter12MinusFiveIntegers :=
  Zsqrtd.sqrtd

def chapter12MinusFiveIdeal : Ideal chapter12MinusFiveIntegers :=
  Ideal.span ({(2 : chapter12MinusFiveIntegers),
    1 + chapter12MinusFiveSqrt} : Set chapter12MinusFiveIntegers)

/- The finite-idele map is canonically attached to `𝓞 K`; this data records
   the standard identification of the displayed quadratic model with that
   number-field presentation. -/
structure Chapter12MinusFiveFieldData
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] where
  field_model : K ≃+* chapter12MinusFiveField
  ringOfIntegers_model : 𝓞 K ≃+* chapter12MinusFiveIntegers
  field_model_compatibility :
    ∀ x : 𝓞 K,
      field_model (algebraMap (𝓞 K) K x) =
        algebraMap chapter12MinusFiveIntegers chapter12MinusFiveField
          (ringOfIntegers_model x)

def chapter12MinusFiveIdealInRingOfIntegers
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (F : Chapter12MinusFiveFieldData K) : Ideal (𝓞 K) :=
  Ideal.comap F.ringOfIntegers_model.toRingHom chapter12MinusFiveIdeal

noncomputable def chapter12MinusFivePlace
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (F : Chapter12MinusFiveFieldData K) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) := by
  sorry

theorem chapter12_minus_five_place_ideal
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (F : Chapter12MinusFiveFieldData K) :
    (chapter12MinusFivePlace F).asIdeal =
      chapter12MinusFiveIdealInRingOfIntegers F := by
  sorry

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

noncomputable def chapter12SinglePlaceFiniteIdeleUnderlying
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (π : p.adicCompletionIntegers K)
    (hπ : chapter12UniformizerAt p π) : chapter12FiniteIdeles R K := by
  classical
  let localUnit : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (v.adicCompletion K)ˣ := fun v =>
    dite (v = p)
      (fun h => h.symm ▸ Units.mk0 (π : p.adicCompletion K) (by sorry))
      (fun _ => 1)
  have hunit : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum R in Filter.cofinite,
      localUnit v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    sorry
  exact RestrictedProduct.mkUnit localUnit hunit

noncomputable def chapter12SinglePlaceFiniteIdeleOf
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (π : p.adicCompletionIntegers K)
    (hπ : chapter12UniformizerAt p π) :
    Chapter12SinglePlaceFiniteIdele D p π where
  x := chapter12SinglePlaceFiniteIdeleUnderlying p π hπ
  uniformizer := hπ
  value_at := by sorry
  value_away := by sorry

noncomputable def chapter12MinusFiveSinglePlaceFiniteIdele
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (F : Chapter12MinusFiveFieldData K)
    (π : (chapter12MinusFivePlace F).adicCompletionIntegers K)
    (hπ : chapter12UniformizerAt (chapter12MinusFivePlace F) π) :
    Chapter12SinglePlaceFiniteIdele
      (chapter12CanonicalFiniteIdeleIdealData K) (chapter12MinusFivePlace F) π :=
  chapter12SinglePlaceFiniteIdeleOf
    (chapter12CanonicalFiniteIdeleIdealData K)
      (chapter12MinusFivePlace F) π hπ

/- The canonical number-field realization is obtained from the preceding
   chapter's finite-divisor realization at the divisor supported at `p`. -/
noncomputable def chapter12CanonicalSinglePlaceFiniteIdele
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter12FiniteIdeles (𝓞 K) K :=
  Classical.choose
    (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_realizes_divisor
      K (Finsupp.single p 1))

theorem chapter12_canonical_single_place_finite_idele_mem_ideal
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (chapter12CanonicalFiniteIdeleIdealData K).idealOf
        (chapter12CanonicalSinglePlaceFiniteIdele p) =
      (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
  sorry

theorem chapter12_canonical_single_place_finite_idele_mem_named_ideal
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (I : Ideal (𝓞 K))
    (hp : p.asIdeal = I) :
    (chapter12CanonicalFiniteIdeleIdealData K).idealOf
        (chapter12CanonicalSinglePlaceFiniteIdele p) =
      (I : FractionalIdeal (𝓞 K)⁰ K) := by
  sorry

theorem chapter12_single_place_finite_idele_mem_ideal
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (π : p.adicCompletionIntegers K)
    (h : Chapter12SinglePlaceFiniteIdele
      (chapter12CanonicalFiniteIdeleIdealData K) p π) :
    (chapter12CanonicalFiniteIdeleIdealData K).idealOf h.x =
      (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
  sorry

theorem chapter12_minus_five_single_place_idele_realizes_named_nonprincipal_ideal
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (F : Chapter12MinusFiveFieldData K)
    (π : (chapter12MinusFivePlace F).adicCompletionIntegers K)
    (hπ : chapter12UniformizerAt (chapter12MinusFivePlace F) π) :
    (chapter12CanonicalFiniteIdeleIdealData K).idealOf
        (chapter12MinusFiveSinglePlaceFiniteIdele F π hπ).x =
      (chapter12MinusFiveIdealInRingOfIntegers F :
        FractionalIdeal (𝓞 K)⁰ K) ∧
      ¬((chapter12MinusFiveIdealInRingOfIntegers F :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal := by
  sorry

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
