import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open scoped BigOperators nonZeroDivisors
open NumberField IsDedekindDomain
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

noncomputable section

/-! ## 1.2 Number fields and their integers -/

variable (K : Type*) [Field K] [NumberField K]

theorem chapter01_degree_eq_field_dimension :
    chapter01Degree K = Module.finrank ℚ K := rfl

theorem chapter01_ring_of_integers_is_fraction_ring :
    IsFractionRing (𝓞 K) K := by infer_instance

theorem chapter01_ring_of_integers_is_dedekind :
    IsDedekindDomain (𝓞 K) := by infer_instance

theorem chapter01_ring_of_integers_is_integrally_closed :
    IsIntegrallyClosed (𝓞 K) := by infer_instance

theorem chapter01_ring_of_integers_is_noetherian :
    IsNoetherian ℤ (𝓞 K) := by infer_instance

theorem chapter01_ring_of_integers_free_over_integers :
    Module.Free ℤ (𝓞 K) := by infer_instance

theorem chapter01_ring_of_integers_finite_over_integers :
    Module.Finite ℤ (𝓞 K) := by infer_instance

theorem chapter01_ring_of_integers_rank :
    Module.finrank ℤ (𝓞 K) = chapter01Degree K := by
  simpa [chapter01Degree] using NumberField.RingOfIntegers.rank K

theorem chapter01_algebraic_integer_iff (x : K) :
    chapter01IsAlgebraicInteger x ↔ IsIntegral ℤ x := Iff.rfl

theorem chapter01_unit_order_apply
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    chapter01UnitOrder v x = chapter01Order v (x : K) := rfl

omit [NumberField K] in
theorem chapter01_ring_integer_coe_is_integral (x : 𝓞 K) :
    IsIntegral ℤ (x : K) :=
  NumberField.RingOfIntegers.isIntegral_coe x

theorem chapter01_principal_fractional_ideal_factorization {x : K} (hx : x ≠ 0) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ chapter01Order v x =
      chapter01PrincipalFractionalIdeal x := by
  change ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ dedekindExponent v x =
    chapterPrincipalFractionalIdeal x
  exact dedekind_principal_fractional_ideal_factorization
    (A := 𝓞 K) (K := K) hx

theorem chapter01_order_finite_support {x : K} (hx : x ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | chapter01Order v x ≠ 0}.Finite := by
  change {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      dedekindExponent v x ≠ 0}.Finite
  exact dedekindExponent_finite_support (A := 𝓞 K) (K := K) hx

theorem chapter01_fractional_ideal_factorization
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ chapter01FractionalIdealOrder v I = I := by
  sorry

theorem chapter01_fractional_ideal_order_finite_support
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      chapter01FractionalIdealOrder v I ≠ 0}.Finite := by
  sorry

theorem chapter01_order_mul
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapter01Order v (x * y) = chapter01Order v x + chapter01Order v y := by
  change dedekindExponent v (x * y) = dedekindExponent v x + dedekindExponent v y
  exact dedekindExponent_mul (A := 𝓞 K) (K := K) v hx hy

theorem chapter01_order_inv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : K} (hx : x ≠ 0) :
    chapter01Order v x⁻¹ = -chapter01Order v x := by
  change dedekindExponent v x⁻¹ = -dedekindExponent v x
  exact dedekindExponent_inv (A := 𝓞 K) (K := K) v hx

theorem chapter01_absolute_ideal_norm_mul (I J : Ideal (𝓞 K)) :
    chapter01AbsoluteIdealNorm (I * J) =
      chapter01AbsoluteIdealNorm I * chapter01AbsoluteIdealNorm J := by
  change Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J
  exact map_mul Ideal.absNorm I J

theorem chapter01_absolute_ideal_norm_span_singleton (x : 𝓞 K) :
    chapter01AbsoluteIdealNorm (Ideal.span ({x} : Set (𝓞 K))) =
      (Algebra.norm ℤ x).natAbs := by
  simp [chapter01AbsoluteIdealNorm]

theorem chapter01_absolute_ideal_norm_eq_quotient_card (I : Ideal (𝓞 K)) :
    chapter01AbsoluteIdealNorm I = Nat.card ((𝓞 K) ⧸ I) := by
  simpa [chapter01AbsoluteIdealNorm, Ideal.absNorm_apply] using
    (Submodule.cardQuot_apply I)

theorem chapter01_prime_norm_eq_residue_card
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter01AbsoluteIdealNorm v.asIdeal = Nat.card (chapter01ResidueField v) := by
  sorry

theorem chapter01_fractional_norm_principal (x : K) :
    FractionalIdeal.absNorm (chapter01PrincipalFractionalIdeal x) =
      |Algebra.norm ℚ x| := by
  simp [chapter01PrincipalFractionalIdeal, FractionalIdeal.absNorm_span_singleton]

theorem chapter01_fractional_norm_of_integral_ideal (I : Ideal (𝓞 K)) :
    FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.absNorm I : ℚ) := by
  exact FractionalIdeal.coeIdeal_absNorm I

def chapter01_ideal_class_group_quotient_equiv :
    chapter01ClassGroup K ≃*
      chapter01FractionalIdealGroup K ⧸
        chapter01PrincipalFractionalIdealSubgroup K :=
  chapter01IdealClassGroupEquiv K

theorem chapter01_ideal_class_group_finite :
    Finite (chapter01ClassGroup K) := by infer_instance

noncomputable instance chapter01_ideal_class_group_fintype :
    Fintype (chapter01ClassGroup K) := by infer_instance

theorem chapter01_minkowski_small_element
    (I : chapter01FractionalIdealGroup K) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
          (4 / Real.pi) ^ chapter01ComplexPlaceCount K *
            (chapter01Degree K).factorial / (chapter01Degree K) ^ chapter01Degree K *
              Real.sqrt |chapter01Discriminant K| := by
  simpa [chapter01ComplexPlaceCount, chapter01Degree, chapter01Discriminant]
    using (NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K I)

theorem chapter01_localization_at_prime_is_dvr
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := by
  sorry

theorem chapter01_completion_is_complete
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (v.adicCompletion K) := by infer_instance

theorem chapter01_completion_integers_is_dvr
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
  IsDiscreteValuationRing (v.adicCompletionIntegers K) := by infer_instance

theorem chapter01_completion_maximal_ideal_is_local_maximal_ideal
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter01CompletionMaximalIdeal v =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := rfl

theorem chapter01_completion_maximal_ideal_eq_prime_extension
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter01CompletionMaximalIdeal v =
      Ideal.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) v.asIdeal := by
  sorry

theorem chapter01_completion_integers_has_finite_residue_field
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite (chapter01ResidueField v) := by
  sorry

theorem chapter01_completion_is_fraction_field
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsFractionRing (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  sorry

theorem chapter01_completion_residue_field_equiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Nonempty (chapter01CompletionResidueField v ≃+* chapter01ResidueField v) := by
  sorry

theorem chapter01_completion_integers_compact
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompactSpace (v.adicCompletionIntegers K) := by
  sorry

def chapter01LocalizationMembership
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : Prop :=
  IsInChapterLocalizationAtPrime v.asIdeal x

theorem chapter01_localization_membership_iff_order_nonnegative
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) :
    chapter01LocalizationMembership K v x ↔ 0 ≤ chapter01Order v x := by
  change IsInChapterLocalizationAtPrime v.asIdeal x ↔ 0 ≤ dedekindExponent v x
  exact localization_membership_iff_dedekindExponent_nonnegative
    (A := 𝓞 K) (K := K) v x

end

end LastLib.Book04AdelesAndIdeles.Chapter01
