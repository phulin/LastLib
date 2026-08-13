import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies
import Mathlib.Topology.Algebra.Valued.LocallyCompact

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open scoped BigOperators nonZeroDivisors WithZero Topology
open NumberField IsDedekindDomain
open WithZero
open Filter
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
    chapter01IsAlgebraicInteger x ↔ ∃ a : 𝓞 K, (a : K) = x := by
  change IsIntegral ℤ x ↔ ∃ a : 𝓞 K, (a : K) = x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe a

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
  change ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I = I
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization'
    (R := 𝓞 K) (K := K) (I := I) hI

theorem chapter01_fractional_ideal_order_finite_support
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      chapter01FractionalIdealOrder v I ≠ 0}.Finite := by
  have h := FractionalIdeal.finite_factors I
  have h' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      FractionalIdeal.count K v I = 0 := by
    simpa [chapter01FractionalIdealOrder] using h
  have _hI : I ≠ 0 := hI
  exact (Filter.eventually_cofinite.1 h')

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
  simpa [chapter01ResidueField] using
    (chapter01_absolute_ideal_norm_eq_quotient_card K v.asIdeal)

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
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (𝓞 K) v.ne_bot (Localization.AtPrime v.asIdeal)

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
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπmem : π ∈ v.asIdeal := by
    apply (v.intValuation_lt_one_iff_mem π).mp
    rw [hπ]
    rw [← exp_zero, exp_lt_exp]
    norm_num
  let πI : v.adicCompletionIntegers K :=
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) π
  have hπv : Valued.v (πI : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) π :
      v.adicCompletionIntegers K) : v.adicCompletion K) = _
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    change Valued.v ((π : K) : v.adicCompletion K) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      v.valuation_of_algebraMap, hπ]
  have hgen :
      Valuation.IsRankOneDiscrete.generator
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) =
        Units.mk0 (WithZero.exp (-1 : ℤ)) (by simp) := by
    apply Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
    exact ⟨πI, hπv⟩
  have hπu :
      Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) πI := by
    change Valued.v (πI : v.adicCompletion K) =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    rw [hgen, hπv]
    simp
  have hgenideal : chapter01CompletionMaximalIdeal v = Ideal.span {πI} := by
    change IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {πI}
    exact Valuation.IsUniformizer.is_generator hπu
  apply le_antisymm
  · rw [hgenideal]
    apply Ideal.span_le.2
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa [πI] using
      (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) hπmem)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r :
      v.adicCompletionIntegers K) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have hval : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) r :
        v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu
    have hval' : Valued.v ((r : K) : v.adicCompletion K) = 1 := by
      simpa only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
        using hval
    have hlt : Valued.v ((r : K) : v.adicCompletion K) < 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
      exact (v.valuation_lt_one_iff_mem (K := K) r).2 hr
    exact (ne_of_lt hlt) hval'

private theorem chapter01_completion_residue_field_surjective
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ∃ g : chapter01ResidueField v →+* chapter01CompletionResidueField v,
      Function.Surjective g := by
  let f : (𝓞 K) →+* v.adicCompletionIntegers K :=
    algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  let mB : Ideal (v.adicCompletionIntegers K) :=
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  have hmap : Ideal.map f v.asIdeal ≤ mB := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ chapter01CompletionMaximalIdeal v
    rw [chapter01_completion_maximal_ideal_eq_prime_extension K v]
    exact Ideal.mem_map_of_mem f ha
  let g : chapter01ResidueField v →+*
      (v.adicCompletionIntegers K) ⧸ mB :=
    Ideal.Quotient.lift v.asIdeal
      ((Ideal.Quotient.mk mB).comp f) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
  have g_surj : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    let U : Set (v.adicCompletion K) :=
      {z |
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            (z - (b : v.adicCompletion K)) <
          (1 : MonoidWithZeroHom.ValueGroup₀
            (.ofClass (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)))}
    have hUopen : IsOpen U := by
      have hball := Valued.isOpen_ball (v.adicCompletion K)
        (1 : MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)))
      simpa [U] using hball.preimage (continuous_id.sub continuous_const)
    have hUmem : U ∈ 𝓝 (b : v.adicCompletion K) := by
      apply hUopen.mem_nhds
      simp [U]
    obtain ⟨x, hxU⟩ := (v.denseRange_algebraMap (K := K)).mem_nhds hUmem
    have hxb : Valued.v ((x : v.adicCompletion K) - (b : v.adicCompletion K)) < 1 := by
      have hrestrict := hxU
      change
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            ((x : v.adicCompletion K) - (b : v.adicCompletion K)) < _ at hrestrict
      have hlt :=
        (Valuation.restrict_lt_iff_lt_embedding
          (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).mp hrestrict
      simpa [Valuation.embedding_restrict] using hlt
    have hxval : Valued.v ((x : K) : v.adicCompletion K) ≤ 1 := by
      calc
        Valued.v ((x : K) : v.adicCompletion K) =
            Valued.v (((x : v.adicCompletion K) - (b : v.adicCompletion K)) +
              (b : v.adicCompletion K)) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v ((x : v.adicCompletion K) - (b : v.adicCompletion K)))
            (Valued.v (b : v.adicCompletion K)) := map_add_le_max _ _ _
        _ ≤ 1 := max_le (le_of_lt hxb) b.property
    have hxglobal : v.valuation K x ≤ 1 := by
      simpa only [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        using hxval
    obtain ⟨a, ha⟩ :=
      v.exists_valuation_sub_lt_of_integer hxglobal
        (Units.mk0 (1 : ℤᵐ⁰) (by simp))
    have hax :
        Valued.v (((a : K) : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 := by
      have hcoe (z : K) : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z := by
        simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rw [hcoe a, hcoe x, ← map_sub, ← hcoe ((a : K) - x)]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
      simpa using ha
    have hbx : Valued.v ((b : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hxb
    have hxa : Valued.v ((x : v.adicCompletion K) - (a : v.adicCompletion K)) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hax
    have hba : Valued.v ((b : v.adicCompletion K) - (a : v.adicCompletion K)) < 1 := by
      calc
        Valued.v ((b : v.adicCompletion K) - (a : v.adicCompletion K)) =
            Valued.v (((b : v.adicCompletion K) - (x : v.adicCompletion K)) +
              ((x : v.adicCompletion K) - (a : v.adicCompletion K))) := by
                rw [sub_add_sub_cancel]
        _ < 1 := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_add_lt hbx hxa
    refine ⟨Ideal.Quotient.mk v.asIdeal a, ?_⟩
    change Ideal.Quotient.mk mB (f a) = Ideal.Quotient.mk mB b
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    apply (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).2
    change Valued.v ((f a - b : v.adicCompletionIntegers K) : v.adicCompletion K) < 1
    have hba' :
        Valued.v ((b : v.adicCompletion K) -
          (f a : v.adicCompletionIntegers K)) < 1 := by
      simpa [f, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
        using hba
    have hrev :
        Valued.v ((f a : v.adicCompletionIntegers K) - b : v.adicCompletion K) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hba'
    simpa only [AddSubgroupClass.coe_sub] using hrev
  exact ⟨g, g_surj⟩

theorem chapter01_completion_integers_has_finite_residue_field
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite (chapter01CompletionResidueField v) := by
  let hfinite : Finite (chapter01ResidueField v) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  obtain ⟨g, hg⟩ := chapter01_completion_residue_field_surjective K v
  exact @Finite.of_surjective _ _ hfinite g hg

theorem chapter01_completion_is_fraction_field
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsFractionRing (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  infer_instance

theorem chapter01_completion_residue_field_equiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Nonempty (chapter01CompletionResidueField v ≃+* chapter01ResidueField v) := by
  let f : (𝓞 K) →+* v.adicCompletionIntegers K :=
    algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  let mB : Ideal (v.adicCompletionIntegers K) :=
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
  have hmap : Ideal.map f v.asIdeal ≤ mB := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ chapter01CompletionMaximalIdeal v
    rw [chapter01_completion_maximal_ideal_eq_prime_extension K v]
    exact Ideal.mem_map_of_mem f ha
  let g : chapter01ResidueField v →+*
      (v.adicCompletionIntegers K) ⧸ mB :=
    Ideal.Quotient.lift v.asIdeal
      ((Ideal.Quotient.mk mB).comp f) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact (Ideal.map_le_iff_le_comap.mp hmap) ha)
  have g_surj : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    let U : Set (v.adicCompletion K) :=
      {z |
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            (z - (b : v.adicCompletion K)) <
          (1 : MonoidWithZeroHom.ValueGroup₀
            (.ofClass (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)))}
    have hUopen : IsOpen U := by
      have hball := Valued.isOpen_ball (v.adicCompletion K)
        (1 : MonoidWithZeroHom.ValueGroup₀
          (.ofClass (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)))
      simpa [U] using hball.preimage (continuous_id.sub continuous_const)
    have hUmem : U ∈ 𝓝 (b : v.adicCompletion K) := by
      apply hUopen.mem_nhds
      simp [U]
    obtain ⟨x, hxU⟩ := (v.denseRange_algebraMap (K := K)).mem_nhds hUmem
    have hxb : Valued.v ((x : v.adicCompletion K) - (b : v.adicCompletion K)) < 1 := by
      have hrestrict := hxU
      change
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            ((x : v.adicCompletion K) - (b : v.adicCompletion K)) < _ at hrestrict
      have hlt :=
        (Valuation.restrict_lt_iff_lt_embedding
          (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).mp hrestrict
      simpa [Valuation.embedding_restrict] using hlt
    have hxval : Valued.v ((x : K) : v.adicCompletion K) ≤ 1 := by
      calc
        Valued.v ((x : K) : v.adicCompletion K) =
            Valued.v (((x : v.adicCompletion K) - (b : v.adicCompletion K)) +
              (b : v.adicCompletion K)) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v ((x : v.adicCompletion K) - (b : v.adicCompletion K)))
            (Valued.v (b : v.adicCompletion K)) := map_add_le_max _ _ _
        _ ≤ 1 := max_le (le_of_lt hxb) b.property
    have hxglobal : v.valuation K x ≤ 1 := by
      simpa only [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        using hxval
    obtain ⟨a, ha⟩ :=
      v.exists_valuation_sub_lt_of_integer hxglobal
        (Units.mk0 (1 : ℤᵐ⁰) (by simp))
    have hax :
        Valued.v (((a : K) : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 := by
      have hcoe (z : K) : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z := by
        simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rw [hcoe a, hcoe x, ← map_sub, ← hcoe ((a : K) - x)]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
      simpa using ha
    have hbx : Valued.v ((b : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hxb
    have hxa : Valued.v ((x : v.adicCompletion K) - (a : v.adicCompletion K)) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hax
    have hba : Valued.v ((b : v.adicCompletion K) - (a : v.adicCompletion K)) < 1 := by
      calc
        Valued.v ((b : v.adicCompletion K) - (a : v.adicCompletion K)) =
            Valued.v (((b : v.adicCompletion K) - (x : v.adicCompletion K)) +
              ((x : v.adicCompletion K) - (a : v.adicCompletion K))) := by
                rw [sub_add_sub_cancel]
        _ < 1 := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_add_lt hbx hxa
    refine ⟨Ideal.Quotient.mk v.asIdeal a, ?_⟩
    change Ideal.Quotient.mk mB (f a) = Ideal.Quotient.mk mB b
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    apply (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).2
    change Valued.v ((f a - b : v.adicCompletionIntegers K) : v.adicCompletion K) < 1
    have hba' :
        Valued.v ((b : v.adicCompletion K) -
          (f a : v.adicCompletionIntegers K)) < 1 := by
      simpa [f, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
        using hba
    have hrev :
        Valued.v ((f a : v.adicCompletionIntegers K) - b : v.adicCompletion K) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hba'
    simpa only [AddSubgroupClass.coe_sub] using hrev
  have g_inj : Function.Injective g := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hmemB : f a - f b ∈ mB := by
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simpa [g] using hxy
    have hltB : Valued.v ((f a - f b : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 := by
      exact (Valuation.mem_maximalIdeal_iff
        (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).1 hmemB
    have hfa : ((f a : v.adicCompletionIntegers K) : v.adicCompletion K) =
        (a : v.adicCompletion K) := by
      change ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a :
        v.adicCompletionIntegers K) : v.adicCompletion K) = _
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    have hfb : ((f b : v.adicCompletionIntegers K) : v.adicCompletion K) =
        (b : v.adicCompletion K) := by
      change ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) b :
        v.adicCompletionIntegers K) : v.adicCompletion K) = _
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    have hltC :
        Valued.v (((a : K) : v.adicCompletion K) - (b : v.adicCompletion K)) < 1 := by
      simpa [hfa, hfb] using hltB
    have hcoe (z : K) : (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z := by
      simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rw [hcoe a, hcoe b, ← map_sub, ← hcoe ((a : K) - b)] at hltC
    have hltA : v.valuation K (a - b) < 1 := by
      simpa only [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        using hltC
    exact (v.valuation_lt_one_iff_mem (K := K) (a - b)).mp hltA
  let e := RingEquiv.ofBijective g ⟨g_inj, g_surj⟩
  exact ⟨e.symm⟩

theorem chapter01_completion_integers_compact
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CompactSpace (v.adicCompletionIntegers K) := by
  apply (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)).2
  refine ⟨by
      change CompleteSpace (v.adicCompletionIntegers K)
      exact (Valued.isClosed_valuationSubring (v.adicCompletion K)).isComplete.completeSpace_coe,
    by
      change IsDiscreteValuationRing (v.adicCompletionIntegers K)
      infer_instance,
    by
      change Finite (chapter01CompletionResidueField v)
      exact chapter01_completion_integers_has_finite_residue_field K v⟩

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
