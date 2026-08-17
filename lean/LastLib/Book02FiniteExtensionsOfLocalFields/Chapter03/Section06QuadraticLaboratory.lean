import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped TensorProduct WithZero

/-! ## 3.6. A quadratic laboratory -/

/-- The quadratic polynomial `T^2-a`. -/
def chapter03QuadraticPolynomial
    {K : Type*} [CommRing K] (a : K) : K[X] :=
  ((X : K[X]) ^ 2 - (C a : K[X]) : K[X])

@[simp] theorem chapter03QuadraticPolynomial_eval
    {K : Type*} [CommRing K] (a x : K) :
    (chapter03QuadraticPolynomial a).eval x = x ^ 2 - a := by
  simp [chapter03QuadraticPolynomial]

/-- The canonical root algebra attached to `T^2-a`. -/
noncomputable abbrev chapter03QuadraticRootAlgebra
    (K : Type*) [CommRing K] (a : K) : Type _ :=
  AdjoinRoot (chapter03QuadraticPolynomial a)

/-- Compatibility of a chosen residue map with the quotient residue map. -/
def chapter03CompatibleResidueMap
    (A k : Type*) [CommRing A] [IsLocalRing A] [CommRing k]
    (ρ : A →+* k) : Prop :=
  ∃ e : A ⧸ IsLocalRing.maximalIdeal A ≃+* k,
    e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = ρ

/-- The precise reduction hypotheses for a quadratic polynomial. -/
def chapter03QuadraticReductionCondition
    (A k : Type*) [CommRing A] [CommRing k]
    (ρ : A →+* k) (f : A[X]) (fbar : k[X]) : Prop :=
  Function.Surjective ρ ∧ f.map ρ = fbar ∧
    Irreducible fbar ∧ fbar.Separable

/-- A unit whose residue class is not a square. -/
def chapter03ResidueUnitNonsquare
    (A k : Type*) [CommRing A] [Field k]
    (ρ : A →+* k) (u : Aˣ) : Prop :=
  ¬ ∃ x : k, x ^ 2 = ρ (u : A)

/-- A finite residue field of odd cardinality. -/
def chapter03FiniteOddResidueField
    (k : Type*) [Field k] [Fintype k] : Prop :=
  Fintype.card k % 2 = 1

theorem chapter03FiniteOddResidueField_iff
    (k : Type*) [Field k] [Fintype k] :
    chapter03FiniteOddResidueField k ↔ Fintype.card k % 2 = 1 := Iff.rfl

/-- An irreducible separable reduction of `T^2-u` gives an unramified
quadratic extension. -/
theorem chapter03_unit_quadratic_is_unramified
    (A k K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field K] [Field L] [Fintype k]
    [Algebra A k] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L] (u : Aˣ)
    (hodd : chapter03FiniteOddResidueField k)
    (hnonsquare : chapter03ResidueUnitNonsquare A k (algebraMap A k) u)
    (hred :
      chapter03QuadraticReductionCondition A k
        (algebraMap A k)
        (chapter03QuadraticPolynomial (u : A))
        (chapter03QuadraticPolynomial (algebraMap A k (u : A))))
    (hresidue : chapter03CompatibleResidueMap A k (algebraMap A k))
    (α : L)
    (hroot : aeval α
      (chapter03QuadraticPolynomial (algebraMap A L (u : A))) = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    [Algebra.IsSeparable K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hvaluationRing : (vK.valuationSubring : Set K) =
      Set.range (algebraMap A K)) :
    ∃ data : Chapter03FiniteLocalExtensionData K L ℤᵐ⁰ vK vL,
      data.e = 1 ∧ data.f = 2 := by
  classical
  obtain ⟨eres, hresidue_comp⟩ := hresidue
  let f : A[X] := chapter03QuadraticPolynomial (u : A)
  let fbar : (A ⧸ IsLocalRing.maximalIdeal A)[X] :=
    f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
  have hmap_fbar :
      fbar.map eres.toRingHom =
        chapter03QuadraticPolynomial (algebraMap A k (u : A)) := by
    change (f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).map
        eres.toRingHom = _
    rw [Polynomial.map_map, hresidue_comp]
    simpa [f] using hred.2.1
  have hfmonic : f.Monic := by
    exact monic_X_pow_sub_C (u : A) (by norm_num)
  have hfbarmonic : fbar.Monic := by
    exact hfmonic.map _
  have hfbarirr : Irreducible fbar := by
    exact Polynomial.Monic.irreducible_of_irreducible_map
      (φ := eres.toRingHom) fbar hfbarmonic (by
        rw [hmap_fbar]
        exact hred.2.2.1)
  have hmap_fbar_symm :
      (chapter03QuadraticPolynomial (algebraMap A k (u : A))).map
          eres.symm.toRingHom = fbar := by
    rw [← hmap_fbar, Polynomial.map_map]
    simp
  have hfbarsep : fbar.Separable := by
    rw [← hmap_fbar_symm]
    exact hred.2.2.2.map (f := eres.symm.toRingHom)
  have hbaseIntegers : vK.Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := by
        intro a
        exact (Valuation.mem_valuationSubring_iff vK
          (algebraMap A K a)).mp ((Set.ext_iff.mp hvaluationRing
            (algebraMap A K a)).mpr ⟨a, rfl⟩)
      exists_of_le_one := by
        intro r hr
        have hr' : r ∈ vK.valuationSubring :=
          (Valuation.mem_valuationSubring_iff vK r).mpr hr
        exact (Set.ext_iff.mp hvaluationRing r).mp hr' }
  let alg : A →+* vK.valuationSubring :=
    (algebraMap A K).codRestrict vK.valuationSubring
      (fun a => hbaseIntegers.map_le_one a)
  have halg_bij : Function.Bijective alg := by
    constructor
    · intro a b hab
      apply hbaseIntegers.hom_inj
      exact congrArg Subtype.val hab
    · intro x
      obtain ⟨a, ha⟩ :=
        (Set.ext_iff.mp hvaluationRing (x : K)).mp x.property
      exact ⟨a, Subtype.ext ha⟩
  let ebase : A ≃+* vK.valuationSubring := RingEquiv.ofBijective alg halg_bij
  have hbase_comp :
      (algebraMap vK.valuationSubring L).comp ebase.toRingHom =
        algebraMap A L := by
    ext a
    change algebraMap K L (algebraMap A K a) = algebraMap A L a
    rw [IsScalarTower.algebraMap_apply A K L]
  let _ : IsAdicComplete
      (IsLocalRing.maximalIdeal A) A := by
    apply (IsAdicComplete.congr_ringEquiv
      (IsLocalRing.maximalIdeal A) ebase).mp
    rw [IsLocalRing.map_ringEquiv_maximalIdeal ebase]
    exact hcomplete
  have hupper : (vL.valuationSubring : Set L) =
      (integralClosure A L : Set L) :=
    (Set.ext fun x => by
      rw [(LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
        vK vL hcomplete).2.2.2.2]
      exact (RingEquiv.isIntegral_iff ebase hbase_comp x).symm)
  have hrootK : aeval α (f.map (algebraMap A K)) = 0 := by
    have hrootA : aeval α f = 0 := by
      simpa [f, chapter03QuadraticPolynomial, aeval_def, Algebra.smul_def] using hroot
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hrootA
  obtain ⟨_, hdegree', he, hf, _⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.separable_residue_polynomial_lift_is_unramified
      vK vL fbar f α ⟨hfbarmonic, hfmonic⟩ hfbarirr hfbarsep rfl hrootK hgen
      hbaseIntegers hvaluationRing hupper
  have hfbar_degree : fbar.natDegree = 2 := by
    calc
      fbar.natDegree = (fbar.map eres.toRingHom).natDegree :=
        (natDegree_map_eq_of_injective eres.injective fbar).symm
      _ = 2 := by
        rw [hmap_fbar]
        simp [chapter03QuadraticPolynomial]
  refine ⟨⟨1, 2, he, ?_, hdegree⟩, rfl, rfl⟩
  simpa [hfbar_degree] using hf

/-- A separable quadratic extension is represented by a square-root algebra. -/
theorem chapter03_quadratic_extension_is_a_square_root
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hdegree : Module.finrank K L = 2)
    [Algebra.IsSeparable K L] (hchar : ¬ CharP K 2) :
    ∃ a : K, Nonempty
      (L ≃ₐ[K] chapter03QuadraticRootAlgebra K a) := by
  classical
  have hnot_surj : ¬ Function.Surjective (algebraMap K L) := by
    intro hsurj
    have hfin : Module.finrank K L = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
        ⟨(algebraMap K L).injective, hsurj⟩
    omega
  obtain ⟨x, hx⟩ : ∃ x : L, x ∉ Set.range (algebraMap K L) := by
    by_contra h
    push Not at h
    exact hnot_surj h
  let b : K := (minpoly K x).coeff 1
  let c : K := (minpoly K x).coeff 0
  have hxint : IsIntegral K x := IsIntegral.of_finite K x
  have hxdeg_lower : 2 ≤ (minpoly K x).natDegree :=
    (minpoly.two_le_natDegree_iff hxint).2 hx
  have hxdeg_upper : (minpoly K x).natDegree ≤ 2 := by
    exact (minpoly.natDegree_le x).trans hdegree.le
  have hxdeg : (minpoly K x).natDegree = 2 := by
    omega
  have hpoly : minpoly K x = X ^ 2 + C b * X + C c := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp [b, c]
    by_cases hn1 : n = 1
    · subst n
      simp [b, c]
    by_cases hn2 : n = 2
    · subst n
      have hlead : (minpoly K x).coeff 2 = 1 := by
        rw [← hxdeg, coeff_natDegree, (minpoly.monic hxint).leadingCoeff]
      simpa [b, c] using hlead
    have hlt : (minpoly K x).natDegree < n := by
      omega
    have hn1' : ¬1 = n := Ne.symm hn1
    simp [coeff_eq_zero_of_natDegree_lt hlt, coeff_X, coeff_C, hn0, hn1', hn2]
  have hxroot : x ^ 2 + algebraMap K L b * x + algebraMap K L c = 0 := by
    have h := minpoly.aeval K x
    rw [hpoly] at h
    simpa [aeval_def, Algebra.smul_def] using h
  let a : K := b ^ 2 - 4 * c
  let α : L := 2 * x + algebraMap K L b
  have hαsquare : α ^ 2 = algebraMap K L a := by
    dsimp [α, a]
    calc
      (2 * x + algebraMap K L b) ^ 2 =
          (algebraMap K L b) ^ 2 - 4 * algebraMap K L c := by
            linear_combination 4 * hxroot
      _ = algebraMap K L (b ^ 2 - 4 * c) := by
        simp [map_sub, map_pow, map_mul, map_ofNat]
  have htwoK : (2 : K) ≠ 0 := by
    intro htwo
    apply hchar
    exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo
  have htwoL : (2 : L) ≠ 0 := by
    have hmap : (algebraMap K L) (2 : K) ≠ 0 :=
      (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).2 htwoK
    simpa [map_natCast, map_ofNat] using hmap
  have hαnot : α ∉ Set.range (algebraMap K L) := by
    intro hαrange
    rcases hαrange with ⟨z, hz⟩
    apply hx
    refine ⟨(z - b) / 2, ?_⟩
    have hz' : (2 : L) * x + algebraMap K L b = algebraMap K L z := by
      simpa [α] using hz.symm
    have hdiv :
        (algebraMap K L z - algebraMap K L b) / (2 : L) = x := by
      apply (div_eq_iff htwoL).2
      linear_combination -hz'
    simpa [map_div₀, map_sub, map_natCast, map_ofNat] using hdiv
  have hαint : IsIntegral K α := IsIntegral.of_finite K α
  have hαdeg_lower : 2 ≤ (minpoly K α).natDegree :=
    (minpoly.two_le_natDegree_iff hαint).2 hαnot
  have hαdeg_upper : (minpoly K α).natDegree ≤ 2 := by
    exact (minpoly.natDegree_le α).trans hdegree.le
  have hαdeg : (minpoly K α).natDegree = 2 := by
    omega
  have hαadjoin_finrank :
      Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = 2 := by
    rw [IntermediateField.adjoin.finrank hαint, hαdeg]
  have hαadjoin : IntermediateField.adjoin K ({α} : Set L) = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hαadjoin_finrank, IntermediateField.finrank_top']
    exact hdegree.symm
  have hαadjoin_sub :
      (IntermediateField.adjoin K ({α} : Set L)).toSubalgebra =
        Algebra.adjoin K ({α} : Set L) :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic
  have hαadjoin_alg : Algebra.adjoin K ({α} : Set L) = ⊤ := by
    rw [← hαadjoin_sub, hαadjoin, IntermediateField.top_toSubalgebra]
  have hroot : aeval α (chapter03QuadraticPolynomial a) = 0 := by
    simp [chapter03QuadraticPolynomial, hαsquare]
  let φ : chapter03QuadraticRootAlgebra K a →ₐ[K] L :=
    AdjoinRoot.liftAlgHom (chapter03QuadraticPolynomial a)
      (Algebra.ofId K L) α hroot
  have hφ_surj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← hαadjoin_alg]
    refine Algebra.adjoin_le_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    refine ⟨AdjoinRoot.root _, ?_⟩
    change
      (AdjoinRoot.liftAlgHom (chapter03QuadraticPolynomial a)
        (Algebra.ofId K L) α hroot)
        (AdjoinRoot.root (chapter03QuadraticPolynomial a)) = α
    exact AdjoinRoot.liftAlgHom_root
      (p := chapter03QuadraticPolynomial a) (Algebra.ofId K L) α hroot
  have hmonic : (chapter03QuadraticPolynomial a).Monic := by
    exact monic_X_pow_sub_C a (by norm_num)
  let _ : Module.Finite K (chapter03QuadraticRootAlgebra K a) :=
    hmonic.finite_adjoinRoot
  have hsource_finrank :
      Module.finrank K (chapter03QuadraticRootAlgebra K a) = 2 := by
    have hpb := PowerBasis.finrank (AdjoinRoot.powerBasis' hmonic)
    change Module.finrank K (chapter03QuadraticRootAlgebra K a) =
      (chapter03QuadraticPolynomial a).natDegree at hpb
    simpa [chapter03QuadraticPolynomial, natDegree_X_pow_sub_C] using hpb
  have hφ_bij : Function.Bijective φ := by
    refine ⟨?_, hφ_surj⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hsource_finrank.trans hdegree.symm)).2
      (show Function.Surjective φ.toLinearMap from hφ_surj)
  exact ⟨a, ⟨(AlgEquiv.ofBijective φ hφ_bij).symm⟩⟩

/-- An Eisenstein quadratic is totally ramified. -/
theorem chapter03_eisenstein_quadratic_is_totally_ramified
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L] (π : A) (f : A[X]) (α : L)
    (hE : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    (hdegree_poly : f.natDegree = 2)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hvaluationRing : (vK.valuationSubring : Set K) =
      Set.range (algebraMap A K)) :
    ∃ data : Chapter03FiniteLocalExtensionData K L ℤᵐ⁰ vK vL,
      data.e = 2 ∧ data.f = 1 := by
  let hbaseIntegers : vK.Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := by
        intro a
        exact (Valuation.mem_valuationSubring_iff vK
          (algebraMap A K a)).mp ((Set.ext_iff.mp hvaluationRing
            (algebraMap A K a)).mpr ⟨a, rfl⟩)
      exists_of_le_one := by
        intro r hr
        have hr' : r ∈ vK.valuationSubring :=
          (Valuation.mem_valuationSubring_iff vK r).mpr hr
        exact (Set.ext_iff.mp hvaluationRing r).mp hr' }
  let alg : A →+* vK.valuationSubring :=
    (algebraMap A K).codRestrict vK.valuationSubring
      (fun a => hbaseIntegers.map_le_one a)
  have halg_bij : Function.Bijective alg := by
    constructor
    · intro a b hab
      apply hbaseIntegers.hom_inj
      exact congrArg Subtype.val hab
    · intro x
      obtain ⟨a, ha⟩ :=
        (Set.ext_iff.mp hvaluationRing (x : K)).mp x.property
      exact ⟨a, Subtype.ext ha⟩
  let e : A ≃+* vK.valuationSubring := RingEquiv.ofBijective alg halg_bij
  have hcomp :
      (algebraMap vK.valuationSubring L).comp e.toRingHom =
        algebraMap A L := by
    ext a
    change algebraMap K L (algebraMap A K a) = algebraMap A L a
    rw [IsScalarTower.algebraMap_apply A K L]
  have hupper : (vL.valuationSubring : Set L) =
    (integralClosure A L : Set L) :=
    (Set.ext fun x => by
      rw [(LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
        vK vL hcomplete).2.2.2.2]
      exact (RingEquiv.isIntegral_iff e hcomp x).symm)
  obtain ⟨_, he, hf, _, _⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_root_is_uniformizer_and_totally_ramified
      (vK := vK) (v := vL) (n := 2) π f α hE hroot hdegree_poly hgen
      hbaseIntegers hvaluationRing hupper
  refine ⟨⟨2, 1, he, hf, hdegree⟩, rfl, rfl⟩

/-- The two standard ramified quadratic examples. -/
theorem chapter03_uniformizer_and_unit_uniformizer_are_totally_ramified
    (A K Lπ Lᵤπ : Type*) [CommRing A] [IsDomain A]
    [Field K] [Field Lπ] [Field Lᵤπ]
    [Algebra A K] [Algebra K Lπ] [Algebra K Lᵤπ]
    [Algebra A Lπ] [Algebra A Lᵤπ]
    [IsDiscreteValuationRing A] [IsFractionRing A K]
    [IsScalarTower A K Lπ] [IsScalarTower A K Lᵤπ]
    [FiniteDimensional K Lπ] [FiniteDimensional K Lᵤπ]
    (π : A) (u : Aˣ) (απ : Lπ) (αᵤπ : Lᵤπ)
    (hπ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter03QuadraticPolynomial π))
    (hᵤπ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter03QuadraticPolynomial ((u : A) * π)))
    (hrootπ : aeval απ (chapter03QuadraticPolynomial π) = 0)
    (hrootᵤπ :
      aeval αᵤπ (chapter03QuadraticPolynomial ((u : A) * π)) = 0)
    (hgenπ : Algebra.adjoin K ({απ} : Set Lπ) = ⊤)
    (hgenᵤπ : Algebra.adjoin K ({αᵤπ} : Set Lᵤπ) = ⊤)
    (hdegreeπ : Module.finrank K Lπ = 2)
    (hdegreeᵤπ : Module.finrank K Lᵤπ = 2)
    (hdegreeπ_poly : (chapter03QuadraticPolynomial π).natDegree = 2)
    (hdegreeᵤπ_poly :
      (chapter03QuadraticPolynomial ((u : A) * π)).natDegree = 2)
    (vK : Valuation K ℤᵐ⁰) (vLπ : Valuation Lπ ℤᵐ⁰)
    (vLᵤπ : Valuation Lᵤπ ℤᵐ⁰)
    [vK.HasExtension vLπ] [vK.HasExtension vLᵤπ]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vLπ]
    [Valuation.IsRankOneDiscrete vLᵤπ]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hvaluationRing : (vK.valuationSubring : Set K) =
      Set.range (algebraMap A K)) :
    (∃ data : Chapter03FiniteLocalExtensionData K Lπ ℤᵐ⁰ vK vLπ,
      data.e = 2 ∧ data.f = 1) ∧
      (∃ data : Chapter03FiniteLocalExtensionData K Lᵤπ ℤᵐ⁰ vK vLᵤπ,
        data.e = 2 ∧ data.f = 1) := by
  constructor
  · exact chapter03_eisenstein_quadratic_is_totally_ramified
      A K Lπ π (chapter03QuadraticPolynomial π) απ hπ hrootπ hgenπ
      hdegreeπ hdegreeπ_poly vK vLπ hcomplete hvaluationRing
  · exact chapter03_eisenstein_quadratic_is_totally_ramified
      A K Lᵤπ π
        (chapter03QuadraticPolynomial ((u : A) * π)) αᵤπ hᵤπ hrootᵤπ
      hgenᵤπ hdegreeᵤπ hdegreeᵤπ_poly vK vLᵤπ hcomplete hvaluationRing

/-- The square subgroup and square-class group of a field. -/
def chapter03SquaresSubgroup (K : Type*) [Field K] : Subgroup Kˣ :=
  Subgroup.closure (Set.range (fun x : Kˣ => x ^ 2))

abbrev chapter03SquareClassGroup (K : Type*) [Field K] :=
  Kˣ ⧸ chapter03SquaresSubgroup K

/-- Every principal unit is a square in the odd-residue complete DVR case. -/
def chapter03PrincipalUnitSquareCondition
    (A : Type*) [CommRing A] (m : Ideal A) : Prop :=
  ∀ x : A, (∃ y : A, x = 1 + y ∧ y ∈ m) →
    ∃ z : A, z ^ 2 = x

theorem chapter03_complete_odd_dvr_principal_units_are_squares
    (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (h2 : IsUnit (2 : A)) :
    chapter03PrincipalUnitSquareCondition A (IsLocalRing.maximalIdeal A) := by
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hcomplete
  intro x hx
  rcases hx with ⟨y, rfl, hy⟩
  let f : A[X] := X ^ 2 - C (1 + y)
  have hf : f.Monic := by
    exact monic_X_pow_sub_C (1 + y) (by norm_num)
  have happrox : f.eval 1 ∈ IsLocalRing.maximalIdeal A := by
    simpa [f] using (IsLocalRing.maximalIdeal A).neg_mem hy
  have hderivative :
      IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
        (f.derivative.eval 1)) := by
    rw [show f.derivative.eval 1 = (2 : A) by norm_num [f]]
    exact h2.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
  obtain ⟨z, hz, _⟩ :=
    HenselianRing.is_henselian f hf 1 happrox hderivative
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 - (1 + y) = 0 := by simpa [f] using hz
  exact sub_eq_zero.mp hz'

/-- An odd finite field has exactly two square classes. -/
theorem chapter03_finite_odd_field_has_two_square_classes
    (k : Type*) [Field k] [Fintype k]
    [Fintype (chapter03SquareClassGroup k)]
    (hodd : chapter03FiniteOddResidueField k) :
    Fintype.card (chapter03SquareClassGroup k) = 2 := by
  classical
  let q : Subgroup kˣ := chapter03SquaresSubgroup k
  have hq : q = (powMonoidHom 2 : kˣ →* kˣ).range := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨x, rfl⟩
      exact ⟨x, by simp [powMonoidHom_apply]⟩
    · rintro y ⟨x, rfl⟩
      exact Subgroup.subset_closure ⟨x, by simp [powMonoidHom_apply]⟩
  have hcard_units : Nat.card kˣ = Fintype.card k - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  change Fintype.card k % 2 = 1 at hodd
  have hdiv : 2 ∣ Nat.card kˣ := by
    rw [hcard_units]
    omega
  have hindex : q.index = 2 := by
    rw [hq, IsCyclic.index_powMonoidHom_range,
      Nat.gcd_eq_right_iff_dvd.mpr hdiv]
  calc
    Fintype.card (chapter03SquareClassGroup k) =
        Nat.card (kˣ ⧸ chapter03SquaresSubgroup k) := Fintype.card_eq_nat_card
    _ = q.index := by simpa [q] using (Subgroup.index_eq_card q).symm
    _ = 2 := hindex

/-- The local square-class decomposition supplied by principal units and the
residue quotient. -/
def chapter03LocalSquareClassDecomposition
    (K k : Type*) [Field K] [Field k] : Prop :=
    Nonempty
    (chapter03SquareClassGroup K ≃*
      Multiplicative (ZMod 2) × chapter03SquareClassGroup k)

theorem chapter03_principal_units_supply_square_class_decomposition
    (A K k : Type*) [CommRing A] [Field K] [Field k]
    [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A K] [IsFractionRing A K]
    (hresidue : Nonempty (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hprincipal :
      chapter03PrincipalUnitSquareCondition A (IsLocalRing.maximalIdeal A)) :
    chapter03LocalSquareClassDecomposition K k := by
  sorry

theorem chapter03_odd_residue_local_square_classes
    (K k : Type*) [Field K] [Field k] [Fintype k]
    [Fintype (chapter03SquareClassGroup K)]
    (hodd : chapter03FiniteOddResidueField k)
    (hprincipal : chapter03LocalSquareClassDecomposition K k) :
    Fintype.card (chapter03SquareClassGroup K) = 4 := by
  classical
  let _ : Fintype (chapter03SquareClassGroup k) := Fintype.ofFinite _
  rcases hprincipal with ⟨e⟩
  calc
    Fintype.card (chapter03SquareClassGroup K) =
        Fintype.card (Multiplicative (ZMod 2) ×
          chapter03SquareClassGroup k) := Fintype.card_congr e
    _ = Fintype.card (Multiplicative (ZMod 2)) *
          Fintype.card (chapter03SquareClassGroup k) := Fintype.card_prod _ _
    _ = 4 := by
      rw [chapter03_finite_odd_field_has_two_square_classes k hodd]
      norm_num

def chapter03NontrivialSquareClass (K : Type*) [Field K] :=
  {a : chapter03SquareClassGroup K // a ≠ 1}

theorem chapter03_three_nontrivial_quadratic_square_classes
    (K : Type*) [Field K] [Fintype (chapter03SquareClassGroup K)]
    [Fintype (chapter03NontrivialSquareClass K)]
    (hcard : Fintype.card (chapter03SquareClassGroup K) = 4) :
    Fintype.card (chapter03NontrivialSquareClass K) = 3 := by
  let fintypeNot : Fintype {x : chapter03SquareClassGroup K // ¬x = 1} :=
    inferInstanceAs (Fintype (chapter03NontrivialSquareClass K))
  have h :
      Fintype.card {x : chapter03SquareClassGroup K // ¬x = 1} =
        Fintype.card (chapter03SquareClassGroup K) -
          Fintype.card {x : chapter03SquareClassGroup K // x = 1} :=
    @Fintype.card_subtype_compl
      (chapter03SquareClassGroup K) inferInstance
      (fun a : chapter03SquareClassGroup K => a = 1)
      (inferInstanceAs (Fintype {x : chapter03SquareClassGroup K // x = 1})) fintypeNot
  have hone : Fintype.card {x : chapter03SquareClassGroup K // x = 1} = 1 := by
    exact Fintype.card_subtype_eq 1
  rw [hone, hcard] at h
  have hthree : Fintype.card {x : chapter03SquareClassGroup K // ¬x = 1} = 3 := by
    omega
  let e : chapter03NontrivialSquareClass K ≃
      {x : chapter03SquareClassGroup K // ¬x = 1} :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact (Fintype.card_congr e).trans hthree

/-- The quadratic self-base-change algebra. -/
abbrev chapter03QuadraticSelfBaseChange
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] :=
  L ⊗[K] L

/-- Quadratic classes differing by a unit square become isomorphic after scalar
extension to a base in which that square root exists. -/
theorem chapter03_ramified_quadratics_become_isomorphic_after_unramified_base_change
    (K Kᵤ : Type*) [Field K] [Field Kᵤ] [Algebra K Kᵤ]
    (u π : K) (hu : IsUnit u)
    (s : Kᵤ) (hsquare : s ^ 2 = algebraMap K Kᵤ u) :
    letI : Algebra Kᵤ (chapter03QuadraticRootAlgebra K π ⊗[K] Kᵤ) :=
      Algebra.TensorProduct.rightAlgebra
    letI : Algebra Kᵤ (chapter03QuadraticRootAlgebra K (u * π) ⊗[K] Kᵤ) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      ((chapter03QuadraticRootAlgebra K π ⊗[K] Kᵤ) ≃ₐ[Kᵤ]
        (chapter03QuadraticRootAlgebra K (u * π) ⊗[K] Kᵤ)) := by
  letI : Algebra Kᵤ (chapter03QuadraticRootAlgebra K π ⊗[K] Kᵤ) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra Kᵤ (chapter03QuadraticRootAlgebra K (u * π) ⊗[K] Kᵤ) :=
    Algebra.TensorProduct.rightAlgebra
  let R := Kᵤ ⊗[K] K
  let p : K[X] := chapter03QuadraticPolynomial π
  let pu : K[X] := chapter03QuadraticPolynomial (u * π)
  let q : R[X] := p.map Algebra.TensorProduct.includeRight.toRingHom
  let qu : R[X] := pu.map Algebra.TensorProduct.includeRight.toRingHom
  let sR : R :=
    Algebra.TensorProduct.includeLeft (R := K) (S := Kᵤ) (A := Kᵤ) (B := K) s
  let sRi : R :=
    Algebra.TensorProduct.includeLeft (R := K) (S := Kᵤ) (A := Kᵤ) (B := K) s⁻¹
  let B := AdjoinRoot qu
  let ss : B := algebraMap R B sR
  let ssi : B := algebraMap R B sRi
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    have hu0 : u ≠ 0 := hu.ne_zero
    have hmapu : algebraMap K Kᵤ u ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap K Kᵤ)
        (FaithfulSMul.algebraMap_injective K Kᵤ)).2 hu0
    have hzero : algebraMap K Kᵤ u = 0 := by
      simpa using hsquare.symm
    exact hmapu hzero
  have hsRinv : sR * sRi = (1 : R) := by
    dsimp [sR, sRi]
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp [hs0]
    exact (Algebra.TensorProduct.one_def (R := K) (A := Kᵤ) (B := K)).symm
  have hssinv : ss * ssi = 1 := by
    dsimp [ss, ssi]
    rw [← map_mul, hsRinv, map_one]
  have hsRsquare : sR ^ 2 =
      Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) u := by
    dsimp [sR]
    rw [Algebra.TensorProduct.tmul_pow, one_pow, hsquare,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have hssquare : ss ^ 2 =
      algebraMap R B
        (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) u) := by
    dsimp [ss]
    rw [← map_pow, hsRsquare]
    rfl
  let β : B := ssi * AdjoinRoot.root qu
  have hβ : β ^ 2 =
      algebraMap R B
        (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) π) := by
    have hroot : (AdjoinRoot.root qu) ^ 2 =
        algebraMap R B
          (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) (u * π)) := by
      have h : aeval (AdjoinRoot.root qu) qu = 0 := by
        rw [AdjoinRoot.aeval_eq]
        simp
      rw [aeval_def, eval₂_map] at h
      simp [pu, chapter03QuadraticPolynomial, eval₂_sub, eval₂_pow,
        eval₂_X, eval₂_C] at h
      have h' := sub_eq_zero.mp h
      calc
        AdjoinRoot.root qu ^ 2 = (AdjoinRoot.of qu) (1 ⊗ₜ[K] u) *
            (AdjoinRoot.of qu) (1 ⊗ₜ[K] π) := h'
        _ = (AdjoinRoot.of qu) ((1 ⊗ₜ[K] u) * (1 ⊗ₜ[K] π)) := by
          rw [map_mul]
        _ = (AdjoinRoot.of qu) (1 ⊗ₜ[K] (u * π)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp
        _ = algebraMap R B
            (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) (u * π)) := rfl
    dsimp [β]
    rw [mul_pow, hroot]
    have hcoef :
        algebraMap R B
            (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) (u * π)) =
          ss ^ 2 * algebraMap R B
            (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) π) := by
      rw [map_mul, map_mul, hssquare]
    rw [hcoef]
    calc
      ssi ^ 2 * (ss ^ 2 * algebraMap R B
          (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) π)) =
          (ssi * ss) ^ 2 * algebraMap R B
            (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) π) := by
        ring
      _ = algebraMap R B
          (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) π) := by
        rw [mul_comm ssi ss, hssinv]
        simp
  let β' : AdjoinRoot q :=
    algebraMap R (AdjoinRoot q) sR * AdjoinRoot.root q
  have hβ' : β' ^ 2 =
      algebraMap R (AdjoinRoot q)
        (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) (u * π)) := by
    have hroot : (AdjoinRoot.root q) ^ 2 =
        algebraMap R (AdjoinRoot q)
          (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) π) := by
      have h : aeval (AdjoinRoot.root q) q = 0 := by
        rw [AdjoinRoot.aeval_eq]
        simp
      rw [aeval_def, eval₂_map] at h
      simp [p, chapter03QuadraticPolynomial, eval₂_sub, eval₂_pow,
        eval₂_X, eval₂_C] at h
      have h' := sub_eq_zero.mp h
      calc
        AdjoinRoot.root q ^ 2 = (AdjoinRoot.of q) (1 ⊗ₜ[K] π) := h'
        _ = (AdjoinRoot.of q)
            (Algebra.TensorProduct.includeRight
              (R := K) (A := Kᵤ) (B := K) π) := rfl
        _ = algebraMap R (AdjoinRoot q)
            (Algebra.TensorProduct.includeRight
              (R := K) (A := Kᵤ) (B := K) π) := rfl
    have hssquare' :
        (algebraMap R (AdjoinRoot q) sR) ^ 2 =
          algebraMap R (AdjoinRoot q)
            (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) u) := by
      rw [← map_pow, hsRsquare]
    change ((algebraMap R (AdjoinRoot q) sR) * AdjoinRoot.root q) ^ 2 =
      algebraMap R (AdjoinRoot q)
        (Algebra.TensorProduct.includeRight (R := K) (A := Kᵤ) (B := K) (u * π))
    rw [mul_pow, hroot, hssquare']
    calc
      (AdjoinRoot.of q) (1 ⊗ₜ[K] u) * (AdjoinRoot.of q) (1 ⊗ₜ[K] π) =
          (AdjoinRoot.of q) ((1 ⊗ₜ[K] u) * (1 ⊗ₜ[K] π)) := by
        rw [map_mul]
      _ = (AdjoinRoot.of q) (1 ⊗ₜ[K] (u * π)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
  have hβroot : aeval β q = 0 := by
    simpa [q, p, chapter03QuadraticPolynomial, aeval_def, Algebra.smul_def] using
      sub_eq_zero.mpr hβ
  have hβ'root : aeval β' qu = 0 := by
    simpa [qu, pu, chapter03QuadraticPolynomial, aeval_def, Algebra.smul_def,
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul] using
      sub_eq_zero.mpr hβ'
  let φ : AdjoinRoot q →ₐ[R] B :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId R B) β hβroot
  let ψ : B →ₐ[R] AdjoinRoot q :=
    AdjoinRoot.liftAlgHom qu (Algebra.ofId R (AdjoinRoot q)) β' hβ'root
  have hφroot : φ (AdjoinRoot.root q) = β := by
    simpa [φ] using
      (AdjoinRoot.liftAlgHom_root (p := q) (Algebra.ofId R B) β hβroot)
  have hψroot : ψ (AdjoinRoot.root qu) = β' := by
    simpa [ψ] using
      (AdjoinRoot.liftAlgHom_root (p := qu)
        (Algebra.ofId R (AdjoinRoot q)) β' hβ'root)
  have hRiR : sRi * sR = (1 : R) := by
    rw [mul_comm, hsRinv]
  have hφψ : ψ.comp φ = AlgHom.id R _ := by
    ext
    change ψ (φ (AdjoinRoot.root q)) = AdjoinRoot.root q
    rw [hφroot]
    change ψ (ssi * AdjoinRoot.root qu) = AdjoinRoot.root q
    rw [map_mul, hψroot]
    dsimp [ssi, β']
    rw [ψ.commutes]
    change (algebraMap R (AdjoinRoot q) sRi) *
      ((algebraMap R (AdjoinRoot q) sR) * AdjoinRoot.root q) =
        AdjoinRoot.root q
    rw [← mul_assoc, ← map_mul, hRiR, map_one, one_mul]
  have hψφ : φ.comp ψ = AlgHom.id R _ := by
    ext
    change φ (ψ (AdjoinRoot.root qu)) = AdjoinRoot.root qu
    rw [hψroot]
    change φ ((algebraMap R (AdjoinRoot q) sR) * AdjoinRoot.root q) =
      AdjoinRoot.root qu
    rw [map_mul, hφroot]
    rw [φ.commutes]
    dsimp [β, ssi]
    rw [← mul_assoc, ← map_mul, hsRinv, map_one, one_mul]
  let eRoot : AdjoinRoot q ≃ₐ[R] B :=
    AlgEquiv.ofAlgHom φ ψ hψφ hφψ
  let eMiddle : Kᵤ ⊗[K] chapter03QuadraticRootAlgebra K π ≃ₐ[Kᵤ]
      Kᵤ ⊗[K] chapter03QuadraticRootAlgebra K (u * π) := by
    exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
      ((eRoot.restrictScalars Kᵤ).trans
        (AdjoinRoot.tensorAlgEquiv pu qu rfl).symm)
  exact ⟨(Algebra.TensorProduct.commRight K Kᵤ
      (chapter03QuadraticRootAlgebra K π)).symm.trans
    (eMiddle.trans (Algebra.TensorProduct.commRight K Kᵤ
      (chapter03QuadraticRootAlgebra K (u * π))))⟩

/- The tower bookkeeping for the unramified and totally ramified quadratic
stages is recorded independently of a chosen common overfield. -/
theorem chapter03_unramified_then_totally_ramified_stages
    (e₁ f₁ e₂ f₂ e f d : ℕ)
    (hunramified : e₁ = 1 ∧ f₁ = 2)
    (htotallyramified : e₂ = 2 ∧ f₂ = 1)
    (he_tower : e = e₂ * e₁)
    (hf_tower : f = f₂ * f₁)
    (hdegree : d = e * f) :
    e = 2 ∧ f = 2 ∧ d = 4 := by
  rcases hunramified with ⟨rfl, rfl⟩
  rcases htotallyramified with ⟨rfl, rfl⟩
  norm_num at he_tower hf_tower
  constructor
  · exact he_tower
  constructor
  · exact hf_tower
  · norm_num [hdegree, he_tower, hf_tower]

/-- Principal units in a local ring. -/
def chapter03PrincipalUnit
    (A : Type*) [CommRing A] (m : Ideal A) : Type _ :=
  {u : Aˣ // (u : A) - 1 ∈ m}

/-- Squaring preserves the principal-unit subgroup. -/
def chapter03PrincipalUnitSquaringMap
    (A : Type*) [CommRing A] (m : Ideal A) :
    chapter03PrincipalUnit A m → chapter03PrincipalUnit A m := by
  intro u
  refine ⟨u.1 ^ 2, ?_⟩
  change ((u.1 : A) ^ 2 - 1) ∈ m
  have hfactor : (u.1 : A) ^ 2 - 1 =
      (u.1 : A) * ((u.1 : A) - 1) + ((u.1 : A) - 1) := by
    ring
  rw [hfactor]
  exact m.add_mem (m.mul_mem_left _ u.2) u.2

def chapter03PrincipalUnitSquaringBijective
    (A : Type*) [CommRing A] (m : Ideal A) : Prop :=
  Function.Bijective (chapter03PrincipalUnitSquaringMap A m)

/-- The dyadic case does not have the odd-residue principal-unit behavior. -/
-- The qualitative source warning is represented by a conditional cardinality
-- theorem, so its local-DVR hypotheses are explicit here.
theorem chapter03_residue_characteristic_two_needs_a_different_square_class_count
    (A K k : Type*) [CommRing A] [IsDomain A]
    [Field K] [Field k] [Algebra A K]
    [IsDiscreteValuationRing A] [IsFractionRing A K]
    [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfraction : Nonempty (FractionRing A ≃+* K))
    (hresidue : Nonempty
      (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    :
    ¬ chapter03PrincipalUnitSquaringBijective A
      (IsLocalRing.maximalIdeal A) := by
  sorry

theorem chapter03_dyadic_square_classes_do_not_have_the_odd_count
    (K k : Type*) [Field K] [Field k] [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hcard : 4 < Fintype.card (chapter03SquareClassGroup K)) :
    ¬ chapter03LocalSquareClassDecomposition K k := by
  intro hdecomp
  rcases hdecomp with ⟨e⟩
  have hsq : ∀ a : kˣ, a ∈ chapter03SquaresSubgroup k := by
    intro a
    obtain ⟨b, hb⟩ :=
      (PerfectRing.bijective_frobenius (R := k) (p := 2)).2 (a : k)
    have hb0 : b ≠ 0 := by
      intro hb'
      subst b
      have ha0 : (0 : k) = (a : k) := by
        simpa only [pow_two, zero_mul] using hb
      exact a.ne_zero ha0.symm
    let b' : kˣ := Units.mk0 b hb0
    have hpow : b' ^ 2 = a := by
      ext
      exact hb
    exact Subgroup.subset_closure ⟨b', hpow⟩
  have htop : chapter03SquaresSubgroup k = ⊤ :=
    (Subgroup.eq_top_iff' _).2 hsq
  have hsubsingleton : Subsingleton (chapter03SquareClassGroup k) := by
    change Subsingleton (kˣ ⧸ chapter03SquaresSubgroup k)
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  let _ : Fintype (kˣ) := Fintype.ofFinite _
  let _ : Fintype (chapter03SquareClassGroup k) := Fintype.ofFinite _
  have hcardk : Fintype.card (chapter03SquareClassGroup k) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨1, fun y => hsubsingleton.elim y 1⟩
  have heq : Fintype.card (chapter03SquareClassGroup K) =
      Fintype.card (Multiplicative (ZMod 2) × chapter03SquareClassGroup k) :=
    Fintype.card_congr e
  have htwo : Fintype.card (chapter03SquareClassGroup K) = 2 := by
    simpa [hcardk] using heq
  omega

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
