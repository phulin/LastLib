import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section02EquivalentCharacterizations

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
  let _ := hodd
  let _ := hnonsquare
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

private theorem chapter03_fraction_units_equiv
    (A K : Type*) [CommRing A] [Field K] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra A K] [IsFractionRing A K]
    {π : A}
    (hπ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Chapter04Uniformizer A π) :
    Nonempty (Kˣ ≃* Multiplicative ℤ × Aˣ) := by
  classical
  let πK : Kˣ := Units.mk0 (algebraMap A K π) (by simpa using hπ.1)
  let uMap : Aˣ →* Kˣ := Units.map (algebraMap A K).toMonoidHom
  let g : (Multiplicative ℤ × Aˣ) →* Kˣ :=
    { toFun := fun x => πK ^ (Multiplicative.toAdd x.1) * uMap x.2
      map_one' := by simp [πK, uMap]
      map_mul' := by
        rintro ⟨n, u⟩ ⟨m, v⟩
        change πK ^ (Multiplicative.toAdd n + Multiplicative.toAdd m) *
          uMap (u * v) =
          (πK ^ Multiplicative.toAdd n * uMap u) *
            (πK ^ Multiplicative.toAdd m * uMap v)
        rw [zpow_add]
        simp [uMap, mul_assoc, mul_left_comm, mul_comm] }
  have hg_surj : Function.Surjective g := by
    intro x
    obtain ⟨n, u, hu⟩ :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.dvr_fraction_field_unique_normal_form
        A K hπ (Units.ne_zero x)
    refine ⟨(Multiplicative.ofAdd n, u), ?_⟩
    apply Units.ext
    simpa [g, πK, uMap, Units.smul_def, Algebra.smul_def, mul_comm] using hu.1.symm
  have hg_inj : Function.Injective g := by
    intro x y hxy
    obtain ⟨n, u, hu, hu_unique⟩ :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.dvr_fraction_field_unique_normal_form
        A K hπ
          (Units.ne_zero (g x))
    have hx : (g x : K) = (x.2 : A) •
        (algebraMap A K π) ^ (Multiplicative.toAdd x.1) := by
      simp [g, πK, uMap, Algebra.smul_def, mul_comm]
    have hxy' : (g x : K) = (y.2 : A) •
        (algebraMap A K π) ^ (Multiplicative.toAdd y.1) := by
      calc
        (g x : K) = (g y : K) := congrArg Units.val hxy
        _ = (y.2 : A) • (algebraMap A K π) ^ (Multiplicative.toAdd y.1) := by
          simp [g, πK, uMap, Algebra.smul_def, mul_comm]
    have hx' := hu_unique (Multiplicative.toAdd x.1) x.2 hx
    have hy' := hu_unique (Multiplicative.toAdd y.1) y.2 hxy'
    apply Prod.ext
    · exact hx'.1.trans hy'.1.symm
    · exact hx'.2.trans hy'.2.symm
  exact ⟨(MulEquiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm⟩

private def chapter03IntegerParity :
    Multiplicative ℤ →* Multiplicative (ZMod 2) :=
  { toFun := fun n => Multiplicative.ofAdd
        ((Multiplicative.toAdd (α := ℤ) n : ℤ) : ZMod 2)
    map_one' := by rfl
    map_mul' := by
      intro n r
      change ((Multiplicative.toAdd (α := ℤ) n +
          Multiplicative.toAdd (α := ℤ) r : ℤ) : ZMod 2) =
        (Multiplicative.toAdd (α := ℤ) n : ZMod 2) +
          (Multiplicative.toAdd (α := ℤ) r : ZMod 2)
      simp }

private theorem chapter03_integer_parity_surjective :
    Function.Surjective chapter03IntegerParity := by
  intro z
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective
    (Multiplicative.toAdd (α := ZMod 2) z)
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  exact congrArg Multiplicative.ofAdd hn

private theorem chapter03_integer_parity_ker :
    chapter03IntegerParity.ker =
      Subgroup.closure (Set.range (fun n : Multiplicative ℤ => n ^ 2)) := by
  have hsquares_rangeZ :
      Subgroup.closure (Set.range (fun n : Multiplicative ℤ => n ^ 2)) =
        (powMonoidHom 2 : Multiplicative ℤ →* Multiplicative ℤ).range := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      exact ⟨v, by simp [powMonoidHom_apply]⟩
    · rintro u ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, by simp [powMonoidHom_apply]⟩
  apply le_antisymm
  · intro n hn
    have hn0 : (Multiplicative.toAdd (α := ℤ) n : ZMod 2) = 0 := by
      change Multiplicative.toAdd (α := ZMod 2)
          (chapter03IntegerParity n) = 0
      rw [MonoidHom.mem_ker.mp hn]
      rfl
    have hdiv : (2 : ℤ) ∣ Multiplicative.toAdd (α := ℤ) n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hn0
    obtain ⟨r, hr⟩ := hdiv
    apply Subgroup.subset_closure
    refine ⟨Multiplicative.ofAdd r, ?_⟩
    change (Multiplicative.ofAdd r) ^ 2 = n
    rw [pow_two]
    change Multiplicative.ofAdd (r + r) = n
    have hr' : n = Multiplicative.ofAdd (2 * r) := congrArg
      Multiplicative.ofAdd hr
    rw [hr']
    congr 1
    ring
  · intro n hn
    rw [hsquares_rangeZ] at hn
    apply MonoidHom.mem_ker.mpr
    change chapter03IntegerParity n = 1
    obtain ⟨r, hr⟩ := hn
    rw [← hr]
    change chapter03IntegerParity (r ^ 2) = 1
    rw [map_pow]
    rw [show chapter03IntegerParity r = Multiplicative.ofAdd
        ((Multiplicative.toAdd (α := ℤ) r : ℤ) : ZMod 2) by rfl, pow_two]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    simp only [toAdd_ofAdd]
    exact CharTwo.add_self_eq_zero _

private theorem chapter03_quotient_equiv_of_surjective
    (G H : Type*) [Group G] [Group H]
    (sG : Subgroup G) [sG.Normal] (F : G →* H)
    (hF_surj : Function.Surjective F) (hF_ker : F.ker = sG) :
    Nonempty (G ⧸ sG ≃* H) := by
  let eG : G ⧸ sG ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hF_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective F hF_surj)
  exact ⟨eG⟩

private theorem chapter03_square_product_eq_prod
    (A : Type*) [CommRing A]
    (sA : Subgroup Aˣ)
    (sZ : Subgroup (Multiplicative ℤ))
    (sG : Subgroup (Multiplicative ℤ × Aˣ))
    (hsA : sA = Subgroup.closure (Set.range (fun u : Aˣ => u ^ 2)))
    (hsZ : sZ =
      Subgroup.closure (Set.range (fun n : Multiplicative ℤ => n ^ 2)))
    (hsG : sG =
      Subgroup.closure (Set.range
        (fun x : Multiplicative ℤ × Aˣ => x ^ 2))) :
    sG = sZ.prod sA := by
  rw [hsG, hsZ, hsA]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨y, rfl⟩
    change y.1 ^ 2 ∈
        Subgroup.closure (Set.range (fun n : Multiplicative ℤ => n ^ 2)) ∧
      y.2 ^ 2 ∈ Subgroup.closure (Set.range (fun u : Aˣ => u ^ 2))
    constructor
    · exact Subgroup.subset_closure ⟨y.1, rfl⟩
    · exact Subgroup.subset_closure ⟨y.2, rfl⟩
  · rw [← Subgroup.closure_prod
      (show (1 : Multiplicative ℤ) ∈
          Set.range (fun n : Multiplicative ℤ => n ^ 2) by
        exact ⟨1, by simp⟩)
      (show (1 : Aˣ) ∈ Set.range (fun u : Aˣ => u ^ 2) by
        exact ⟨1, by simp⟩)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    apply Subgroup.subset_closure
    refine ⟨(u, v), ?_⟩
    simp [hu, hv]

private theorem chapter03_square_class_product_quotient
    (A k : Type*) [CommRing A] [Field k]
    (sA : Subgroup Aˣ)
    (sZ : Subgroup (Multiplicative ℤ))
    (sG : Subgroup (Multiplicative ℤ × Aˣ))
    (hsquare_prod : sG = sZ.prod sA)
    (parity : Multiplicative ℤ →* Multiplicative (ZMod 2))
    (hparity_surj : Function.Surjective parity)
    (hparity_ker : parity.ker = sZ)
    (redClass : Aˣ →* chapter03SquareClassGroup k)
    (hredClass_surj : Function.Surjective redClass)
    (hredClass_ker : redClass.ker = sA) :
    Nonempty
      (((Multiplicative ℤ × Aˣ) ⧸ sG) ≃*
        Multiplicative (ZMod 2) × chapter03SquareClassGroup k) := by
  classical
  let F : (Multiplicative ℤ × Aˣ) →*
      (Multiplicative (ZMod 2) × chapter03SquareClassGroup k) :=
    { toFun := fun x => (parity x.1, redClass x.2)
      map_one' := by simp
      map_mul' := by
        intro x y
        change (parity (x.1 * y.1), redClass (x.2 * y.2)) =
          (parity x.1 * parity y.1, redClass x.2 * redClass y.2)
        rw [parity.map_mul, redClass.map_mul] }
  have hF_surj : Function.Surjective F := by
    intro z
    obtain ⟨n, hn⟩ := hparity_surj z.1
    obtain ⟨u, hu⟩ := hredClass_surj z.2
    refine ⟨(n, u), ?_⟩
    change (parity n, redClass u) = z
    exact Prod.ext hn hu
  have hker_prod : F.ker = sZ.prod sA := by
    ext x
    change (parity x.1, redClass x.2) = (1, 1) ↔
      x.1 ∈ sZ ∧ x.2 ∈ sA
    simp only [Prod.mk.injEq]
    rw [← MonoidHom.mem_ker, hparity_ker,
      ← MonoidHom.mem_ker, hredClass_ker]
  exact chapter03_quotient_equiv_of_surjective
    (Multiplicative ℤ × Aˣ)
    (Multiplicative (ZMod 2) × chapter03SquareClassGroup k)
    sG F hF_surj (hker_prod.trans hsquare_prod.symm)

private theorem chapter03_square_class_decomposition_of_residue_map
    (A K k : Type*) [CommRing A] [Field K] [Field k]
    (eUnits : Kˣ ≃* Multiplicative ℤ × Aˣ)
    (sA : Subgroup Aˣ)
    (hsA : sA = Subgroup.closure (Set.range (fun u : Aˣ => u ^ 2)))
    (redClass : Aˣ →* chapter03SquareClassGroup k)
    (hredClass_surj : Function.Surjective redClass)
    (hredClass_ker : redClass.ker = sA) :
    Nonempty
      (chapter03SquareClassGroup K ≃*
        Multiplicative (ZMod 2) × chapter03SquareClassGroup k) := by
  classical
  let sK : Subgroup Kˣ := chapter03SquaresSubgroup K
  let sZ : Subgroup (Multiplicative ℤ) :=
    Subgroup.closure (Set.range (fun n : Multiplicative ℤ => n ^ 2))
  let sG : Subgroup (Multiplicative ℤ × Aˣ) :=
    Subgroup.closure (Set.range (fun x : Multiplicative ℤ × Aˣ => x ^ 2))
  let parity : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    chapter03IntegerParity
  have hparity_surj : Function.Surjective parity := by
    simpa [parity] using chapter03_integer_parity_surjective
  have hparity_ker : parity.ker = sZ := by
    change chapter03IntegerParity.ker = sZ
    simpa [sZ] using chapter03_integer_parity_ker
  have hsquare_prod : sG = sZ.prod sA :=
    chapter03_square_product_eq_prod A sA sZ sG hsA (by rfl) (by rfl)
  obtain ⟨eG⟩ := chapter03_square_class_product_quotient
    A k sA sZ sG hsquare_prod parity hparity_surj hparity_ker
      redClass hredClass_surj hredClass_ker
  have he_map : sK.map eUnits.toMonoidHom = sG := by
    apply le_antisymm
    · refine Subgroup.map_le_iff_le_comap.mpr ?_
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨eUnits v, by simp⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := eUnits.surjective v
      refine ⟨w ^ 2, Subgroup.subset_closure ⟨w, rfl⟩, ?_⟩
      simp
  have he_pre : sG.comap eUnits.toMonoidHom = sK := by
    have heUnits_injective : Function.Injective eUnits.toMonoidHom :=
      eUnits.injective
    rw [← Subgroup.comap_map_eq_self_of_injective heUnits_injective sK,
      he_map]
  let φ : Kˣ →* ((Multiplicative ℤ × Aˣ) ⧸ sG) :=
    (QuotientGroup.mk' sG).comp eUnits.toMonoidHom
  have hφ_surj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective sG).comp eUnits.surjective
  have hφ_ker : φ.ker = sK := by
    ext x
    change φ x = 1 ↔ x ∈ sK
    change QuotientGroup.mk' sG (eUnits x) = 1 ↔ x ∈ sK
    rw [show QuotientGroup.mk' sG (eUnits x) = 1 ↔ eUnits x ∈ sG by
      exact QuotientGroup.eq_one_iff _]
    change x ∈ sG.comap eUnits.toMonoidHom ↔ x ∈ sK
    rw [he_pre]
  let eQ : chapter03SquareClassGroup K ≃*
      (Multiplicative ℤ × Aˣ) ⧸ sG :=
    QuotientGroup.liftEquiv sK hφ_surj hφ_ker.symm
  exact ⟨eQ.trans eG⟩

theorem chapter03_principal_units_supply_square_class_decomposition
    (A K k : Type*) [CommRing A] [Field K] [Field k]
    [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A K] [IsFractionRing A K]
    (hresidue : Nonempty (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hprincipal :
      chapter03PrincipalUnitSquareCondition A (IsLocalRing.maximalIdeal A)) :
    chapter03LocalSquareClassDecomposition K k := by
  classical
  let m : Ideal A := IsLocalRing.maximalIdeal A
  obtain ⟨eRes⟩ := hresidue
  let sA : Subgroup Aˣ :=
    Subgroup.closure (Set.range (fun u : Aˣ => u ^ 2))
  let sK : Subgroup Kˣ := chapter03SquaresSubgroup K
  let sk : Subgroup kˣ := chapter03SquaresSubgroup k
  have hsquares_rangeK :
      sK = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    dsimp [sK, chapter03SquaresSubgroup]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      exact ⟨v, by simp [powMonoidHom_apply]⟩
    · rintro u ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, by simp [powMonoidHom_apply]⟩
  have hsquares_rangeK' :
      sk = (powMonoidHom 2 : kˣ →* kˣ).range := by
    dsimp [sk, chapter03SquaresSubgroup]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      exact ⟨v, by simp [powMonoidHom_apply]⟩
    · rintro u ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, by simp [powMonoidHom_apply]⟩
  have hsquares_rangeA :
      sA = (powMonoidHom 2 : Aˣ →* Aˣ).range := by
    dsimp [sA]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      exact ⟨v, by simp [powMonoidHom_apply]⟩
    · rintro u ⟨v, rfl⟩
      exact Subgroup.subset_closure ⟨v, by simp [powMonoidHom_apply]⟩
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Chapter04Uniformizer A π :=
    ⟨hπirr.ne_zero, hπirr.maximalIdeal_eq⟩
  obtain ⟨eUnits⟩ := chapter03_fraction_units_equiv A K hπ
  let red : Aˣ →* kˣ :=
    (Units.map eRes.toMonoidHom).comp
      (Units.map (IsLocalRing.residue A).toMonoidHom)
  have hred0_surj :
      Function.Surjective (Units.map (IsLocalRing.residue A).toMonoidHom) := by
    exact IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue A) IsLocalRing.residue_surjective
      (inferInstance : IsLocalHom (IsLocalRing.residue A))
  have hredRes_surj :
      Function.Surjective (Units.map eRes.toMonoidHom) := by
    intro u
    refine ⟨Units.map eRes.symm.toMonoidHom u, ?_⟩
    apply Units.ext
    simp
  have hred_surj : Function.Surjective red := hredRes_surj.comp hred0_surj
  have hred_eq_one_iff (u : Aˣ) :
      red u = 1 ↔ (u : A) - 1 ∈ m := by
    constructor
    · intro hu
      have huq : Ideal.Quotient.mk m (u : A) = 1 := by
        apply eRes.injective
        have huval := congrArg Units.val hu
        simpa [red, m, IsLocalRing.residue] using huval
      have hzero : Ideal.Quotient.mk m ((u : A) - 1) = 0 := by
        rw [map_sub, huq]
        simp
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    · intro hu
      have hzero : Ideal.Quotient.mk m ((u : A) - 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hu
      have huq : Ideal.Quotient.mk m (u : A) = 1 := by
        have : Ideal.Quotient.mk m (u : A) - 1 = 0 := by
          simpa [map_sub] using hzero
        exact sub_eq_zero.mp this
      apply Units.ext
      change eRes (Ideal.Quotient.mk m (u : A)) = 1
      rw [huq, map_one]
  have hprincipal_units : red.ker ≤ sA := by
    intro u hu
    have hu1 : red u = 1 := MonoidHom.mem_ker.mp hu
    have hu_mem : (u : A) - 1 ∈ m := (hred_eq_one_iff u).mp hu1
    obtain ⟨z, hz⟩ := hprincipal (u : A)
      ⟨(u : A) - 1, by ring, hu_mem⟩
    have hz0 : z ≠ 0 := by
      intro hz0
      have hu0 : (u : A) = 0 := by
        rw [← hz, hz0]
        simp
      exact (Units.ne_zero u) hu0
    have hzpow : IsUnit (z * z) := by
      rw [← pow_two, hz]
      exact Units.isUnit u
    have hzunit : IsUnit z := isUnit_of_mul_isUnit_left hzpow
    let zu : Aˣ := hzunit.unit
    have hzu : zu ^ 2 = u := by
      apply Units.ext
      simpa [zu, hzunit.unit_spec] using hz
    exact Subgroup.subset_closure ⟨zu, hzu⟩
  let redClass : Aˣ →* chapter03SquareClassGroup k :=
    (QuotientGroup.mk' sk).comp red
  have hredClass_surj : Function.Surjective redClass :=
    (QuotientGroup.mk'_surjective sk).comp hred_surj
  have hredClass_ker : redClass.ker = sA := by
    apply le_antisymm
    · intro u hu
      have huq : red u ∈ sk := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact MonoidHom.mem_ker.mp hu
      rw [hsquares_rangeK'] at huq
      obtain ⟨v, hv⟩ := huq
      obtain ⟨w, hw⟩ := hred_surj v
      have hdiv : u / w ^ 2 ∈ red.ker := by
        apply MonoidHom.mem_ker.mpr
        change red (u / w ^ 2) = 1
        rw [_root_.map_div, map_pow, hw]
        rw [show red u = v ^ 2 by simpa [powMonoidHom_apply] using hv.symm]
        simp
      have hdivsq : u / w ^ 2 ∈ sA := hprincipal_units hdiv
      have hwsq : w ^ 2 ∈ sA :=
        Subgroup.subset_closure ⟨w, rfl⟩
      have hfactor : u = (u / w ^ 2) * w ^ 2 :=
        (div_mul_cancel u (w ^ 2)).symm
      rw [hfactor]
      exact sA.mul_mem hdivsq hwsq
    · refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨v, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply (QuotientGroup.eq_one_iff _).mpr
      exact Subgroup.subset_closure ⟨red v, by simp⟩
  exact chapter03_square_class_decomposition_of_residue_map
    A K k eUnits sA (by rfl) redClass hredClass_surj hredClass_ker

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
  let _ : Algebra Kᵤ (chapter03QuadraticRootAlgebra K π ⊗[K] Kᵤ) :=
    Algebra.TensorProduct.rightAlgebra
  let _ : Algebra Kᵤ (chapter03QuadraticRootAlgebra K (u * π) ⊗[K] Kᵤ) :=
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
  classical
  let _ := hcomplete
  let _ := hfraction
  intro hbij
  obtain ⟨e⟩ := hresidue
  have h2 : (2 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply e.injective
    change e (2 : A ⧸ IsLocalRing.maximalIdeal A) = e 0
    calc
      e (2 : A ⧸ IsLocalRing.maximalIdeal A) = (2 : k) := map_natCast e 2
      _ = 0 := CharP.cast_eq_zero k 2
      _ = e 0 := (map_zero e).symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hπ_not_m2 : π ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
    intro hπ2
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hπ2
    obtain ⟨c, hc⟩ := hπ2
    have hmul : (1 : A) = π * c := by
      apply (mul_left_cancel₀ hπ.ne_zero)
      calc
        π * 1 = π := mul_one π
        _ = π ^ 2 * c := hc
        _ = π * (π * c) := by ring
    have hunit : IsUnit π :=
      isUnit_iff_dvd_one.mpr ⟨c, hmul⟩
    exact hπ.not_isUnit hunit
  have hneg_nonunit : -π ∈ nonunits A := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact (IsLocalRing.maximalIdeal A).neg_mem hπmem
  have hunit_one_add : IsUnit (1 + π) := by
    have ht := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-π) hneg_nonunit
    simpa [sub_neg_eq_add] using ht
  let u : Aˣ := hunit_one_add.unit
  have huval : (u : A) = 1 + π := IsUnit.unit_spec hunit_one_add
  have huprincipal : (u : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
    simpa [huval] using hπmem
  let x : chapter03PrincipalUnit A (IsLocalRing.maximalIdeal A) :=
    ⟨u, huprincipal⟩
  rcases hbij.2 x with ⟨y, hy⟩
  have hsq : (y.1 : A) ^ 2 = (u : A) := by
    have h := congrArg
      (fun z : chapter03PrincipalUnit A (IsLocalRing.maximalIdeal A) => (z.1 : A)) hy
    simpa [chapter03PrincipalUnitSquaringMap] using h
  let a : A := (y.1 : A) - 1
  have ha : a ∈ IsLocalRing.maximalIdeal A := y.2
  have hya : (y.1 : A) = 1 + a := by
    simp [a]
  have hrel : π = (2 : A) * a + a ^ 2 := by
    calc
      π = (y.1 : A) ^ 2 - 1 := by rw [hsq, huval]; ring
      _ = (1 + a) ^ 2 - 1 := by rw [hya]
      _ = (2 : A) * a + a ^ 2 := by ring
  have h2a : (2 : A) * a ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    simpa [pow_two] using
      (Ideal.mul_mem_mul h2 ha)
  have haa : a ^ 2 ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    simpa [pow_two] using
      (Ideal.mul_mem_mul ha ha)
  have hπ2 : π ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    rw [hrel]
    exact (IsLocalRing.maximalIdeal A) ^ 2 |>.add_mem h2a haa
  exact hπ_not_m2 hπ2

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
