import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section02CharacteristicPolynomialsAndIntegralRestriction
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section04FactorizationOfTheMaximalIdeal
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open IntermediateField
open scoped BigOperators Polynomial

/-! ## 4.7. Minimal polynomials and multiplicities -/

/- The trace formula records the `[L : K(x)]` multiplicity (§4.7). -/
theorem chapter04_trace_minpoly_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x =
      Module.finrank (K⟮x⟯) L * -(minpoly K x).nextCoeff := by
  exact trace_eq_finrank_mul_minpoly_nextCoeff K x

/- The norm formula records the same multiplicity (§4.7). -/
theorem chapter04_norm_minpoly_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      (((-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^
        Module.finrank (K⟮x⟯) L) := by
  rw [Algebra.norm_eq_norm_adjoin K x]
  rw [← IntermediateField.adjoin.powerBasis_gen (Algebra.IsIntegral.isIntegral x)]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  simp only [IntermediateField.adjoin.powerBasis, minpoly_gen]

/- Purely inseparable minimal polynomials are Frobenius powers (§4.7). -/
theorem chapter04_purely_inseparable_minpoly_shape
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (p : ℕ) [ExpChar K p] (x : L) :
    ∃ r : ℕ, ∃ a : K,
      minpoly K x = (Polynomial.X : K[X]) ^ (p ^ r) - Polynomial.C a := by
  exact IsPurelyInseparable.minpoly_eq_X_pow_sub_C K p x

/- The trace vanishes for the purely inseparable minimal-polynomial shapes
from §4.7, while the norm retains the constant term. -/
theorem chapter04_purely_inseparable_generator_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [Fact p.Prime] [CharP K p]
    (α : L) (a : K) (hpower : α ^ p = algebraMap K L a)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = p) :
    Algebra.norm K α = (-1 : K) ^ (p + 1) * a := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hgen' : K⟮α⟯ = (⊤ : IntermediateField K L) :=
    IntermediateField.adjoin_eq_top_of_algebra K ({α} : Set L) hgen
  have hminpoly_degree : (minpoly K α).natDegree = p := by
    rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hgen']
    simpa using hdegree
  have hminpoly : minpoly K α =
      (Polynomial.X : K[X]) ^ p - Polynomial.C a := by
    symm
    apply minpoly.unique
    · exact Polynomial.monic_X_pow_sub_C _ hp0
    · simp [Polynomial.aeval_def, hpower]
    · intro q hq hqroot
      rw [Polynomial.degree_X_pow_sub_C hp_pos,
        Polynomial.degree_eq_natDegree hq.ne_zero]
      have hmin := minpoly.min K α hq hqroot
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero
        (Algebra.IsIntegral.isIntegral α)),
        Polynomial.degree_eq_natDegree hq.ne_zero] at hmin
      have hmin' : p ≤ q.natDegree := by simpa [hminpoly_degree] using hmin
      exact_mod_cast hmin'
  rw [chapter04_norm_minpoly_formula K L α, hminpoly]
  have hfinrank : Module.finrank (K⟮α⟯) L = 1 := by
    rw [hgen']
    exact IntermediateField.finrank_top
  rw [hfinrank]
  simp only [Polynomial.natDegree_X_pow_sub_C, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, if_neg hp0.symm, Polynomial.coeff_C_zero,
    zero_sub, pow_succ]
  ring

/- Coefficients of the minimal polynomial of an integral element lie in the
integrally closed base ring (§4.7). -/
theorem chapter04_integral_minpoly_coefficients_in_base
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    ∀ i : ℕ, ∃ a : A,
      algebraMap A K a = (minpoly K (algebraMap B L x)).coeff i := by
  intro i
  refine ⟨(minpoly A x).coeff i, ?_⟩
  rw [minpoly.isIntegrallyClosed_eq_field_fractions (R := A) (S := B) K L
    (Algebra.IsIntegral.isIntegral (R := A) x), Polynomial.coeff_map]

/- A unit has a unit constant coefficient in its minimal polynomial (§4.7). -/
theorem chapter04_integral_unit_minpoly_constant_coefficient_is_unit
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) (hx : IsUnit x) :
    ∃ u : Aˣ,
      algebraMap A K (u : A) =
        (minpoly K (algebraMap B L x)).coeff 0 := by
  rcases chapter04_integral_minpoly_coefficients_in_base A B K L x 0 with
    ⟨a, ha⟩
  rcases chapter04_norm_of_integral_unit_is_base_unit A B K L
      hx.unit with ⟨u, hu⟩
  rw [hx.unit_spec] at hu
  let m := Module.finrank (K⟮algebraMap B L x⟯) L
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hnorm := chapter04_norm_minpoly_formula K L (algebraMap B L x)
  have heqK : algebraMap A K (((-1 : A) ^
      (minpoly K (algebraMap B L x)).natDegree * a) ^ m) =
      algebraMap A K (u : A) := by
    calc
      algebraMap A K (((-1 : A) ^
          (minpoly K (algebraMap B L x)).natDegree * a) ^ m) =
          ((-1 : K) ^ (minpoly K (algebraMap B L x)).natDegree *
            algebraMap A K a) ^ m := by simp
      _ = Algebra.norm K (algebraMap B L x) := by
        rw [ha]
        exact hnorm.symm
      _ = algebraMap A K (u : A) := hu.symm
  have heqA : ((-1 : A) ^
      (minpoly K (algebraMap B L x)).natDegree * a) ^ m = (u : A) :=
    IsFractionRing.injective A K heqK
  have hpow : IsUnit (((-1 : A) ^
      (minpoly K (algebraMap B L x)).natDegree * a) ^ m) := by
    rw [heqA]
    exact u.isUnit
  have hbase : IsUnit ((-1 : A) ^
      (minpoly K (algebraMap B L x)).natDegree * a) :=
    (isUnit_pow_iff hm).mp hpow
  have haunit : IsUnit a := (IsUnit.mul_iff.mp hbase).2
  refine ⟨haunit.unit, ?_⟩
  rw [haunit.unit_spec, ha]

/-
The totally ramified uniformizer case has Eisenstein shape (§4.7).  The
conclusion uses Book 1 Chapter 12's coefficient-level Eisenstein interface.
-/
theorem chapter04_totally_ramified_uniformizer_minpoly_is_eisenstein
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal A)] (πA : A) (x : B)
    (hπA : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.isUniformizerElement (R := A) πA)
    (hπB : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.isUniformizerElement (R := B) x)
    (hP : P = IsLocalRing.maximalIdeal B)
    (htotal : P.ramificationIdx A = Module.finrank K L ∧
      P.inertiaDeg A = 1)
    (hgen : Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤) :
    ∃ f : A[X], f.Monic ∧
      Polynomial.map (algebraMap A K) f =
        minpoly K (algebraMap B L x) ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πA f := by
  refine ⟨minpoly A x, ?_, ?_, ?_⟩
  · exact minpoly.monic (Algebra.IsIntegral.isIntegral x)
  · apply Polynomial.ext
    intro i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions (R := A) (S := B) K L
      (Algebra.IsIntegral.isIntegral (R := A) x), Polynomial.coeff_map]
  · unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
    refine ⟨minpoly.monic (Algebra.IsIntegral.isIntegral x), ?_⟩
    have hgen' : K⟮algebraMap B L x⟯ = (⊤ : IntermediateField K L) :=
      IntermediateField.adjoin_eq_top_of_algebra K ({algebraMap B L x} : Set L) hgen
    have hdegK : (minpoly K (algebraMap B L x)).natDegree = Module.finrank K L := by
      rw [← IntermediateField.adjoin.finrank
        (Algebra.IsIntegral.isIntegral (algebraMap B L x)), hgen']
      simp only [IntermediateField.finrank_top']
    have hmapdeg : (minpoly A x).natDegree =
        (minpoly K (algebraMap B L x)).natDegree := by
      have hmap : Polynomial.map (algebraMap A K) (minpoly A x) =
          minpoly K (algebraMap B L x) := by
        apply Polynomial.ext
        intro i
        rw [minpoly.isIntegrallyClosed_eq_field_fractions (R := A) (S := B) K L
          (Algebra.IsIntegral.isIntegral (R := A) x), Polynomial.coeff_map]
      simpa [hmap] using
        (Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A K)
          (minpoly A x)).symm
    have hm0 : IsLocalRing.maximalIdeal A ≠ (⊥ : Ideal A) :=
      IsDiscreteValuationRing.not_a_field A
    have hprimes : (IsLocalRing.maximalIdeal A).primesOver B = {P} := by
      rw [IsLocalRing.primesOver_eq B hm0, hP]
    have hmapm : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        P ^ Module.finrank K L := by
      rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_global_ideal_factorization
        A B (IsLocalRing.maximalIdeal A) hm0]
      simp [hprimes, htotal.1]
    have hPspan : P = Ideal.span ({x} : Set B) := by
      rw [hP]
      exact hπB.2
    have hPpow : P ^ Module.finrank K L =
        Ideal.span ({x ^ Module.finrank K L} : Set B) := by
      rw [hPspan]
      simp [Ideal.span_singleton_pow]
    have hx0 : x ≠ 0 := by
      intro hx
      apply IsDiscreteValuationRing.not_a_field B
      rw [hπB.2, hx, Ideal.span_singleton_zero]
    have hxirr : Irreducible x :=
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x hx0 hπB.2
    have hcoeff_ge (i : ℕ) (hi : i < (minpoly A x).natDegree)
        (hci : (minpoly A x).coeff i ∈ IsLocalRing.maximalIdeal A) :
        (Module.finrank K L : ℕ∞) ≤
          IsDiscreteValuationRing.addVal B
            (algebraMap A B ((minpoly A x).coeff i)) := by
      have hmem : algebraMap A B ((minpoly A x).coeff i) ∈
          P ^ Module.finrank K L := by
        rw [← hmapm]
        exact Ideal.mem_map_of_mem (algebraMap A B) hci
      rw [hPpow] at hmem
      rw [Ideal.mem_span_singleton] at hmem
      have hle := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hmem
      simpa only [hxirr.addVal_pow] using hle
    classical
    have hdegree_pos : 0 < (minpoly A x).natDegree := by
      rw [hmapdeg, hdegK]
      exact Module.finrank_pos
    let terms : ℕ → B := fun j ↦
      algebraMap A B ((minpoly A x).coeff j) * x ^ j
    have hroot :
        Finset.sum (Finset.range ((minpoly A x).natDegree + 1)) terms = 0 := by
      simpa [terms, Polynomial.aeval_eq_sum_range, Algebra.smul_def] using
        (minpoly.aeval A x)
    have hterm_value (j : ℕ) :
        IsDiscreteValuationRing.addVal B (terms j) =
          IsDiscreteValuationRing.addVal B
              (algebraMap A B ((minpoly A x).coeff j)) + (j : ℕ∞) := by
      dsimp [terms]
      rw [IsDiscreteValuationRing.addVal_mul, hxirr.addVal_pow]
    have hterm_unit_value (j : ℕ)
        (hjunit : IsUnit ((minpoly A x).coeff j)) :
        IsDiscreteValuationRing.addVal B (terms j) = (j : ℕ∞) := by
      rw [hterm_value]
      have hmapunit :
          IsUnit (algebraMap A B ((minpoly A x).coeff j)) :=
        hjunit.map (algebraMap A B)
      obtain ⟨u, hu⟩ := hmapunit
      rw [← hu, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
    have hno_lower_unit (i : ℕ) (hi : i < (minpoly A x).natDegree)
        (hiunit : IsUnit ((minpoly A x).coeff i)) : False := by
      let U : Finset ℕ := (Finset.range (minpoly A x).natDegree).filter
        (fun j => IsUnit ((minpoly A x).coeff j))
      have hU : U.Nonempty := by
        refine ⟨i, ?_⟩
        simp [U, hi, hiunit]
      let i₀ : ℕ := U.min' hU
      have hi₀U : i₀ ∈ U := by
        exact Finset.min'_mem U hU
      have hi₀U' : i₀ ∈
          Finset.filter (fun j => IsUnit ((minpoly A x).coeff j))
            (Finset.range (minpoly A x).natDegree) := by
        simpa [U] using hi₀U
      have hi₀lt : i₀ < (minpoly A x).natDegree := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp hi₀U').1
      have hi₀unit : IsUnit ((minpoly A x).coeff i₀) :=
        (Finset.mem_filter.mp hi₀U').2
      have hterm_i₀ : terms i₀ ≠ 0 := by
        dsimp [terms]
        exact mul_ne_zero (hi₀unit.map (algebraMap A B)).ne_zero
          (pow_ne_zero _ hx0)
      have hleast :
          ∀ j : ℕ, j ∈ Finset.range ((minpoly A x).natDegree + 1) →
            j ≠ i₀ →
              IsDiscreteValuationRing.addVal B (terms i₀) <
                IsDiscreteValuationRing.addVal B (terms j) := by
        intro j hj hji
        have hjle : j ≤ (minpoly A x).natDegree :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        by_cases hjlower : j < (minpoly A x).natDegree
        · by_cases hjunit : IsUnit ((minpoly A x).coeff j)
          · have hjU : j ∈ U := by
              simp [U, hjlower, hjunit]
            have hminle : i₀ ≤ j := by
              exact Finset.min'_le U j hjU
            have hijlt : i₀ < j :=
              lt_of_le_of_ne hminle (Ne.symm hji)
            rw [hterm_unit_value i₀ hi₀unit, hterm_unit_value j hjunit]
            exact_mod_cast hijlt
          · have hjmax : (minpoly A x).coeff j ∈ IsLocalRing.maximalIdeal A := by
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
              exact hjunit
            have hcoef := hcoeff_ge j hjlower hjmax
            have hterm_ge :
                (Module.finrank K L : ℕ∞) ≤
                  IsDiscreteValuationRing.addVal B (terms j) := by
              calc
                (Module.finrank K L : ℕ∞) ≤
                    IsDiscreteValuationRing.addVal B
                      (algebraMap A B ((minpoly A x).coeff j)) := hcoef
                _ ≤ IsDiscreteValuationRing.addVal B
                      (algebraMap A B ((minpoly A x).coeff j)) + (j : ℕ∞) :=
                  le_add_of_nonneg_right zero_le
                _ = IsDiscreteValuationRing.addVal B (terms j) :=
                  (hterm_value j).symm
            have hi₀_lt_finrank :
                (i₀ : ℕ∞) < (Module.finrank K L : ℕ∞) := by
              have hnat : i₀ < Module.finrank K L := by
                calc
                  i₀ < (minpoly A x).natDegree := hi₀lt
                  _ = (minpoly K (algebraMap B L x)).natDegree := hmapdeg
                  _ = Module.finrank K L := hdegK
              exact_mod_cast hnat
            rw [hterm_unit_value i₀ hi₀unit]
            exact hi₀_lt_finrank.trans_le hterm_ge
        · have hjeq : j = (minpoly A x).natDegree :=
            Nat.le_antisymm hjle (Nat.le_of_not_gt hjlower)
          subst j
          have hlead :
              (minpoly A x).coeff (minpoly A x).natDegree = 1 :=
            (minpoly.monic (Algebra.IsIntegral.isIntegral x)).coeff_natDegree
          have hleadunit :
              IsUnit ((minpoly A x).coeff (minpoly A x).natDegree) := by
            rw [hlead]
            exact isUnit_one
          rw [hterm_unit_value i₀ hi₀unit,
            hterm_unit_value _ hleadunit]
          exact_mod_cast hi₀lt
      have hlt :
          IsDiscreteValuationRing.addVal B (terms i₀) <
            IsDiscreteValuationRing.addVal B
              (∑ j ∈ (Finset.range ((minpoly A x).natDegree + 1)) \ {i₀},
                terms j) := by
        apply (IsDiscreteValuationRing.addVal B).map_lt_sum
        · intro htop
          exact hterm_i₀
            (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
        · intro j hj
          exact hleast j (Finset.mem_sdiff.mp hj).1 (by
            intro h
            exact (Finset.mem_sdiff.mp hj).2 (by simp [h]))
      have hdecomp :=
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem
          (s := Finset.range ((minpoly A x).natDegree + 1))
          (i := i₀) (Finset.mem_range.mpr (Nat.lt_succ_of_lt hi₀lt)) terms
      have hzero :
          terms i₀ +
              (∑ j ∈ (Finset.range ((minpoly A x).natDegree + 1)) \ {i₀},
                terms j) = 0 := by
        rw [← hdecomp]
        exact hroot
      have hcancel :=
        AddValuation.map_add_eq_of_lt_left (IsDiscreteValuationRing.addVal B) hlt
      rw [hzero, AddValuation.map_zero] at hcancel
      have hne :
          IsDiscreteValuationRing.addVal B (terms i₀) ≠ (⊤ : ℕ∞) := by
        intro htop
        exact hterm_i₀
          (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
      exact hne hcancel.symm
    refine ⟨?_, ?_, ?_, hπA.2.symm⟩
    · rw [hmapdeg, hdegK]
      exact Module.finrank_pos
    · intro i hi
      classical
      rw [← hπA.2]
      by_contra hnot
      have hiunit : IsUnit ((minpoly A x).coeff i) := by
        by_contra h
        apply hnot
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact h
      let U : Finset ℕ := (Finset.range (minpoly A x).natDegree).filter
        (fun j => IsUnit ((minpoly A x).coeff j))
      have hU : U.Nonempty := by
        refine ⟨i, ?_⟩
        simp [U, hi, hiunit]
      let i₀ : ℕ := U.min' hU
      have hi₀U : i₀ ∈ U := by
        exact Finset.min'_mem U hU
      have hi₀U' : i₀ ∈
          Finset.filter (fun j => IsUnit ((minpoly A x).coeff j))
            (Finset.range (minpoly A x).natDegree) := by
        simpa [U] using hi₀U
      have hi₀lt : i₀ < (minpoly A x).natDegree := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp hi₀U').1
      have hi₀unit : IsUnit ((minpoly A x).coeff i₀) :=
        (Finset.mem_filter.mp hi₀U').2
      let terms : ℕ → B := fun j ↦
        algebraMap A B ((minpoly A x).coeff j) * x ^ j
      have hroot :
          Finset.sum (Finset.range ((minpoly A x).natDegree + 1)) terms = 0 := by
        simpa [terms, Polynomial.aeval_eq_sum_range, Algebra.smul_def] using
          (minpoly.aeval A x)
      have hterm_value (j : ℕ) :
          IsDiscreteValuationRing.addVal B (terms j) =
            IsDiscreteValuationRing.addVal B
                (algebraMap A B ((minpoly A x).coeff j)) + (j : ℕ∞) := by
        dsimp [terms]
        rw [IsDiscreteValuationRing.addVal_mul, hxirr.addVal_pow]
      have hterm_unit_value (j : ℕ)
          (hjunit : IsUnit ((minpoly A x).coeff j)) :
          IsDiscreteValuationRing.addVal B (terms j) = (j : ℕ∞) := by
        rw [hterm_value]
        have hmapunit :
            IsUnit (algebraMap A B ((minpoly A x).coeff j)) :=
          hjunit.map (algebraMap A B)
        obtain ⟨u, hu⟩ := hmapunit
        rw [← hu, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
      have hterm_i₀ : terms i₀ ≠ 0 := by
        dsimp [terms]
        exact mul_ne_zero (hi₀unit.map (algebraMap A B)).ne_zero
          (pow_ne_zero _ hx0)
      have hleast :
          ∀ j : ℕ, j ∈ Finset.range ((minpoly A x).natDegree + 1) →
            j ≠ i₀ →
              IsDiscreteValuationRing.addVal B (terms i₀) <
                IsDiscreteValuationRing.addVal B (terms j) := by
        intro j hj hji
        have hjle : j ≤ (minpoly A x).natDegree :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        by_cases hjlower : j < (minpoly A x).natDegree
        · by_cases hjunit : IsUnit ((minpoly A x).coeff j)
          · have hjU : j ∈ U := by
              simp [U, hjlower, hjunit]
            have hminle : i₀ ≤ j := by
              exact Finset.min'_le U j hjU
            have hijlt : i₀ < j :=
              lt_of_le_of_ne hminle (Ne.symm hji)
            rw [hterm_unit_value i₀ hi₀unit, hterm_unit_value j hjunit]
            exact_mod_cast hijlt
          · have hjmax : (minpoly A x).coeff j ∈ IsLocalRing.maximalIdeal A := by
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
              exact hjunit
            have hcoef := hcoeff_ge j hjlower hjmax
            have hterm_ge :
                (Module.finrank K L : ℕ∞) ≤
                  IsDiscreteValuationRing.addVal B (terms j) := by
              calc
                (Module.finrank K L : ℕ∞) ≤
                    IsDiscreteValuationRing.addVal B
                      (algebraMap A B ((minpoly A x).coeff j)) := hcoef
                _ ≤ IsDiscreteValuationRing.addVal B
                      (algebraMap A B ((minpoly A x).coeff j)) + (j : ℕ∞) :=
                  le_add_of_nonneg_right zero_le
                _ = IsDiscreteValuationRing.addVal B (terms j) :=
                  (hterm_value j).symm
            have hi₀_lt_finrank :
                (i₀ : ℕ∞) < (Module.finrank K L : ℕ∞) := by
              have hnat : i₀ < Module.finrank K L := by
                calc
                  i₀ < (minpoly A x).natDegree := hi₀lt
                  _ = (minpoly K (algebraMap B L x)).natDegree := hmapdeg
                  _ = Module.finrank K L := hdegK
              exact_mod_cast hnat
            rw [hterm_unit_value i₀ hi₀unit]
            exact hi₀_lt_finrank.trans_le hterm_ge
        · have hjeq : j = (minpoly A x).natDegree :=
            Nat.le_antisymm hjle (Nat.le_of_not_gt hjlower)
          subst j
          have hlead :
              (minpoly A x).coeff (minpoly A x).natDegree = 1 :=
            (minpoly.monic (Algebra.IsIntegral.isIntegral x)).coeff_natDegree
          have hleadunit :
              IsUnit ((minpoly A x).coeff (minpoly A x).natDegree) := by
            rw [hlead]
            exact isUnit_one
          rw [hterm_unit_value i₀ hi₀unit,
            hterm_unit_value _ hleadunit]
          exact_mod_cast hi₀lt
      have hlt :
          IsDiscreteValuationRing.addVal B (terms i₀) <
            IsDiscreteValuationRing.addVal B
              (∑ j ∈ (Finset.range ((minpoly A x).natDegree + 1)) \ {i₀},
                terms j) := by
        apply (IsDiscreteValuationRing.addVal B).map_lt_sum
        · intro htop
          exact hterm_i₀
            (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
        · intro j hj
          exact hleast j (Finset.mem_sdiff.mp hj).1 (by
            intro h
            exact (Finset.mem_sdiff.mp hj).2 (by simp [h]))
      have hdecomp :=
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem
          (s := Finset.range ((minpoly A x).natDegree + 1))
          (i := i₀) (Finset.mem_range.mpr (Nat.lt_succ_of_lt hi₀lt)) terms
      have hzero :
          terms i₀ +
              (∑ j ∈ (Finset.range ((minpoly A x).natDegree + 1)) \ {i₀},
                terms j) = 0 := by
        rw [← hdecomp]
        exact hroot
      have hcancel :=
        AddValuation.map_add_eq_of_lt_left (IsDiscreteValuationRing.addVal B) hlt
      rw [hzero, AddValuation.map_zero] at hcancel
      have hne :
        IsDiscreteValuationRing.addVal B (terms i₀) ≠ (⊤ : ℕ∞) :=
        by
          intro htop
          exact hterm_i₀
            (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
      exact hne hcancel.symm
    · intro hconst
      change (minpoly A x).coeff 0 ∈ Ideal.span {πA ^ 2} at hconst
      have hcoeff_mem (j : ℕ) (hj : j < (minpoly A x).natDegree) :
          (minpoly A x).coeff j ∈ IsLocalRing.maximalIdeal A := by
        by_contra hnot
        have hjunit : IsUnit ((minpoly A x).coeff j) := by
          by_contra hnu
          apply hnot
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          exact hnu
        exact hno_lower_unit j hj hjunit
      have hπAmax : πA ∈ IsLocalRing.maximalIdeal A := by
        rw [hπA.2]
        exact Ideal.mem_span_singleton_self _
      have hπmap : algebraMap A B πA ∈ P ^ Module.finrank K L := by
        rw [← hmapm]
        exact Ideal.mem_map_of_mem (algebraMap A B) hπAmax
      rw [hPpow] at hπmap
      have hπdvd : x ^ Module.finrank K L ∣ algebraMap A B πA :=
        Ideal.mem_span_singleton.mp hπmap
      have hπval :
          (Module.finrank K L : ℕ∞) ≤
            IsDiscreteValuationRing.addVal B (algebraMap A B πA) := by
        have h := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hπdvd
        simpa only [hxirr.addVal_pow] using h
      have hconstdiv :
          ∃ a : A, (minpoly A x).coeff 0 = πA ^ 2 * a := by
        exact Ideal.mem_span_singleton.mp hconst
      obtain ⟨a, ha⟩ := hconstdiv
      have hconst_ge2 :
          (2 * Module.finrank K L : ℕ∞) ≤
            IsDiscreteValuationRing.addVal B
              (algebraMap A B ((minpoly A x).coeff 0)) := by
        calc
          (2 * Module.finrank K L : ℕ∞) =
              (Module.finrank K L : ℕ∞) + (Module.finrank K L : ℕ∞) := by
                simp [two_mul]
          _ ≤ IsDiscreteValuationRing.addVal B (algebraMap A B πA) +
                IsDiscreteValuationRing.addVal B (algebraMap A B πA) :=
            add_le_add hπval hπval
          _ = IsDiscreteValuationRing.addVal B
                (algebraMap A B πA * algebraMap A B πA) := by
            rw [IsDiscreteValuationRing.addVal_mul]
          _ = IsDiscreteValuationRing.addVal B
                (algebraMap A B (πA ^ 2)) := by
            simp [pow_two]
          _ ≤ IsDiscreteValuationRing.addVal B
                (algebraMap A B (πA ^ 2)) +
                IsDiscreteValuationRing.addVal B (algebraMap A B a) :=
            le_add_of_nonneg_right zero_le
          _ = IsDiscreteValuationRing.addVal B
                (algebraMap A B ((minpoly A x).coeff 0)) := by
            rw [ha, map_mul, IsDiscreteValuationRing.addVal_mul]
      have hlead :
          (minpoly A x).coeff (minpoly A x).natDegree = 1 :=
        (minpoly.monic (Algebra.IsIntegral.isIntegral x)).coeff_natDegree
      have hleadunit :
          IsUnit ((minpoly A x).coeff (minpoly A x).natDegree) := by
        rw [hlead]
        exact isUnit_one
      have hterm_lead_ne :
          terms (minpoly A x).natDegree ≠ 0 := by
        dsimp [terms]
        exact mul_ne_zero (hleadunit.map (algebraMap A B)).ne_zero
          (pow_ne_zero _ hx0)
      have hterm_lead_value :
          IsDiscreteValuationRing.addVal B (terms (minpoly A x).natDegree) =
            ((minpoly A x).natDegree : ℕ∞) :=
        hterm_unit_value _ hleadunit
      have hterm_zero_ge :
          (2 * Module.finrank K L : ℕ∞) ≤
            IsDiscreteValuationRing.addVal B (terms 0) := by
        calc
          (2 * Module.finrank K L : ℕ∞) ≤
              IsDiscreteValuationRing.addVal B
                (algebraMap A B ((minpoly A x).coeff 0)) := hconst_ge2
          _ = IsDiscreteValuationRing.addVal B
                (algebraMap A B ((minpoly A x).coeff 0)) + (0 : ℕ∞) := by
            simp
          _ = IsDiscreteValuationRing.addVal B (terms 0) :=
            (hterm_value 0).symm
      have hleast_lead :
          ∀ j : ℕ, j ∈ Finset.range ((minpoly A x).natDegree + 1) →
            j ≠ (minpoly A x).natDegree →
              IsDiscreteValuationRing.addVal B
                  (terms (minpoly A x).natDegree) <
                IsDiscreteValuationRing.addVal B (terms j) := by
        intro j hj hjne
        have hjle : j ≤ (minpoly A x).natDegree :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjlower : j < (minpoly A x).natDegree :=
          lt_of_le_of_ne hjle hjne
        by_cases hjzero : j = 0
        · subst j
          have hn_lt_2n :
              ((minpoly A x).natDegree : ℕ∞) <
                (2 * Module.finrank K L : ℕ∞) := by
            have hnat : (minpoly A x).natDegree <
                2 * Module.finrank K L := by
              rw [hmapdeg, hdegK]
              omega
            exact_mod_cast hnat
          rw [hterm_lead_value]
          exact hn_lt_2n.trans_le hterm_zero_ge
        · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
          have hcoef := hcoeff_mem j hjlower
          have hcoef_ge := hcoeff_ge j hjlower hcoef
          have hterm_ge :
              (Module.finrank K L : ℕ∞) + (j : ℕ∞) ≤
                IsDiscreteValuationRing.addVal B (terms j) := by
            calc
              (Module.finrank K L : ℕ∞) + (j : ℕ∞) ≤
                  IsDiscreteValuationRing.addVal B
                    (algebraMap A B ((minpoly A x).coeff j)) + (j : ℕ∞) :=
                by
                  simpa [add_comm] using
                    add_le_add_left hcoef_ge (j : ℕ∞)
              _ = IsDiscreteValuationRing.addVal B (terms j) :=
                (hterm_value j).symm
          have hnj :
              ((minpoly A x).natDegree : ℕ∞) <
                (Module.finrank K L : ℕ∞) + (j : ℕ∞) := by
            have hnat : (minpoly A x).natDegree <
                Module.finrank K L + j := by
              rw [hmapdeg, hdegK]
              omega
            exact_mod_cast hnat
          rw [hterm_lead_value]
          exact hnj.trans_le hterm_ge
      have hlt_lead :
            IsDiscreteValuationRing.addVal B
              (terms (minpoly A x).natDegree) <
            IsDiscreteValuationRing.addVal B
              (∑ j ∈ (Finset.range ((minpoly A x).natDegree + 1)) \ {
                (minpoly A x).natDegree}, terms j) := by
        apply (IsDiscreteValuationRing.addVal B).map_lt_sum
        · intro htop
          exact hterm_lead_ne
            (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
        · intro j hj
          exact hleast_lead j (Finset.mem_sdiff.mp hj).1 (by
            intro h
            exact (Finset.mem_sdiff.mp hj).2 (by simp [h]))
      have hdecomp_lead :=
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem
          (s := Finset.range ((minpoly A x).natDegree + 1))
          (i := (minpoly A x).natDegree)
          (Finset.mem_range.mpr (Nat.lt_succ_self _)) terms
      have hzero_lead :
          terms (minpoly A x).natDegree +
              (∑ j ∈ (Finset.range ((minpoly A x).natDegree + 1)) \ {
                (minpoly A x).natDegree}, terms j) = 0 := by
        rw [← hdecomp_lead]
        exact hroot
      have hcancel_lead :=
        AddValuation.map_add_eq_of_lt_left (IsDiscreteValuationRing.addVal B)
          hlt_lead
      rw [hzero_lead, AddValuation.map_zero] at hcancel_lead
      have hne_lead :
          IsDiscreteValuationRing.addVal B
              (terms (minpoly A x).natDegree) ≠ (⊤ : ℕ∞) := by
        intro htop
        exact hterm_lead_ne
          (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
      exact hne_lead hcancel_lead.symm

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
