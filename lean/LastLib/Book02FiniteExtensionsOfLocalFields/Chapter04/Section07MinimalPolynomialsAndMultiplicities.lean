import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section06TracePairingsAndSeparability

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
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
