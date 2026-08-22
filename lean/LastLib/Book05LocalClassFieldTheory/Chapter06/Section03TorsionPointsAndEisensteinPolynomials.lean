import LastLib.Book05LocalClassFieldTheory.Chapter06.Section02FormalModule

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators Polynomial

/-!
### 6.3. Torsion points and Eisenstein polynomials
-/

/-- The explicit Lubin--Tate polynomial over the valuation ring. -/
def chapter06LubinTatePolynomial
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    Polynomial (Chapter06ValuationRing D) :=
  Polynomial.C D.uniformizer * Polynomial.X +
    Polynomial.X ^ chapter06ResidueCardinality D

/-- The iterated multiplication-by-`π` polynomial `Sₙ`. -/
def chapter06TorsionPolynomialSequence
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) : ℕ →
    Polynomial (Chapter06ValuationRing D)
  | 0 => Polynomial.X
  | n + 1 =>
      (chapter06LubinTatePolynomial D).comp
        (chapter06TorsionPolynomialSequence D n)

abbrev chapter06Sn
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :=
  chapter06TorsionPolynomialSequence D n

theorem chapter06_explicit_torsion_sequence_is_scalar_power
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ)
    (M : Chapter06FormalModuleData D
      (chapter06ExplicitLubinTateSeries D)) :
      M.scalar ((D.uniformizer : Chapter06ValuationRing D) ^ n) =
      (chapter06Sn D n : PowerSeries (Chapter06ValuationRing D)) := by
  have hzero : ∀ m,
      PowerSeries.constantCoeff
          (chapter06Sn D m : PowerSeries (Chapter06ValuationRing D)) = 0 := by
    intro m
    induction m with
    | zero =>
        simp [chapter06Sn, chapter06TorsionPolynomialSequence]
    | succ m hm =>
        change Polynomial.coeff
          (chapter06TorsionPolynomialSequence D (m + 1)) 0 = 0
        rw [chapter06TorsionPolynomialSequence,
          Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
        have hm' : Polynomial.eval 0 (chapter06TorsionPolynomialSequence D m) = 0 := by
          rw [← Polynomial.coeff_zero_eq_eval_zero]
          simpa only [Polynomial.constantCoeff_coe] using hm
        have hq0 : chapter06ResidueCardinality D ≠ 0 :=
          Nat.ne_of_gt (chapter06_residue_cardinality_pos D)
        simp [chapter06LubinTatePolynomial, hm', hq0]
  induction n with
  | zero =>
      rw [pow_zero, M.scalar_one]
      simp [chapter06Sn, chapter06TorsionPolynomialSequence]
  | succ n ih =>
      rw [pow_succ', ← M.scalar_mul]
      rw [ih, M.scalar_pi]
      have hsub : PowerSeries.HasSubst
          (chapter06Sn D n : PowerSeries (Chapter06ValuationRing D)) :=
        PowerSeries.HasSubst.of_constantCoeff_zero' (hzero n)
      have hexplicit : chapter06ExplicitLubinTateSeries D =
          (chapter06LubinTatePolynomial D : PowerSeries (Chapter06ValuationRing D)) := by
        simp [chapter06ExplicitLubinTateSeries, chapter06LubinTatePolynomial]
      rw [hexplicit]
      change PowerSeries.subst
        (chapter06Sn D n : PowerSeries (Chapter06ValuationRing D))
        (chapter06LubinTatePolynomial D : PowerSeries (Chapter06ValuationRing D)) =
        (chapter06Sn D (n + 1) : PowerSeries (Chapter06ValuationRing D))
      rw [PowerSeries.subst_coe hsub]
      have hcompat :
          Polynomial.aeval
              (chapter06Sn D n : PowerSeries (Chapter06ValuationRing D))
              (chapter06LubinTatePolynomial D) =
            (chapter06Sn D (n + 1) : PowerSeries (Chapter06ValuationRing D)) := by
        simp [chapter06Sn, chapter06TorsionPolynomialSequence,
          chapter06LubinTatePolynomial, Polynomial.aeval_def,
          Polynomial.add_comp, Polynomial.X_comp]
      exact hcompat

/-- The polynomial `Qₙ` whose roots are the primitive `πⁿ`-torsion points;
the source's indexing is `Qₙ = Qₙ₋₁` in this zero-based definition. -/
def chapter06PrimitiveDivisionPolynomial
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Polynomial (Chapter06ValuationRing D) :=
  Polynomial.C D.uniformizer +
    (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1)

def chapter06Qn
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Polynomial (Chapter06ValuationRing D) :=
  chapter06PrimitiveDivisionPolynomial D (n - 1)

theorem chapter06_Qn_explicit
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (_hn : 0 < n) :
    chapter06Qn D n =
      Polynomial.C D.uniformizer +
        (chapter06Sn D (n - 1)) ^ (chapter06ResidueCardinality D - 1) := by
  rfl

theorem chapter06_Qn_factorization
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    chapter06Sn D n = chapter06Sn D (n - 1) * chapter06Qn D n := by
  have hfactor :
      chapter06Sn D ((n - 1) + 1) =
        chapter06Sn D (n - 1) * chapter06PrimitiveDivisionPolynomial D (n - 1) := by
    change (chapter06LubinTatePolynomial D).comp (chapter06Sn D (n - 1)) =
      chapter06Sn D (n - 1) *
        (Polynomial.C D.uniformizer +
          (chapter06Sn D (n - 1)) ^ (chapter06ResidueCardinality D - 1))
    rw [chapter06LubinTatePolynomial, Polynomial.add_comp,
      Polynomial.C_mul_comp, Polynomial.X_comp, Polynomial.X_pow_comp]
    have hq : 0 < chapter06ResidueCardinality D :=
      chapter06_residue_cardinality_pos D
    have hpow :
        (chapter06Sn D (n - 1)) ^ chapter06ResidueCardinality D =
          chapter06Sn D (n - 1) *
            (chapter06Sn D (n - 1)) ^ (chapter06ResidueCardinality D - 1) := by
      calc
        (chapter06Sn D (n - 1)) ^ chapter06ResidueCardinality D =
            (chapter06Sn D (n - 1)) ^
              ((chapter06ResidueCardinality D - 1) + 1) := by
          rw [Nat.sub_add_cancel hq]
        _ = chapter06Sn D (n - 1) *
              (chapter06Sn D (n - 1)) ^ (chapter06ResidueCardinality D - 1) := by
          rw [pow_succ']
    rw [hpow]
    ring
  simpa [chapter06Qn, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hfactor

theorem chapter06_torsion_polynomial_succ_factorization
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    chapter06Sn D (n + 1) =
      chapter06Sn D n * chapter06PrimitiveDivisionPolynomial D n := by
  change (chapter06LubinTatePolynomial D).comp (chapter06Sn D n) =
    chapter06Sn D n *
      (Polynomial.C D.uniformizer +
        (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1))
  rw [chapter06LubinTatePolynomial, Polynomial.add_comp,
    Polynomial.C_mul_comp, Polynomial.X_comp, Polynomial.X_pow_comp]
  have hq : 0 < chapter06ResidueCardinality D :=
    chapter06_residue_cardinality_pos D
  have hpow :
      (chapter06Sn D n) ^ chapter06ResidueCardinality D =
        chapter06Sn D n *
          (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1) := by
    calc
      (chapter06Sn D n) ^ chapter06ResidueCardinality D =
          (chapter06Sn D n) ^
            ((chapter06ResidueCardinality D - 1) + 1) := by
        rw [Nat.sub_add_cancel hq]
      _ = chapter06Sn D n *
            (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1) := by
        rw [pow_succ']
  rw [hpow]
  ring

theorem chapter06_torsion_polynomial_mod_uniformizer
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06Sn D n).map
        (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) =
      Polynomial.X ^ chapter06ResidueCardinality D ^ n := by
  have hπmem : (D.uniformizer : Chapter06ValuationRing D) ∈
      IsLocalRing.maximalIdeal (Chapter06ValuationRing D) := by
    change (D.uniformizer : Chapter06ValuationRing D) ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01MaximalIdeal
        D.valuation.toValuation
    rw [D.uniformizer_spec.2]
    exact Ideal.mem_span_singleton_self _
  have hπmap :
      (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D))
          D.uniformizer = 0 := by
    rw [IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact hπmem
  have hq : 0 < chapter06ResidueCardinality D :=
    chapter06_residue_cardinality_pos D
  have hq0 : chapter06ResidueCardinality D ≠ 0 := Nat.ne_of_gt hq
  induction n with
  | zero =>
      simp [chapter06Sn, chapter06TorsionPolynomialSequence]
  | succ n ih =>
      change ((chapter06LubinTatePolynomial D).comp (chapter06Sn D n)).map
          (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) = _
      rw [Polynomial.map_comp]
      have hmap :
          (chapter06LubinTatePolynomial D).map
              (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) =
            Polynomial.X ^ chapter06ResidueCardinality D := by
        rw [chapter06LubinTatePolynomial, Polynomial.map_add,
          Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
          Polynomial.map_pow, hπmap]
        simp
      rw [hmap, Polynomial.X_pow_comp, ih]
      rw [← pow_mul]
      rw [pow_succ']
      congr 1
      exact Nat.mul_comm _ _

theorem chapter06_torsion_polynomial_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06Sn D n).natDegree = chapter06ResidueCardinality D ^ n := by
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  have hq1 : 1 < chapter06ResidueCardinality D := by
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hπ0 : (D.uniformizer : Chapter06ValuationRing D) ≠ 0 := by
    exact D.uniformizer_spec.1
  have hleft :
      ((Polynomial.C D.uniformizer :
          Polynomial (Chapter06ValuationRing D)) *
          (Polynomial.X : Polynomial (Chapter06ValuationRing D))).natDegree <
        ((Polynomial.X : Polynomial (Chapter06ValuationRing D)) ^
          chapter06ResidueCardinality D).natDegree := by
    rw [Polynomial.natDegree_C_mul hπ0, Polynomial.natDegree_X_pow]
    simp [hq1]
  have hLT :
      (chapter06LubinTatePolynomial D).natDegree =
        chapter06ResidueCardinality D := by
    rw [chapter06LubinTatePolynomial,
      Polynomial.natDegree_add_eq_right_of_natDegree_lt hleft,
      Polynomial.natDegree_X_pow]
  induction n with
  | zero =>
      simp [chapter06Sn, chapter06TorsionPolynomialSequence]
  | succ n ih =>
      change ((chapter06LubinTatePolynomial D).comp
          (chapter06Sn D n)).natDegree = _
      rw [Polynomial.natDegree_comp, hLT, ih, pow_succ']

theorem chapter06_torsion_polynomial_monic
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06Sn D n).Monic := by
  have hq1 : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hπ0 : (D.uniformizer : Chapter06ValuationRing D) ≠ 0 := by
    exact D.uniformizer_spec.1
  have hdeg :
      ((Polynomial.C D.uniformizer : Polynomial (Chapter06ValuationRing D)) *
          (Polynomial.X : Polynomial (Chapter06ValuationRing D))).degree <
        (chapter06ResidueCardinality D : WithBot ℕ) := by
    rw [Polynomial.degree_C_mul_X hπ0]
    exact WithBot.coe_lt_coe.mpr hq1
  have hfmonic : (chapter06LubinTatePolynomial D).Monic := by
    rw [chapter06LubinTatePolynomial, add_comm]
    exact Polynomial.monic_X_pow_add hdeg
  induction n with
  | zero =>
      simp [chapter06Sn, chapter06TorsionPolynomialSequence]
  | succ n ih =>
      change (chapter06LubinTatePolynomial D).comp (chapter06Sn D n) |>.Monic
      apply hfmonic.comp ih
      rw [chapter06_torsion_polynomial_degree D n]
      exact pow_ne_zero _ (by omega)

theorem chapter06_primitive_division_polynomial_monic
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).Monic := by
  have hSn : (chapter06Sn D n).Monic :=
    chapter06_torsion_polynomial_monic D n
  have hq1 : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hSnDegree : (chapter06Sn D n).natDegree =
      chapter06ResidueCardinality D ^ n :=
    chapter06_torsion_polynomial_degree D n
  change (Polynomial.C D.uniformizer +
    (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1)).Monic
  apply (hSn.pow (chapter06ResidueCardinality D - 1)).add_of_right
  apply (Polynomial.degree_C_le (a := D.uniformizer)).trans_lt
  rw [Polynomial.degree_eq_natDegree ((hSn.pow _).ne_zero), hSn.natDegree_pow,
    hSnDegree]
  apply WithBot.coe_lt_coe.mpr
  exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

theorem chapter06_primitive_division_polynomial_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).natDegree =
      chapter06ResidueCardinality D ^ n *
        (chapter06ResidueCardinality D - 1) := by
  have hSn : (chapter06Sn D n).Monic :=
    chapter06_torsion_polynomial_monic D n
  have hq1 : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hSnDegree : (chapter06Sn D n).natDegree =
      chapter06ResidueCardinality D ^ n :=
    chapter06_torsion_polynomial_degree D n
  have hlt : (Polynomial.C D.uniformizer).natDegree <
      ((chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1)).natDegree := by
    rw [Polynomial.natDegree_C, hSn.natDegree_pow, hSnDegree]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  change (Polynomial.C D.uniformizer +
    (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1)).natDegree = _
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt,
    hSn.natDegree_pow, hSnDegree]
  exact Nat.mul_comm _ _

theorem chapter06_primitive_division_polynomial_constant
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).eval 0 = D.uniformizer := by
  have hzero : ∀ m,
      (chapter06Sn D m).eval 0 = 0 := by
    intro m
    induction m with
    | zero =>
        simp [chapter06Sn, chapter06TorsionPolynomialSequence]
    | succ m hm =>
        change ((chapter06LubinTatePolynomial D).comp
          (chapter06Sn D m)).eval 0 = 0
        rw [Polynomial.eval_comp]
        have hq0 : chapter06ResidueCardinality D ≠ 0 :=
          Nat.ne_of_gt (chapter06_residue_cardinality_pos D)
        simp [chapter06LubinTatePolynomial, hm, hq0]
  have hq1 : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hqminus : chapter06ResidueCardinality D - 1 ≠ 0 := by
    omega
  simp [chapter06PrimitiveDivisionPolynomial, Polynomial.eval_add,
    Polynomial.eval_pow, hzero n, hqminus]

theorem chapter06_primitive_division_polynomial_mod_uniformizer
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).map
        (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) =
      Polynomial.X ^
        (chapter06ResidueCardinality D ^ n *
          (chapter06ResidueCardinality D - 1)) := by
  have hπmem : (D.uniformizer : Chapter06ValuationRing D) ∈
      IsLocalRing.maximalIdeal (Chapter06ValuationRing D) := by
    change (D.uniformizer : Chapter06ValuationRing D) ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01MaximalIdeal
        D.valuation.toValuation
    rw [D.uniformizer_spec.2]
    exact Ideal.mem_span_singleton_self _
  have hπmap :
      (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D))
          D.uniformizer = 0 := by
    rw [IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact hπmem
  change (Polynomial.C D.uniformizer +
    (chapter06Sn D n) ^ (chapter06ResidueCardinality D - 1)).map
      (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) = _
  rw [Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow, hπmap,
    chapter06_torsion_polynomial_mod_uniformizer D n]
  simp only [map_zero, zero_add]
  rw [← pow_mul]

theorem chapter06_primitive_division_polynomial_is_eisenstein
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).IsEisensteinAt
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) := by
  let A := Chapter06ValuationRing D
  let B := Chapter06ResidueField D
  let φ : A →+* B := algebraMap A B
  have hdegree := chapter06_primitive_division_polynomial_degree D n
  have hspan : Ideal.span ({(D.uniformizer : A)} : Set A) =
      IsLocalRing.maximalIdeal A := by
    change Ideal.span ({(D.uniformizer : A)} : Set A) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01MaximalIdeal
        D.valuation.toValuation
    exact D.uniformizer_spec.2.symm
  have hπ0 : (D.uniformizer : A) ≠ 0 := D.uniformizer_spec.1
  have hirr : Irreducible (D.uniformizer : A) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      D.uniformizer hπ0 hspan.symm
  have hcoeff_mem : ∀ i < (chapter06PrimitiveDivisionPolynomial D n).natDegree,
      (chapter06PrimitiveDivisionPolynomial D n).coeff i ∈
        IsLocalRing.maximalIdeal A := by
    intro i hi
    have hi' : i < chapter06ResidueCardinality D ^ n *
        (chapter06ResidueCardinality D - 1) := by
      simpa [hdegree] using hi
    have hcoeff := congrArg (fun p : Polynomial B => p.coeff i)
      (chapter06_primitive_division_polynomial_mod_uniformizer D n)
    have hzero : φ ((chapter06PrimitiveDivisionPolynomial D n).coeff i) = 0 := by
      rw [Polynomial.coeff_map] at hcoeff
      rw [Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi')] at hcoeff
      exact hcoeff
    have hmemmax : (chapter06PrimitiveDivisionPolynomial D n).coeff i ∈
        IsLocalRing.maximalIdeal A := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [← IsLocalRing.ResidueField.algebraMap_eq]
      exact hzero
    exact hmemmax
  have hconst :
      (chapter06PrimitiveDivisionPolynomial D n).constantCoeff = D.uniformizer := by
    simpa [Polynomial.constantCoeff, Polynomial.coeff_zero_eq_eval_zero] using
      chapter06_primitive_division_polynomial_constant D n
  have hconstant_not_mem :
      (chapter06PrimitiveDivisionPolynomial D n).constantCoeff ∉
        (IsLocalRing.maximalIdeal A) ^ 2 := by
    rw [hconst, ← hspan, Ideal.span_singleton_pow]
    intro hmem
    have hdiv : (D.uniformizer : A) ^ 2 ∣ D.uniformizer :=
      Ideal.mem_span_singleton.mp hmem
    rcases hdiv with ⟨c, hc⟩
    have hcancel : (1 : A) = D.uniformizer * c := by
      apply (mul_left_cancel₀ hπ0)
      simpa [pow_two, mul_assoc] using hc
    have hunit : IsUnit (D.uniformizer : A) := by
      apply isUnit_of_dvd_one
      refine ⟨c, hcancel⟩
    exact hirr.not_isUnit hunit
  have hleading :
      (chapter06PrimitiveDivisionPolynomial D n).leadingCoeff ∉
        IsLocalRing.maximalIdeal A :=
    (chapter06_primitive_division_polynomial_monic D n).leadingCoeff_notMem
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  refine ⟨hleading, ?_, hconstant_not_mem⟩
  intro i hi
  simpa [A] using hcoeff_mem i hi

theorem chapter06_Qn_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).natDegree =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
  have _hn : 0 < n := hn
  exact chapter06_primitive_division_polynomial_degree D (n - 1)

theorem chapter06_Qn_monic
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).Monic := by
  have _hn : 0 < n := hn
  exact chapter06_primitive_division_polynomial_monic D (n - 1)

theorem chapter06_Qn_constant
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).eval 0 = D.uniformizer := by
  have _hn : 0 < n := hn
  exact chapter06_primitive_division_polynomial_constant D (n - 1)

theorem chapter06_Qn_is_eisenstein
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).IsEisensteinAt
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) := by
  have _hn : 0 < n := hn
  exact chapter06_primitive_division_polynomial_is_eisenstein D (n - 1)

/-- The `πⁿ`-torsion set in the fixed algebraic closure. -/
def chapter06TorsionPolynomialOverK
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Polynomial K :=
  (chapter06Sn D n).map (algebraMap (Chapter06ValuationRing D) K)

def chapter06TorsionSet
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Set (AlgebraicClosure K) :=
  {x | Polynomial.aeval x (chapter06TorsionPolynomialOverK D n) = 0}

def chapter06PrimitiveTorsionPolynomialOverK
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Polynomial K :=
  (chapter06Qn D n).map (algebraMap (Chapter06ValuationRing D) K)

def chapter06PrimitiveTorsionSet
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Set (AlgebraicClosure K) :=
  {x | Polynomial.aeval x (chapter06PrimitiveTorsionPolynomialOverK D n) = 0}

/-- A primitive point is a root at level `n` which is not a root at level
`n-1`; this is the source definition and avoids a hidden choice of generator. -/
structure Chapter06PrimitiveTorsionPoint
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) where
  point : AlgebraicClosure K
  torsion : point ∈ chapter06TorsionSet D n
  primitive : point ∉ chapter06TorsionSet D (n - 1)

theorem chapter06_primitive_torsion_point_exists
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (Chapter06PrimitiveTorsionPoint D n hn) := by
  have hq1 : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hdegree :
      0 < (chapter06PrimitiveTorsionPolynomialOverK D n).natDegree := by
    have hmapdegree :
        (chapter06PrimitiveTorsionPolynomialOverK D n).natDegree =
          (chapter06Qn D n).natDegree := by
      unfold chapter06PrimitiveTorsionPolynomialOverK
      apply Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff
      rw [(chapter06_Qn_monic D n hn).leadingCoeff]
      exact isUnit_one
    rw [hmapdegree, chapter06_Qn_degree D n hn]
    exact Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have hdegree' :
      (chapter06PrimitiveTorsionPolynomialOverK D n).degree ≠ 0 :=
    ne_of_gt ((Polynomial.natDegree_pos_iff_degree_pos).mp hdegree)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero
    (AlgebraicClosure K) (chapter06PrimitiveTorsionPolynomialOverK D n) hdegree'
  have hfactor :
      chapter06TorsionPolynomialOverK D n =
        chapter06TorsionPolynomialOverK D (n - 1) *
          chapter06PrimitiveTorsionPolynomialOverK D n := by
    unfold chapter06TorsionPolynomialOverK chapter06PrimitiveTorsionPolynomialOverK
    rw [chapter06_Qn_factorization D n hn, Polynomial.map_mul]
  have hformula :
      chapter06PrimitiveTorsionPolynomialOverK D n =
        Polynomial.C (algebraMap (Chapter06ValuationRing D) K D.uniformizer) +
          (chapter06TorsionPolynomialOverK D (n - 1)) ^
            (chapter06ResidueCardinality D - 1) := by
    simp [chapter06PrimitiveTorsionPolynomialOverK, chapter06Qn,
      chapter06PrimitiveDivisionPolynomial, chapter06TorsionPolynomialOverK]
  have hpi :
      algebraMap K (AlgebraicClosure K)
          (algebraMap (Chapter06ValuationRing D) K D.uniformizer) ≠ 0 := by
    intro hzero
    apply chapter06_uniformizer_ne_zero D
    apply (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K))
    simpa using hzero
  have hqminus : chapter06ResidueCardinality D - 1 ≠ 0 := by
    omega
  refine ⟨⟨x, ?_, ?_⟩⟩
  · change Polynomial.aeval x (chapter06TorsionPolynomialOverK D n) = 0
    rw [hfactor]
    simp only [map_mul, hx, mul_zero]
  · change Polynomial.aeval x
        (chapter06TorsionPolynomialOverK D (n - 1)) ≠ 0
    intro hprev
    have hprev' :
        Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
            (chapter06TorsionPolynomialOverK D (n - 1)) = 0 := by
      simpa [Polynomial.aeval_def] using hprev
    have hconst :
        Polynomial.aeval x (chapter06PrimitiveTorsionPolynomialOverK D n) =
            algebraMap K (AlgebraicClosure K)
            (algebraMap (Chapter06ValuationRing D) K D.uniformizer) := by
      rw [hformula]
      simp [Polynomial.aeval_def, hprev', hqminus]
    rw [hx] at hconst
    exact hpi hconst.symm

theorem chapter06_primitive_torsion_point_is_a_root
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    Polynomial.aeval ω.point (chapter06TorsionPolynomialOverK D n) = 0 := by
  exact ω.torsion

theorem chapter06_primitive_torsion_point_is_not_previous_root
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    Polynomial.aeval ω.point
        (chapter06TorsionPolynomialOverK D (n - 1)) ≠ 0 := by
  intro h
  exact ω.primitive h

/-- A primitive point viewed as a point of the full torsion set. -/
def chapter06PrimitivePointAsTorsion
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
  ⟨ω.point, ω.torsion⟩

theorem chapter06_mem_primitiveTorsionSet_iff
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) (x : AlgebraicClosure K) :
    x ∈ chapter06PrimitiveTorsionSet D n ↔
      x ∈ chapter06TorsionSet D n ∧
        x ∉ chapter06TorsionSet D (n - 1) := by
  change Polynomial.aeval x (chapter06PrimitiveTorsionPolynomialOverK D n) = 0 ↔
    Polynomial.aeval x (chapter06TorsionPolynomialOverK D n) = 0 ∧
      Polynomial.aeval x (chapter06TorsionPolynomialOverK D (n - 1)) ≠ 0
  have hq1 : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hqminus : chapter06ResidueCardinality D - 1 ≠ 0 := by
    omega
  have hfactor :
      chapter06TorsionPolynomialOverK D n =
        chapter06TorsionPolynomialOverK D (n - 1) *
          chapter06PrimitiveTorsionPolynomialOverK D n := by
    unfold chapter06TorsionPolynomialOverK chapter06PrimitiveTorsionPolynomialOverK
    rw [chapter06_Qn_factorization D n hn, Polynomial.map_mul]
  have hformula :
      chapter06PrimitiveTorsionPolynomialOverK D n =
        Polynomial.C (algebraMap (Chapter06ValuationRing D) K D.uniformizer) +
          (chapter06TorsionPolynomialOverK D (n - 1)) ^
            (chapter06ResidueCardinality D - 1) := by
    simp [chapter06PrimitiveTorsionPolynomialOverK, chapter06Qn,
      chapter06PrimitiveDivisionPolynomial, chapter06TorsionPolynomialOverK]
  have hpi :
      algebraMap K (AlgebraicClosure K)
          (algebraMap (Chapter06ValuationRing D) K D.uniformizer) ≠ 0 := by
    intro hzero
    apply chapter06_uniformizer_ne_zero D
    apply (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K))
    simpa using hzero
  constructor
  · intro hprimitive
    constructor
    · rw [hfactor]
      simp only [map_mul, hprimitive, mul_zero]
    · intro hprev
      have hprev' :
          Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06TorsionPolynomialOverK D (n - 1)) = 0 := by
        simpa [Polynomial.aeval_def] using hprev
      have hconst :
          Polynomial.aeval x (chapter06PrimitiveTorsionPolynomialOverK D n) =
              algebraMap K (AlgebraicClosure K)
              (algebraMap (Chapter06ValuationRing D) K D.uniformizer) := by
        rw [hformula]
        simp [Polynomial.aeval_def, hprev', hqminus]
      rw [hprimitive] at hconst
      exact hpi hconst.symm
  · rintro ⟨htorsion, hprev⟩
    rw [hfactor] at htorsion
    have hprod :
        Polynomial.aeval x (chapter06TorsionPolynomialOverK D (n - 1)) *
          Polynomial.aeval x (chapter06PrimitiveTorsionPolynomialOverK D n) = 0 := by
      simpa only [map_mul] using htorsion
    exact (mul_eq_zero.mp hprod).resolve_left hprev

theorem chapter06_primitive_torsion_point_is_primitive_division_root
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    ω.point ∈ chapter06PrimitiveTorsionSet D n := by
  exact (chapter06_mem_primitiveTorsionSet_iff D n hn ω.point).2
    ⟨ω.torsion, ω.primitive⟩

theorem chapter06_torsion_polynomial_derivative_at_zero
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06TorsionPolynomialOverK D n).derivative.eval 0 =
      (algebraMap (Chapter06ValuationRing D) K) D.uniformizer ^ n := by
  have hq : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hq0 : chapter06ResidueCardinality D ≠ 0 := by omega
  have hqminus : chapter06ResidueCardinality D - 1 ≠ 0 := by omega
  have hzero : ∀ m, (chapter06Sn D m).eval 0 = 0 := by
    intro m
    induction m with
    | zero =>
        simp [chapter06Sn, chapter06TorsionPolynomialSequence]
    | succ m hm =>
        change ((chapter06LubinTatePolynomial D).comp
          (chapter06Sn D m)).eval 0 = 0
        rw [Polynomial.eval_comp]
        simp [chapter06LubinTatePolynomial, hm, hq0]
  have hzeroK : ∀ m, (chapter06TorsionPolynomialOverK D m).eval 0 = 0 := by
    intro m
    induction m with
    | zero =>
        simp [chapter06TorsionPolynomialOverK, chapter06Sn,
          chapter06TorsionPolynomialSequence]
    | succ m hm =>
        change Polynomial.eval 0
          (((chapter06LubinTatePolynomial D).comp
            (chapter06Sn D m)).map
              (algebraMap (Chapter06ValuationRing D) K)) = 0
        rw [Polynomial.map_comp, Polynomial.eval_comp]
        have hm' :
            Polynomial.eval 0
                ((chapter06Sn D m).map
                  (algebraMap (Chapter06ValuationRing D) K)) = 0 := by
          exact hm
        rw [hm']
        simp [chapter06LubinTatePolynomial, hq0]
  induction n with
  | zero =>
      simp [chapter06TorsionPolynomialOverK, chapter06Sn,
        chapter06TorsionPolynomialSequence]
  | succ n ih =>
      have hcomp :
          chapter06TorsionPolynomialOverK D (n + 1) =
            ((chapter06LubinTatePolynomial D).map
                (algebraMap (Chapter06ValuationRing D) K)).comp
              (chapter06TorsionPolynomialOverK D n) := by
        simp [chapter06TorsionPolynomialOverK, chapter06Sn,
          chapter06TorsionPolynomialSequence, Polynomial.map_comp]
      rw [hcomp, Polynomial.derivative_comp]
      rw [Polynomial.eval_mul, Polynomial.eval_comp]
      rw [ih]
      have hmap :
          (chapter06LubinTatePolynomial D).map
              (algebraMap (Chapter06ValuationRing D) K) =
            Polynomial.C ((algebraMap (Chapter06ValuationRing D) K) D.uniformizer) *
                Polynomial.X +
              Polynomial.X ^ chapter06ResidueCardinality D := by
        rw [chapter06LubinTatePolynomial, Polynomial.map_add,
          Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X]
      rw [hmap]
      simp [Polynomial.derivative_add, Polynomial.derivative_X,
        Polynomial.derivative_X_pow, hzeroK n, hqminus, pow_succ']
      ring

theorem chapter06_torsion_polynomial_roots_simple
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ)
    (x : AlgebraicClosure K)
    (hx : x ∈ chapter06TorsionSet D n) :
    Polynomial.aeval x (chapter06TorsionPolynomialOverK D n).derivative ≠ 0 := by
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  have hq : 1 < chapter06ResidueCardinality D := by
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hqminusK :
      ((chapter06ResidueCardinality D - 1 : ℕ) : K) ≠ 0 := by
    intro hzero
    have hzeroA :
        ((chapter06ResidueCardinality D - 1 : ℕ) : Chapter06ValuationRing D) = 0 := by
      apply Subtype.ext
      exact hzero
    have hzeroB :
        ((chapter06ResidueCardinality D - 1 : ℕ) : Chapter06ResidueField D) = 0 := by
      have hmap := congrArg
        (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) hzeroA
      simpa using hmap
    have hqB : (chapter06ResidueCardinality D : Chapter06ResidueField D) = 0 := by
      rw [chapter06ResidueCardinality, Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero (Chapter06ResidueField D)
    rw [Nat.cast_sub (by omega : 1 ≤ chapter06ResidueCardinality D), hqB] at hzeroB
    simp at hzeroB
  have hSn_deriv_ne_zero : ∀ m,
      (chapter06TorsionPolynomialOverK D m).derivative ≠ 0 := by
    intro m hzero
    have hderiv := chapter06_torsion_polynomial_derivative_at_zero D m
    rw [hzero] at hderiv
    have hpi :
        (algebraMap (Chapter06ValuationRing D) K) D.uniformizer ≠ 0 := by
      intro h
      apply D.uniformizer_spec.1
      apply (FaithfulSMul.algebraMap_injective
        (Chapter06ValuationRing D) K)
      simpa using h
    have hderiv' : 0 =
        (algebraMap (Chapter06ValuationRing D) K) D.uniformizer ^ m := by
      simpa using hderiv
    exact (pow_ne_zero m hpi) hderiv'.symm
  have hQ_deriv_ne_zero : ∀ m,
      (chapter06PrimitiveTorsionPolynomialOverK D (m + 1)).derivative ≠ 0 := by
    intro m hzero
    have hformula :
        (chapter06PrimitiveTorsionPolynomialOverK D (m + 1)).derivative =
          Polynomial.C ((chapter06ResidueCardinality D - 1 : ℕ) : K) *
              (chapter06TorsionPolynomialOverK D m) ^
                (chapter06ResidueCardinality D - 2) *
          (chapter06TorsionPolynomialOverK D m).derivative := by
      have hq2 : chapter06ResidueCardinality D - 1 - 1 =
          chapter06ResidueCardinality D - 2 := by omega
      simp [chapter06PrimitiveTorsionPolynomialOverK, chapter06Qn,
        chapter06PrimitiveDivisionPolynomial, chapter06TorsionPolynomialOverK,
        Polynomial.derivative_map, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_pow, hq2]
    rw [hformula] at hzero
    have hSn : chapter06TorsionPolynomialOverK D m ≠ 0 := by
      intro h
      apply hSn_deriv_ne_zero m
      rw [h]
      simp
    have hleft :
        Polynomial.C ((chapter06ResidueCardinality D - 1 : ℕ) : K) *
            (chapter06TorsionPolynomialOverK D m) ^
              (chapter06ResidueCardinality D - 2) ≠ 0 := by
      apply mul_ne_zero
      · simpa only [Polynomial.C_ne_zero] using hqminusK
      · exact pow_ne_zero _ hSn
    apply hSn_deriv_ne_zero m
    exact (mul_eq_zero.mp hzero).resolve_left hleft
  have hQsep : ∀ m,
      (chapter06PrimitiveTorsionPolynomialOverK D (m + 1)).Separable := by
    intro m
    have hpos : 0 < (chapter06Qn D (m + 1)).natDegree := by
      rw [chapter06_Qn_degree D (m + 1) (by omega)]
      exact Nat.mul_pos (pow_pos (by omega) _) (by omega)
    have hmonic := chapter06_Qn_monic D (m + 1) (by omega)
    have hirrA : Irreducible (chapter06Qn D (m + 1)) := by
      apply (chapter06_Qn_is_eisenstein D (m + 1) (by omega)).irreducible
        (IsLocalRing.maximalIdeal.isMaximal _).isPrime
        hmonic.isPrimitive hpos
    have hirrK :
        Irreducible (chapter06PrimitiveTorsionPolynomialOverK D (m + 1)) := by
      exact (hmonic.irreducible_iff_irreducible_map_fraction_map).mp hirrA
    exact (Polynomial.separable_iff_derivative_ne_zero hirrK).2
      (hQ_deriv_ne_zero m)
  induction n generalizing x with
  | zero =>
      simp [chapter06TorsionPolynomialOverK, chapter06Sn,
        chapter06TorsionPolynomialSequence]
  | succ n ih =>
      have hfactor :
          chapter06TorsionPolynomialOverK D (n + 1) =
            chapter06TorsionPolynomialOverK D n *
              chapter06PrimitiveTorsionPolynomialOverK D (n + 1) := by
        unfold chapter06TorsionPolynomialOverK
          chapter06PrimitiveTorsionPolynomialOverK
        rw [chapter06_Qn_factorization D (n + 1) (by omega),
          Polynomial.map_mul]
        simp only [Nat.add_sub_cancel]
      have hx' :
          Polynomial.aeval x (chapter06TorsionPolynomialOverK D (n + 1)) = 0 := hx
      rw [hfactor] at hx'
      have hprod :
          Polynomial.aeval x (chapter06TorsionPolynomialOverK D n) *
              Polynomial.aeval x
                (chapter06PrimitiveTorsionPolynomialOverK D (n + 1)) = 0 := by
        simpa only [Polynomial.aeval_def, Polynomial.eval₂_mul] using hx'
      rcases mul_eq_zero.mp hprod with hprev | hprimitive
      · have hprev' : x ∈ chapter06TorsionSet D n := hprev
        have hprevderiv := ih x hprev'
        have hprimitive_ne :
            Polynomial.aeval x
                (chapter06PrimitiveTorsionPolynomialOverK D (n + 1)) ≠ 0 := by
          intro hprimitive_zero
          have hprimitive_mem :
              x ∈ chapter06PrimitiveTorsionSet D (n + 1) := hprimitive_zero
          -- The primitive-root characterization excludes the previous level.
          exact False.elim (((chapter06_mem_primitiveTorsionSet_iff D (n + 1) (by omega) x).mp
            hprimitive_mem).2 hprev')
        have hprev_eval :
            Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06TorsionPolynomialOverK D n) = 0 := by
          simpa [Polynomial.aeval_def] using hprev
        have hprevderiv_eval :
            Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06TorsionPolynomialOverK D n).derivative ≠ 0 := by
          simpa [Polynomial.aeval_def] using hprevderiv
        have hprimitive_eval :
            Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06PrimitiveTorsionPolynomialOverK D (n + 1)) ≠ 0 := by
          simpa [Polynomial.aeval_def] using hprimitive_ne
        rw [hfactor, Polynomial.derivative_mul]
        simp only [Polynomial.aeval_def, Polynomial.eval₂_add,
          Polynomial.eval₂_mul]
        rw [hprev_eval, zero_mul, add_zero]
        exact mul_ne_zero hprevderiv_eval hprimitive_eval
      · have hprimitive_mem :
            x ∈ chapter06PrimitiveTorsionSet D (n + 1) := hprimitive
        have hprev_ne :
            Polynomial.aeval x (chapter06TorsionPolynomialOverK D n) ≠ 0 := by
          intro hprev_zero
          have hprev_mem : x ∈ chapter06TorsionSet D n := hprev_zero
          exact ((chapter06_mem_primitiveTorsionSet_iff D (n + 1) (by omega) x).mp
            hprimitive_mem).2 hprev_mem
        have hprimitive_deriv :=
          (hQsep n).aeval_derivative_ne_zero hprimitive
        have hprimitive_eval :
            Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06PrimitiveTorsionPolynomialOverK D (n + 1)) = 0 := by
          simpa [Polynomial.aeval_def] using hprimitive
        have hprev_eval_ne :
            Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06TorsionPolynomialOverK D n) ≠ 0 := by
          simpa [Polynomial.aeval_def] using hprev_ne
        have hprimitive_deriv_eval :
            Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x
              (chapter06PrimitiveTorsionPolynomialOverK D (n + 1)).derivative ≠ 0 := by
          simpa [Polynomial.aeval_def] using hprimitive_deriv
        rw [hfactor, Polynomial.derivative_mul]
        simp only [Polynomial.aeval_def, Polynomial.eval₂_add,
          Polynomial.eval₂_mul]
        rw [hprimitive_eval, mul_zero, zero_add]
        exact mul_ne_zero hprev_eval_ne hprimitive_deriv_eval

theorem chapter06_torsion_set_finite
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Set.Finite (chapter06TorsionSet D n) := by
  have hmonic :
      (chapter06TorsionPolynomialOverK D n).Monic := by
    unfold chapter06TorsionPolynomialOverK
    exact (chapter06_torsion_polynomial_monic D n).map _
  apply (Polynomial.rootSet_finite
    (chapter06TorsionPolynomialOverK D n) (AlgebraicClosure K)).subset
  intro x hx
  exact (Polynomial.mem_rootSet).2 ⟨hmonic.ne_zero, hx⟩

theorem chapter06_torsion_set_cardinality
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Nat.card {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} =
      chapter06ResidueCardinality D ^ n := by
  classical
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  have hmonic :
      (chapter06TorsionPolynomialOverK D n).Monic := by
    unfold chapter06TorsionPolynomialOverK
    exact (chapter06_torsion_polynomial_monic D n).map _
  have hmapmonic :
      ((chapter06TorsionPolynomialOverK D n).map
          (algebraMap K (AlgebraicClosure K))).Monic := hmonic.map _
  have hsplit :
      ((chapter06TorsionPolynomialOverK D n).map
          (algebraMap K (AlgebraicClosure K))).Splits := by
    exact IsAlgClosed.splits _
  have hsep :
      (chapter06TorsionPolynomialOverK D n).Separable := by
    apply (Polynomial.nodup_aroots_iff_of_splits hmonic.ne_zero hsplit).1
    apply Multiset.nodup_iff_count_le_one.mpr
    intro x
    rw [Polynomial.aroots_def, Polynomial.count_roots]
    by_contra hcount
    have hgt :
        1 < Polynomial.rootMultiplicity x
          ((chapter06TorsionPolynomialOverK D n).map
            (algebraMap K (AlgebraicClosure K))) := by
      omega
    have hroot :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hmapmonic.ne_zero).mp hgt
    have hx : x ∈ chapter06TorsionSet D n := by
      change Polynomial.aeval x (chapter06TorsionPolynomialOverK D n) = 0
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot.1
    have hderivzero :
        Polynomial.aeval x
            (chapter06TorsionPolynomialOverK D n).derivative = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map,
        ← Polynomial.derivative_map]
      exact hroot.2
    exact (chapter06_torsion_polynomial_roots_simple D n x hx) hderivzero
  have hset :
      chapter06TorsionSet D n =
        (chapter06TorsionPolynomialOverK D n).rootSet (AlgebraicClosure K) := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      exact ⟨hmonic.ne_zero, hx⟩
    · exact And.right
  let _ : Fintype {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    (chapter06_torsion_set_finite D n).fintype
  calc
    Nat.card {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} =
        Fintype.card {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
      Nat.card_eq_fintype_card
    _ = Fintype.card {x : AlgebraicClosure K //
        x ∈ (chapter06TorsionPolynomialOverK D n).rootSet (AlgebraicClosure K)} := by
      exact Fintype.card_congr (Equiv.setCongr hset)
    _ = (chapter06TorsionPolynomialOverK D n).natDegree :=
      Polynomial.card_rootSet_eq_natDegree hsep hsplit
    _ = chapter06ResidueCardinality D ^ n := by
      change ((chapter06Sn D n).map
          (algebraMap (Chapter06ValuationRing D) K)).natDegree = _
      rw [(chapter06_torsion_polynomial_monic D n).natDegree_map]
      exact chapter06_torsion_polynomial_degree D n

theorem chapter06_primitive_torsion_set_cardinality
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ)
    (hn : 0 < n) :
    Nat.card {x : AlgebraicClosure K // x ∈ chapter06PrimitiveTorsionSet D n} =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
  classical
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  have hq : 1 < chapter06ResidueCardinality D := by
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hqminusK :
      ((chapter06ResidueCardinality D - 1 : ℕ) : K) ≠ 0 := by
    intro hzero
    have hzeroA :
        ((chapter06ResidueCardinality D - 1 : ℕ) : Chapter06ValuationRing D) = 0 := by
      apply Subtype.ext
      exact hzero
    have hzeroB :
        ((chapter06ResidueCardinality D - 1 : ℕ) : Chapter06ResidueField D) = 0 := by
      have hmap := congrArg
        (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) hzeroA
      simpa using hmap
    have hqB : (chapter06ResidueCardinality D : Chapter06ResidueField D) = 0 := by
      rw [chapter06ResidueCardinality, Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero (Chapter06ResidueField D)
    rw [Nat.cast_sub (by omega : 1 ≤ chapter06ResidueCardinality D), hqB] at hzeroB
    simp at hzeroB
  have hSn_deriv_ne_zero :
      (chapter06TorsionPolynomialOverK D (n - 1)).derivative ≠ 0 := by
    intro hzero
    have hderiv := chapter06_torsion_polynomial_derivative_at_zero D (n - 1)
    rw [hzero] at hderiv
    have hpi :
        (algebraMap (Chapter06ValuationRing D) K) D.uniformizer ≠ 0 := by
      intro h
      apply D.uniformizer_spec.1
      apply (FaithfulSMul.algebraMap_injective
        (Chapter06ValuationRing D) K)
      simpa using h
    have hderiv' : 0 =
        (algebraMap (Chapter06ValuationRing D) K) D.uniformizer ^ (n - 1) := by
      simpa using hderiv
    exact (pow_ne_zero (n - 1) hpi) hderiv'.symm
  have hQ_deriv_ne_zero :
      (chapter06PrimitiveTorsionPolynomialOverK D n).derivative ≠ 0 := by
    intro hzero
    have hq2 : chapter06ResidueCardinality D - 1 - 1 =
        chapter06ResidueCardinality D - 2 := by omega
    have hformula :
        (chapter06PrimitiveTorsionPolynomialOverK D n).derivative =
          Polynomial.C ((chapter06ResidueCardinality D - 1 : ℕ) : K) *
              (chapter06TorsionPolynomialOverK D (n - 1)) ^
                (chapter06ResidueCardinality D - 2) *
          (chapter06TorsionPolynomialOverK D (n - 1)).derivative := by
      simp [chapter06PrimitiveTorsionPolynomialOverK, chapter06Qn,
        chapter06PrimitiveDivisionPolynomial,
        chapter06TorsionPolynomialOverK, Polynomial.derivative_map,
        Polynomial.map_add, Polynomial.map_pow, Polynomial.derivative_add,
        Polynomial.derivative_C, Polynomial.derivative_pow, hq2]
    rw [hformula] at hzero
    have hSn : chapter06TorsionPolynomialOverK D (n - 1) ≠ 0 := by
      intro h
      apply hSn_deriv_ne_zero
      rw [h]
      simp
    have hleft :
        Polynomial.C ((chapter06ResidueCardinality D - 1 : ℕ) : K) *
            (chapter06TorsionPolynomialOverK D (n - 1)) ^
              (chapter06ResidueCardinality D - 2) ≠ 0 := by
      apply mul_ne_zero
      · simpa only [Polynomial.C_ne_zero] using hqminusK
      · exact pow_ne_zero _ hSn
    apply hSn_deriv_ne_zero
    exact (mul_eq_zero.mp hzero).resolve_left hleft
  have hpos : 0 < (chapter06Qn D n).natDegree := by
    rw [chapter06_Qn_degree D n hn]
    exact Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have hmonicQ := chapter06_Qn_monic D n hn
  have hirrA : Irreducible (chapter06Qn D n) := by
    apply (chapter06_Qn_is_eisenstein D n hn).irreducible
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime
      hmonicQ.isPrimitive hpos
  have hirrK :
      Irreducible (chapter06PrimitiveTorsionPolynomialOverK D n) := by
    exact (hmonicQ.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have hsep :
      (chapter06PrimitiveTorsionPolynomialOverK D n).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hirrK).2 hQ_deriv_ne_zero
  have hmonic :
      (chapter06PrimitiveTorsionPolynomialOverK D n).Monic := by
    unfold chapter06PrimitiveTorsionPolynomialOverK
    exact hmonicQ.map _
  have hsplit :
      ((chapter06PrimitiveTorsionPolynomialOverK D n).map
          (algebraMap K (AlgebraicClosure K))).Splits := by
    exact IsAlgClosed.splits _
  have hset :
      chapter06PrimitiveTorsionSet D n =
        (chapter06PrimitiveTorsionPolynomialOverK D n).rootSet
          (AlgebraicClosure K) := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      exact ⟨hmonic.ne_zero, hx⟩
    · exact And.right
  have hfinite : (chapter06PrimitiveTorsionSet D n).Finite := by
    rw [hset]
    exact Polynomial.rootSet_finite
      (chapter06PrimitiveTorsionPolynomialOverK D n) (AlgebraicClosure K)
  let _ : Fintype {x : AlgebraicClosure K // x ∈ chapter06PrimitiveTorsionSet D n} :=
    hfinite.fintype
  calc
    Nat.card {x : AlgebraicClosure K // x ∈ chapter06PrimitiveTorsionSet D n} =
        Fintype.card {x : AlgebraicClosure K // x ∈ chapter06PrimitiveTorsionSet D n} :=
      Nat.card_eq_fintype_card
    _ = Fintype.card {x : AlgebraicClosure K //
        x ∈ (chapter06PrimitiveTorsionPolynomialOverK D n).rootSet
          (AlgebraicClosure K)} := by
      exact Fintype.card_congr (Equiv.setCongr hset)
    _ = (chapter06PrimitiveTorsionPolynomialOverK D n).natDegree :=
      Polynomial.card_rootSet_eq_natDegree hsep hsplit
    _ = chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
      change ((chapter06Qn D n).map
          (algebraMap (Chapter06ValuationRing D) K)).natDegree = _
      rw [hmonicQ.natDegree_map]
      exact chapter06_Qn_degree D n hn

/-- The finite residue ring used to label torsion points. -/
abbrev Chapter06TorsionResidueRing
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :=
  Chapter06ValuationRing D ⧸
    (Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) ^ n

theorem chapter06_torsion_residue_unit_cardinality
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Nat.card (Chapter06TorsionResidueRing D n)ˣ =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
  sorry

/-- The canonical quotient-ring reduction from level `n+1` to level `n`. -/
noncomputable def chapter06TorsionResidueRingTransition
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Chapter06TorsionResidueRing D (n + 1) →+*
      Chapter06TorsionResidueRing D n := by
  exact Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ n))

theorem chapter06TorsionResidueRingTransition_mk
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ)
    (a : Chapter06ValuationRing D) :
    chapter06TorsionResidueRingTransition D n
        (Ideal.Quotient.mk
          ((Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) ^
            (n + 1)) a) =
      Ideal.Quotient.mk
        ((Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) ^ n) a := by
  exact Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ n)) a

/-- The induced canonical transition on finite-level unit groups. -/
def chapter06TorsionResidueUnitTransition
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (Chapter06TorsionResidueRing D (n + 1))ˣ →*
      (Chapter06TorsionResidueRing D n)ˣ :=
  Units.map (chapter06TorsionResidueRingTransition D n).toMonoidHom

/-- Formal scalar multiplication on a torsion level, packaged so that the
algebraic evaluation issue is explicit rather than hidden in a dummy power
series evaluation. -/
structure Chapter06TorsionAction
    {K : Type*} [Field K] [UniformSpace (AlgebraicClosure K)]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (n : ℕ) (hn : 0 < n)
    (M : Chapter06FormalModuleData D f) where
  explicit_series : f = chapter06ExplicitLubinTateSeries D
  action : Chapter06ValuationRing D →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}
  action_eval : ∀ a x,
    (action a x).1 =
      PowerSeries.eval₂
        (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K)) x.1
          (M.scalar a)
  formalAddition :
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}
  formalAddition_eval : ∀ x y,
    (formalAddition x y).1 =
      MvPowerSeries.eval₂
        (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K))
        (fun i : Fin 2 => if i = (0 : Fin 2) then x.1 else y.1)
        M.formalGroup.series
  zero : {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}
  zero_eq : zero.1 = 0
  zero_left : ∀ x, formalAddition zero x = x
  zero_right : ∀ x, formalAddition x zero = x
  commutative : ∀ x y, formalAddition x y = formalAddition y x
  associative : ∀ x y z,
    formalAddition (formalAddition x y) z =
      formalAddition x (formalAddition y z)
  inverse : {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}
  inverse_left : ∀ x, formalAddition (inverse x) x = zero
  inverse_right : ∀ x, formalAddition x (inverse x) = zero
  quotientAction : Chapter06TorsionResidueRing D n →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} →
    {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}
  quotientAction_spec : ∀ a x,
    quotientAction
      (Ideal.Quotient.mk
        ((Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) ^ n) a) x =
      action a x
  additive : ∀ a b x,
    action (a + b) x = formalAddition (action a x) (action b x)
  multiplicative : ∀ a b x, action (a * b) x = action a (action b x)
  primitive_iff_unit : ∀ a (ω : Chapter06PrimitiveTorsionPoint D n hn),
    IsUnit a ↔
      (action a (chapter06PrimitivePointAsTorsion D n hn ω)).1 ∈
        chapter06PrimitiveTorsionSet D n

theorem chapter06_torsion_action_exists
    {K : Type*} [Field K] [UniformSpace (AlgebraicClosure K)]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (n : ℕ) (hn : 0 < n)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (M : Chapter06FormalModuleData D f)
    (hExplicit : f = chapter06ExplicitLubinTateSeries D) :
    Nonempty (Chapter06TorsionAction D f n hn M) := by
  sorry

theorem chapter06_torsion_parametrization_bijective
    {K : Type*} [Field K] [UniformSpace (AlgebraicClosure K)]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (n : ℕ) (hn : 0 < n)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (M : Chapter06FormalModuleData D f)
    (A : Chapter06TorsionAction D f n hn M)
    (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    Function.Bijective (fun a : Chapter06TorsionResidueRing D n =>
      A.quotientAction a (chapter06PrimitivePointAsTorsion D n hn ω)) := by
  sorry

theorem chapter06_torsion_parametrization_primitive_iff_unit
    {K : Type*} [Field K] [UniformSpace (AlgebraicClosure K)]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (n : ℕ) (hn : 0 < n)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (M : Chapter06FormalModuleData D f)
    (A : Chapter06TorsionAction D f n hn M)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (a : Chapter06TorsionResidueRing D n) :
    IsUnit a ↔
      (A.quotientAction a
        (chapter06PrimitivePointAsTorsion D n hn ω)).1 ∈
        chapter06PrimitiveTorsionSet D n := by
  sorry

theorem chapter06_primitive_division_polynomial_factorization
    {K : Type*} [Field K] [UniformSpace (AlgebraicClosure K)]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (n : ℕ) (hn : 0 < n)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (M : Chapter06FormalModuleData D f)
    (A : Chapter06TorsionAction D f n hn M)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [Fintype (Chapter06TorsionResidueRing D n)ˣ] :
    ((chapter06Qn D n).map
        (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K))) =
      ∏ a : (Chapter06TorsionResidueRing D n)ˣ,
        (Polynomial.X - Polynomial.C (A.quotientAction
          (a : Chapter06TorsionResidueRing D n)
          (chapter06PrimitivePointAsTorsion D n hn ω)).1) := by
  sorry

/-- The field generated by one primitive torsion point. -/
noncomputable def chapter06TorsionField
    {K : Type*} [Field K] (_D : Chapter06LocalFieldData K)
    (_n : ℕ) (ω : AlgebraicClosure K) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K ({ω} : Set (AlgebraicClosure K))

noncomputable def chapter06PrimitivePointInField
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    chapter06TorsionField D n ω.point :=
  ⟨ω.point, IntermediateField.subset_adjoin K
    ({ω.point} : Set (AlgebraicClosure K)) (Set.mem_singleton ω.point)⟩

/-- The valued total-ramification predicate used for the torsion fields. -/
def chapter06TotallyRamifiedValuedExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter06LocalFieldData K)
    (V : Chapter06ValuedFiniteExtension D L) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationExtension
      D.valuation V.valuation ∧
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationScaling
      D.valuation V.valuation (Module.finrank K L) ∧
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TotallyRamifiedResidueAgreement
      D.valuation V.valuation

/-- Eisenstein's theorem gives the degree, total ramification, and
uniformizer property of a primitive torsion point. -/
theorem chapter06_torsion_field_is_eisenstein_extension
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    (V : Chapter06ValuedFiniteExtension D
      (chapter06TorsionField D n ω.point)) :
    Module.finrank K (chapter06TorsionField D n ω.point) =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) ∧
      chapter06TotallyRamifiedValuedExtension D V ∧
      V.valuation (chapter06PrimitivePointInField D n hn ω) = 1 := by
  sorry

theorem chapter06_torsion_field_is_finite_and_galois
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    FiniteDimensional K (chapter06TorsionField D n ω.point) ∧
      IsGalois K (chapter06TorsionField D n ω.point) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
