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
  classical
  have hExplicit : f = chapter06ExplicitLubinTateSeries D := A.explicit_series
  subst f
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  let R := Chapter06ValuationRing D
  let I : Ideal R := Ideal.span ({D.uniformizer} : Set R)
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.complete.1
  let _ : IsDiscreteValuationRing R := by
    change IsDiscreteValuationRing D.valuation.toValuation.valuationSubring
    infer_instance
  have hπirr : Irreducible (D.uniformizer : R) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (D.uniformizer : R)).2
    exact D.uniformizer_spec.2
  have hquotcard : Nat.card (R ⧸ I ^ n) =
      chapter06ResidueCardinality D ^ n := by
    change Nat.card (R ⧸ (Ideal.span ({D.uniformizer} : Set R)) ^ n) =
      Nat.card (Chapter06ResidueField D) ^ n
    rw [Ideal.span_singleton_pow]
    exact
      @LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapter_quotient_cardinality_pow
        R _ _ _ (D.uniformizer : R) hπirr D.residue_finite n
  let _ : Finite (R ⧸ I ^ n) := by
    apply Nat.finite_of_card_ne_zero
    rw [hquotcard]
    exact Nat.ne_of_gt (pow_pos (chapter06_residue_cardinality_pos D) n)
  let _ : Fintype (R ⧸ I ^ n) := Fintype.ofFinite _
  let _ : Fintype {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    (chapter06_torsion_set_finite D n).fintype
  let p : {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    chapter06PrimitivePointAsTorsion D n hn ω
  let _ : Zero {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    ⟨A.zero⟩
  let _ : Add {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    ⟨A.formalAddition⟩
  let _ : Neg {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    ⟨A.inverse⟩
  let _ : AddCommGroup {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} :=
    { add := A.formalAddition
      zero := A.zero
      neg := A.inverse
      add_assoc := A.associative
      zero_add := A.zero_left
      add_zero := A.zero_right
      neg_add_cancel := A.inverse_left
      add_comm := A.commutative
      nsmul := nsmulRec
      zsmul := zsmulRec
      nsmul_zero := by intros; rfl
      nsmul_succ := by intros; rfl
      zsmul_zero' := by intros; rfl
      zsmul_succ' := by intros; rfl
      zsmul_neg' := by intros; rfl
      sub_eq_add_neg := by intros; rfl }
  have h_action_zero (x : {x : AlgebraicClosure K //
      x ∈ chapter06TorsionSet D n}) : A.action 0 x = A.zero := by
    apply Subtype.ext
    rw [A.action_eval, M.scalar_zero]
    rw [A.zero_eq]
    have hz : PowerSeries.eval₂ (algebraMap (Chapter06ValuationRing D)
        (AlgebraicClosure K)) (↑x)
        (↑(0 : Polynomial (Chapter06ValuationRing D))) =
        (0 : AlgebraicClosure K) := by
      rw [PowerSeries.eval₂_coe, Polynomial.eval₂_zero]
    simpa only [Polynomial.coe_zero] using hz
  have h_action_one (x : {x : AlgebraicClosure K //
      x ∈ chapter06TorsionSet D n}) : A.action 1 x = x := by
    apply Subtype.ext
    rw [A.action_eval, M.scalar_one, PowerSeries.eval₂_X]
  have h_action_neg (b : R)
      (x : {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}) :
      A.action (-b) x = -A.action b x := by
    have hz : A.formalAddition (A.action b x) (A.action (-b) x) = A.zero := by
      simpa [h_action_zero x] using (A.additive b (-b) x).symm
    exact eq_neg_of_add_eq_zero_right hz
  have h_action_sub (r s : R)
      (x : {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}) :
      A.action (r - s) x = A.action r x - A.action s x := by
    calc
      A.action (r - s) x = A.action (r + -s) x := by rw [sub_eq_add_neg]
      _ = A.formalAddition (A.action r x) (A.action (-s) x) :=
        A.additive r (-s) x
      _ = A.action r x - A.action s x := by rw [h_action_neg]; rfl
  have h_action_unit_cancel (u : Rˣ)
      (x : {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}) :
      A.action ((↑(u⁻¹) : R)) (A.action (u : R) x) = x := by
    calc
      A.action ((↑(u⁻¹) : R)) (A.action (u : R) x) =
          A.action ((↑(u⁻¹) : R) * (u : R)) x :=
        (A.multiplicative (↑(u⁻¹) : R) (u : R) x).symm
      _ = A.action 1 x := by simp
      _ = x := h_action_one x
  have hdiv (k m : ℕ) (hkm : k ≤ m) :
      chapter06Sn D k ∣ chapter06Sn D m := by
    induction m with
    | zero =>
        have : k = 0 := by omega
        subst k
        exact dvd_rfl
    | succ m ih =>
        by_cases hks : k = m + 1
        · subst k
          exact dvd_rfl
        · have hkm' : k ≤ m := by omega
          exact dvd_trans (ih hkm')
            ⟨chapter06PrimitiveDivisionPolynomial D m,
              chapter06_torsion_polynomial_succ_factorization D m⟩
  have hscalar_zero_imp (k : ℕ) (hk : k < n) :
      A.action ((D.uniformizer : R) ^ k) p ≠ A.zero := by
    intro hzero
    have heval : PowerSeries.eval₂
        (algebraMap R (AlgebraicClosure K)) p.1
        (M.scalar ((D.uniformizer : R) ^ k)) = 0 := by
      calc
        PowerSeries.eval₂ (algebraMap R (AlgebraicClosure K)) p.1
            (M.scalar ((D.uniformizer : R) ^ k)) =
            (A.action ((D.uniformizer : R) ^ k) p).1 :=
          (A.action_eval ((D.uniformizer : R) ^ k) p).symm
        _ = A.zero.1 := congrArg Subtype.val hzero
        _ = 0 := A.zero_eq
    have hscalar := chapter06_explicit_torsion_sequence_is_scalar_power D k M
    rw [hscalar] at heval
    have hSk : Polynomial.eval₂
        (algebraMap R (AlgebraicClosure K)) p.1 (chapter06Sn D k) = 0 := by
      simpa [PowerSeries.eval₂_coe] using heval
    have hprev : Polynomial.eval₂
        (algebraMap R (AlgebraicClosure K)) p.1
          (chapter06Sn D (n - 1)) = 0 := by
      obtain ⟨q, hq⟩ := hdiv k (n - 1) (by omega)
      rw [hq, Polynomial.eval₂_mul, hSk, zero_mul]
    have hprev' : Polynomial.aeval p.1
        (chapter06TorsionPolynomialOverK D (n - 1)) = 0 := by
      change Polynomial.aeval p.1
        ((chapter06Sn D (n - 1)).map (algebraMap R K)) = 0
      rw [Polynomial.aeval_def, Polynomial.eval₂_map,
        ← IsScalarTower.algebraMap_eq]
      exact hprev
    exact (chapter06_primitive_torsion_point_is_not_previous_root D n hn ω)
      hprev'
  let φ : Chapter06TorsionResidueRing D n →
      {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} := fun a =>
    A.quotientAction a p
  have hφinj : Function.Injective φ := by
    intro a b hab
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : A.action r p = A.action s p := by
      rw [← A.quotientAction_spec r p, ← A.quotientAction_spec s p]
      exact hab
    have hzero : A.action (r - s) p = A.zero := by
      calc
        A.action (r - s) p = A.action r p - A.action s p :=
          h_action_sub r s p
        _ = 0 := sub_eq_zero.mpr hab'
        _ = A.zero := by rfl
    rw [Ideal.Quotient.eq]
    by_cases hd : r - s = 0
    · simp [hd]
    obtain ⟨k, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπirr
    by_cases hkn : n ≤ k
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨(u : R) * (D.uniformizer : R) ^ (k - n), ?_⟩
      calc
        r - s = (u : R) * (D.uniformizer : R) ^ k := hu
        _ = (u : R) * ((D.uniformizer : R) ^ n *
              (D.uniformizer : R) ^ (k - n)) := by
                rw [← pow_add, show n + (k - n) = k by omega]
        _ = (D.uniformizer : R) ^ n *
            ((u : R) * (D.uniformizer : R) ^ (k - n)) := by ring
    · have hk : k < n := by omega
      have hπzero : A.action ((D.uniformizer : R) ^ k) p = A.zero := by
        have h_action_at_zero (a : R) : A.action a A.zero = A.zero := by
          calc
            A.action a A.zero = A.action a (A.action 0 p) := by
              rw [h_action_zero p]
            _ = A.action (a * 0) p := by rw [A.multiplicative]
            _ = A.action 0 p := by simp
            _ = A.zero := h_action_zero p
        have hmul :
            A.action (u : R)
                (A.action ((D.uniformizer : R) ^ k) p) = A.zero := by
          rw [← A.multiplicative, ← hu, hzero]
        calc
          A.action ((D.uniformizer : R) ^ k) p =
              A.action ((↑(u⁻¹) : R))
                (A.action (u : R)
                  (A.action ((D.uniformizer : R) ^ k) p)) := by
            rw [h_action_unit_cancel]
          _ = A.action ((↑(u⁻¹) : R)) A.zero := by rw [hmul]
          _ = A.zero := h_action_at_zero _
      exact False.elim ((hscalar_zero_imp k hk) hπzero)
  have hcard : Fintype.card (Chapter06TorsionResidueRing D n) =
      Fintype.card {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hquotcard.trans (chapter06_torsion_set_cardinality D n).symm
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).2 ⟨hφinj, hcard⟩
  exact hbij

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
  classical
  let _ := hf
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  let I : Ideal (Chapter06ValuationRing D) :=
    Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))
  have hI : I = IsLocalRing.maximalIdeal (Chapter06ValuationRing D) := by
    change Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D)) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01MaximalIdeal
        D.valuation.toValuation
    exact D.uniformizer_spec.2.symm
  let _ : I.IsMaximal := hI ▸ inferInstance
  have hunit : IsUnit (Ideal.Quotient.mk (I ^ n) r) ↔ IsUnit r := by
    rw [Ideal.Quotient.isUnit_mk_pow_iff_notMem I (Nat.ne_of_gt hn)]
    rw [hI, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    simp
  calc
    IsUnit (Ideal.Quotient.mk
        ((Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) ^ n) r) ↔
        IsUnit r := by simpa [I] using hunit
    _ ↔
        (A.quotientAction
          (Ideal.Quotient.mk
            ((Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) ^ n) r)
          (chapter06PrimitivePointAsTorsion D n hn ω)).1 ∈
          chapter06PrimitiveTorsionSet D n := by
      rw [A.quotientAction_spec r
        (chapter06PrimitivePointAsTorsion D n hn ω)]
      exact A.primitive_iff_unit r ω

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
  classical
  let T := Chapter06TorsionResidueRing D n
  let X := {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n}
  let Y := {x : AlgebraicClosure K // x ∈ chapter06PrimitiveTorsionSet D n}
  let p₀ : X := chapter06PrimitivePointAsTorsion D n hn ω
  have hYfinite : Set.Finite (chapter06PrimitiveTorsionSet D n) := by
    apply (chapter06_torsion_set_finite D n).subset
    intro x hx
    exact (chapter06_mem_primitiveTorsionSet_iff D n hn x).mp hx |>.1
  let _ : Fintype Y := hYfinite.fintype
  let φ : T → X := fun a => A.quotientAction a p₀
  have hφ : Function.Bijective φ := by
    exact chapter06_torsion_parametrization_bijective D n hn f hf M A ω
  have hprimitive (a : T) : IsUnit a ↔ (φ a).1 ∈
      chapter06PrimitiveTorsionSet D n := by
    dsimp [φ]
    exact chapter06_torsion_parametrization_primitive_iff_unit
      D n hn f hf M A ω a
  let e : Tˣ → Y := fun a =>
    ⟨(φ (a : T)).1, (hprimitive (a : T)).1 a.isUnit⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      apply Units.ext
      apply hφ.1
      apply Subtype.ext
      simpa [e] using congrArg (fun z : Y => z.1) hab
    · intro y
      let hyX : X :=
        ⟨y.1, (chapter06_mem_primitiveTorsionSet_iff D n hn y.1).mp y.2 |>.1⟩
      obtain ⟨a, ha⟩ := hφ.2 hyX
      have hmem : (φ a).1 ∈ chapter06PrimitiveTorsionSet D n := by
        rw [ha]
        simp [hyX, y.2]
      have hunit : IsUnit a := (hprimitive a).2 hmem
      refine ⟨hunit.unit, ?_⟩
      apply Subtype.ext
      change (φ (↑hunit.unit : T)).1 = y.1
      rw [hunit.unit_spec, ha]
  have hcardU : Fintype.card Tˣ =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
    calc
      Fintype.card Tˣ = Fintype.card Y :=
        Fintype.card_congr (Equiv.ofBijective e he)
      _ = Nat.card Y := (Nat.card_eq_fintype_card).symm
      _ = chapter06ResidueCardinality D ^ (n - 1) *
          (chapter06ResidueCardinality D - 1) := by
        exact chapter06_primitive_torsion_set_cardinality D n hn
  let P : Polynomial (AlgebraicClosure K) :=
    (chapter06Qn D n).map
      (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K))
  have hPmonic : P.Monic := by
    exact (chapter06_Qn_monic D n hn).map _
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hPdegree : P.natDegree =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
    change ((chapter06Qn D n).map
        (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K))).natDegree = _
    rw [(chapter06_Qn_monic D n hn).natDegree_map]
    exact chapter06_Qn_degree D n hn
  let g : Tˣ → AlgebraicClosure K := fun a => (φ (a : T)).1
  have hg : Function.Injective g := by
    intro a b hab
    apply Units.ext
    apply hφ.1
    exact Subtype.ext hab
  have hgroot (a : Tˣ) : P.eval (g a) = 0 := by
    have hmem := (hprimitive (a : T)).1 a.isUnit
    change Polynomial.aeval (g a)
      ((chapter06Qn D n).map (algebraMap (Chapter06ValuationRing D) K)) = 0 at hmem
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq] at hmem
    change Polynomial.eval₂ (RingHom.id (AlgebraicClosure K)) (g a)
      ((chapter06Qn D n).map
        (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K))) = 0
    rw [Polynomial.eval₂_map]
    simpa only [RingHom.id_comp] using hmem
  let S : Finset (AlgebraicClosure K) := Finset.univ.image g
  have hSroot : ∀ x ∈ S, P.eval x = 0 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact hgroot a
  have hScard : S.card = P.natDegree := by
    calc
      S.card = Fintype.card Tˣ := by
        dsimp [S]
        exact (Finset.card_image_iff.mpr hg.injOn).trans Finset.card_univ
      _ = chapter06ResidueCardinality D ^ (n - 1) *
          (chapter06ResidueCardinality D - 1) := hcardU
      _ = P.natDegree := hPdegree.symm
  have hroots : P.roots = S.val := by
    exact Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hSroot
      (hScard.symm.le) hPne
  change P = _
  calc
    P = (P.roots.map (fun x => Polynomial.X - Polynomial.C x)).prod := by
      symm
      exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
        hPmonic IsAlgClosed.card_roots_eq_natDegree
    _ = S.prod (fun x => Polynomial.X - Polynomial.C x) := by
      rw [hroots, ← Finset.prod_eq_multiset_prod]
    _ = ∏ a : Tˣ, (Polynomial.X - Polynomial.C (g a)) := by
      dsimp [S]
      rw [Finset.prod_image]
      exact hg.injOn

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
  let L := chapter06TorsionField D n ω.point
  let Pi : L := chapter06PrimitivePointInField D n hn ω
  have hmonicQ := chapter06_Qn_monic D n hn
  have hq : 1 < chapter06ResidueCardinality D := by
    let _ := D.residue_finite
    let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hposQ : 0 < (chapter06Qn D n).natDegree := by
    rw [chapter06_Qn_degree D n hn]
    exact Nat.mul_pos (pow_pos (chapter06_residue_cardinality_pos D) _)
      (by omega)
  have hirrA : Irreducible (chapter06Qn D n) := by
    apply (chapter06_Qn_is_eisenstein D n hn).irreducible
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime
      hmonicQ.isPrimitive hposQ
  have hrootK : Polynomial.aeval ω.point
      (chapter06PrimitiveTorsionPolynomialOverK D n) = 0 :=
    chapter06_primitive_torsion_point_is_primitive_division_root D n hn ω
  have hrootQ : Polynomial.eval₂
      (algebraMap (Chapter06ValuationRing D) (AlgebraicClosure K)) ω.point
      (chapter06Qn D n) = 0 := by
    change Polynomial.eval₂ (algebraMap K (AlgebraicClosure K)) ω.point
      ((chapter06Qn D n).map (algebraMap (Chapter06ValuationRing D) K)) = 0 at hrootK
    rw [Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq] at hrootK
    exact hrootK
  have hrootL : Polynomial.eval₂
      (algebraMap (Chapter06ValuationRing D) L) Pi
      (chapter06Qn D n) = 0 := by
    apply L.val.injective
    change L.val (Polynomial.eval₂
      (algebraMap (Chapter06ValuationRing D) L) Pi
      (chapter06Qn D n)) = 0
    change L.val.toRingHom (Polynomial.eval₂
      (algebraMap (Chapter06ValuationRing D) L) Pi
      (chapter06Qn D n)) = 0
    rw [Polynomial.hom_eval₂]
    simpa [Pi, L, chapter06PrimitivePointInField,
      IsScalarTower.algebraMap_eq] using hrootQ
  have hgenIF : IntermediateField.adjoin K ({Pi} : Set L) = ⊤ := by
    apply IntermediateField.map_injective L.val
    rw [IntermediateField.adjoin_map]
    have hmaptop : IntermediateField.map L.val (⊤ : IntermediateField K L) = L := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rw [hmaptop]
    rw [Set.image_singleton]
    change IntermediateField.adjoin K ({ω.point} : Set (AlgebraicClosure K)) =
      IntermediateField.adjoin K ({ω.point} : Set (AlgebraicClosure K))
    rfl
  have hPiAlg : IsAlgebraic K Pi :=
    Algebra.IsAlgebraic.isAlgebraic Pi
  have hgen : Algebra.adjoin K ({Pi} : Set L) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hPiAlg)).mp hgenIF
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.complete.1
  let _ : Valuation.IsRankOneDiscrete V.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      V.valuation V.complete.1
  let _ : IsDiscreteValuationRing (Chapter06ValuationRing D) := by
    change IsDiscreteValuationRing D.valuation.toValuation.valuationSubring
    infer_instance
  have hval : D.valuation.IsEquiv
      (AddValuation.comap (algebraMap K L) V.valuation) := V.extension
  let _ : Valuation.HasExtension D.valuation.toValuation V.valuation.toValuation :=
    ⟨hval⟩
  have hupper : (V.valuation.toValuation.valuationSubring : Set L) =
      (integralClosure (Chapter06ValuationRing D) L : Set L) := by
    exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_extension_valuation_ring_is_integral_closure
      D.valuation.toValuation V.valuation.toValuation D.complete.2
  have hEcustom :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
        D.uniformizer (chapter06Qn D n) := by
    have hEi := chapter06_Qn_is_eisenstein D n hn
    refine ⟨hmonicQ, hposQ, ?_, ?_, D.uniformizer_spec.2.symm⟩
    · intro i hi
      rw [← D.uniformizer_spec.2]
      exact hEi.mem hi
    · rw [← Ideal.span_singleton_pow, ← D.uniformizer_spec.2]
      exact hEi.notMem
  have hbaseValuationRing :
      (D.valuation.toValuation.valuationSubring : Set K) =
        Set.range (algebraMap (Chapter06ValuationRing D) K) := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact a.property
  have hbaseIntegers :
      D.valuation.toValuation.Integers (Chapter06ValuationRing D) := by
    refine
      { hom_inj := IsFractionRing.injective (Chapter06ValuationRing D) K
        map_le_one := ?_
        exists_of_le_one := ?_ }
    · intro a
      apply (Valuation.mem_valuationSubring_iff D.valuation.toValuation
        (algebraMap (Chapter06ValuationRing D) K a)).mp
      change (algebraMap (Chapter06ValuationRing D) K a) ∈
        (D.valuation.toValuation.valuationSubring : Set K)
      rw [hbaseValuationRing]
      exact ⟨a, rfl⟩
    · intro x hx
      have hx' : x ∈ D.valuation.toValuation.valuationSubring :=
        (Valuation.mem_valuationSubring_iff D.valuation.toValuation x).mpr hx
      change x ∈ (D.valuation.toValuation.valuationSubring : Set K) at hx'
      rw [hbaseValuationRing] at hx'
      exact hx'
  have hE :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_root_is_uniformizer_and_totally_ramified
      D.valuation.toValuation V.valuation.toValuation D.uniformizer
      (chapter06Qn D n) Pi hEcustom
      hrootL (chapter06_Qn_degree D n hn) hgen hbaseIntegers
      hbaseValuationRing hupper
  have hresrank :
      Module.finrank
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
            D.valuation)
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
            V.valuation) = 1 := by
    let A0 := Chapter06ValuationRing D
    let B0 := V.valuation.toValuation.valuationSubring
    let mA := IsLocalRing.maximalIdeal A0
    let mB := IsLocalRing.maximalIdeal B0
    let _ : Algebra A0 B0 :=
      Valuation.HasExtension.instAlgebra_valuationSubring
        D.valuation.toValuation V.valuation.toValuation
    let _ : IsLocalHom (algebraMap A0 B0) :=
      Valuation.HasExtension.instIsLocalHomValuationInteger
        (vR := D.valuation.toValuation) (vS := V.valuation.toValuation)
    let eA : (A0 ⧸ mA) ≃+*
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
          D.valuation := RingEquiv.refl _
    let eB : (B0 ⧸ mB) ≃+*
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
          V.valuation := RingEquiv.refl _
    have hfin : Module.finrank (A0 ⧸ mA) (B0 ⧸ mB) =
        Module.finrank
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
            D.valuation)
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
            V.valuation) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA eB
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun _ => rfl)
    have hquot : Module.finrank (A0 ⧸ mA) (B0 ⧸ mB) = 1 := by
      rw [← Ideal.inertiaDeg_eq_of_isMaximal mA mB]
      exact hE.2.2.1
    exact hfin.symm.trans hquot
  have htotal :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08TotallyRamified
        D.valuation V.valuation hval := by
    change Module.finrank
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
          D.valuation)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField
          V.valuation) = 1
    exact hresrank
  have hPiVal : V.valuation Pi = 1 := by
    have hvg :
        MonoidWithZeroHom.valueGroup (.ofClass V.valuation.toValuation) = ⊤ := by
      obtain ⟨π, _hπ0, hπ, _hv⟩ := V.complete.1
      have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
        intro z
        induction z with
        | zero => simp
        | succ z ih =>
            rw [succ_nsmul, Nat.cast_succ, ih]
      have hnegcast : ∀ z : ℕ,
          (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
        intro z
        simp [Int.negSucc_eq]
      have hpow : ∀ z : ℤ, V.valuation (π ^ z) = (z : WithTop ℤ) := by
        intro z
        cases z with
        | ofNat z =>
            change V.valuation (π ^ (z : ℤ)) = (z : WithTop ℤ)
            rw [zpow_natCast, V.valuation.map_pow, hπ, hone]
        | negSucc z =>
            rw [zpow_negSucc, V.valuation.map_inv, V.valuation.map_pow, hπ]
            rw [hnegcast z, hone]
      apply top_unique
      intro u _hu
      have hu0 :
          (OrderDual.ofDual (Multiplicative.toAdd
            (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
        intro htop
        apply Units.ne_zero u
        change Multiplicative.ofAdd (OrderDual.toDual
          (OrderDual.ofDual (Multiplicative.toAdd
            (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
          Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
        rw [htop]
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hu0
      apply MonoidWithZeroHom.mem_valueGroup
      refine ⟨π ^ z, ?_⟩
      change Multiplicative.ofAdd (OrderDual.toDual (V.valuation (π ^ z))) = u
      rw [hpow z]
      exact congrArg (fun t : WithTop ℤ =>
        Multiplicative.ofAdd (OrderDual.toDual t)) hz
    let γ : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ :=
      Units.mk0 (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)))
        (by
          intro h
          have htop : (1 : WithTop ℤ) = ⊤ := congrArg (fun z =>
            OrderDual.ofDual (Multiplicative.toAdd z)) h
          exact (WithTop.coe_lt_top 1).ne htop)
    have hγ_lt : γ < 1 := by
      change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) < 1
      change (0 : WithTop ℤ) < 1
      norm_num
    have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
      intro z
      induction z with
      | zero => simp
      | succ z ih =>
          rw [succ_nsmul, Nat.cast_succ, ih]
    have hnegcast : ∀ z : ℕ,
        (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
      intro z
      simp [Int.negSucc_eq]
    have hγpow : ∀ z : ℤ,
        (γ ^ z : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ).val =
          Multiplicative.ofAdd (OrderDual.toDual (z : WithTop ℤ)) := by
      intro z
      cases z with
      | ofNat z =>
          simp [γ, zpow_natCast]
          change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^ z =
            Multiplicative.ofAdd (OrderDual.toDual (z : WithTop ℤ))
          rw [← ofAdd_nsmul z (OrderDual.toDual (1 : WithTop ℤ))]
          congr 1
          exact congrArg OrderDual.toDual (hone z)
      | negSucc z =>
          simp [γ, zpow_negSucc]
          change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
              (z + 1))⁻¹ =
            Multiplicative.ofAdd (OrderDual.toDual (Int.negSucc z : WithTop ℤ))
          rw [hnegcast z]
          change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
              (z + 1))⁻¹ =
            Multiplicative.ofAdd (-(OrderDual.toDual ((z + 1 : ℕ) : WithTop ℤ)))
          rw [ofAdd_neg]
          rw [← ofAdd_nsmul (z + 1) (OrderDual.toDual (1 : WithTop ℤ))]
          congr 1
          exact congrArg OrderDual.toDual (hone (z + 1))
    have hγ_zpowers : Subgroup.zpowers γ =
        (⊤ : Subgroup ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)) := by
      apply top_unique
      intro u _hu
      have hu0 :
          (OrderDual.ofDual (Multiplicative.toAdd
            (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
        intro htop
        apply Units.ne_zero u
        change Multiplicative.ofAdd (OrderDual.toDual
          (OrderDual.ofDual (Multiplicative.toAdd
            (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
          Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
        rw [htop]
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hu0
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨z, ?_⟩
      apply Units.ext
      rw [hγpow]
      exact congrArg (fun t : WithTop ℤ =>
        Multiplicative.ofAdd (OrderDual.toDual t)) hz
    have hγ_zpowers_v : Subgroup.zpowers γ =
        MonoidWithZeroHom.valueGroup (.ofClass V.valuation.toValuation) := by
      rw [hvg]
      exact hγ_zpowers
    have hgen : γ = LinearOrderedCommGroup.Subgroup.genLTOne
        (MonoidWithZeroHom.valueGroup (.ofClass V.valuation.toValuation)) := by
      exact LinearOrderedCommGroup.Subgroup.genLTOne_unique
        (MonoidWithZeroHom.valueGroup (.ofClass V.valuation.toValuation))
        hγ_lt hγ_zpowers_v
    have hPiUniform : V.valuation.toValuation Pi =
        Valuation.IsRankOneDiscrete.generator V.valuation.toValuation := hE.1
    have hgenval :
        (Valuation.IsRankOneDiscrete.generator V.valuation.toValuation :
          Multiplicative (WithTop ℤ)ᵒᵈ) =
          Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) := by
      calc
        (Valuation.IsRankOneDiscrete.generator V.valuation.toValuation :
            Multiplicative (WithTop ℤ)ᵒᵈ) =
            LinearOrderedCommGroup.Subgroup.genLTOne
              (MonoidWithZeroHom.valueGroup (.ofClass V.valuation.toValuation)) :=
          congrArg Units.val
            (Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator
              V.valuation.toValuation).symm
        _ = γ := (congrArg Units.val hgen).symm
        _ = Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) := by rfl
    have hmul :
        Multiplicative.ofAdd (OrderDual.toDual (V.valuation Pi)) =
          Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) := by
      calc
        Multiplicative.ofAdd (OrderDual.toDual (V.valuation Pi)) =
            V.valuation.toValuation Pi := by rfl
        _ = Valuation.IsRankOneDiscrete.generator V.valuation.toValuation :=
          hPiUniform
        _ = Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) := hgenval
    exact congrArg (fun z : Multiplicative (WithTop ℤ)ᵒᵈ =>
      OrderDual.ofDual (Multiplicative.toAdd z)) hmul
  have hfiniteUpper : Module.Finite (Chapter06ValuationRing D)
      V.valuation.toValuation.valuationSubring :=
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_finite_extension_remains_local
      D.valuation.toValuation V.valuation.toValuation D.complete.2).1
  have hfiniteIntegralClosure : Module.Finite (Chapter06ValuationRing D)
      (integralClosure (Chapter06ValuationRing D) L) := by
    let e : (integralClosure (Chapter06ValuationRing D) L) ≃ₗ[Chapter06ValuationRing D]
        V.valuation.toValuation.valuationSubring :=
      { toFun := fun x =>
          ⟨x.1, (Set.ext_iff.mp hupper x.1).mpr x.2⟩
        invFun := fun x =>
          ⟨x.1, (Set.ext_iff.mp hupper x.1).mp x.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro x; apply Subtype.ext; rfl
        map_add' := by intro x y; apply Subtype.ext; rfl
        map_smul' := by intro c x; apply Subtype.ext; rfl }
    exact Module.Finite.equiv e.symm
  have hintegralK : ∀ x : K,
      IsIntegral (Chapter06ValuationRing D) x ↔ 0 ≤ D.valuation x := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ :=
        (IsIntegrallyClosed.isIntegral_iff (R := Chapter06ValuationRing D)).mp hx
      have ha0 : 0 ≤ D.valuation (a : K) := a.property
      have ha' : (a : K) = x := ha
      rw [ha'] at ha0
      exact ha0
    · intro hx
      apply (IsIntegrallyClosed.isIntegral_iff
        (R := Chapter06ValuationRing D)).mpr
      exact ⟨⟨x, hx⟩, rfl⟩
  have hintegralL : ∀ x : L,
      IsIntegral (Chapter06ValuationRing D) x ↔ 0 ≤ V.valuation x := by
    intro x
    constructor
    · intro hx
      change x ∈ (integralClosure (Chapter06ValuationRing D) L : Set L) at hx
      rw [← hupper] at hx
      exact hx
    · intro hx
      have hx' : x ∈ V.valuation.toValuation.valuationSubring := by
        exact (Valuation.mem_valuationSubring_iff V.valuation.toValuation x).mpr hx
      change x ∈ (integralClosure (Chapter06ValuationRing D) L : Set L)
      rw [← hupper]
      exact hx'
  obtain ⟨e, he, hscale, hdegree⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_uniformizer_extension_degree_data
      D.complete.2 hfiniteIntegralClosure D.valuation V.valuation D.complete.1
      V.complete.1 hval htotal hintegralK hintegralL Pi hPiVal
  have hnsmul : ∀ m : ℕ, ∀ z : WithTop ℤ,
      m • z = (m : WithTop ℤ) * z := by
    intro m z
    induction z using WithTop.recTopCoe with
    | top =>
        cases m with
        | zero => simp
        | succ m =>
            have hm : (↑m + 1 : WithTop ℤ) ≠ 0 := by positivity
            simp [succ_nsmul, WithTop.mul_top hm]
    | coe z =>
        rw [← WithTop.coe_nsmul]
        norm_num [nsmul_eq_mul]
  have hscaleFinal :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationScaling
        D.valuation V.valuation (Module.finrank K L) := by
    rw [hdegree]
    unfold LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationScaling
    intro x
    by_cases hx : x = 0
    · subst x
      simp [Nat.ne_of_gt he]
    · calc
        V.valuation (algebraMap K L x) = e • D.valuation x := by
          simpa [L] using hscale x hx
        _ = (e : WithTop ℤ) * D.valuation x := hnsmul e (D.valuation x)
  have hresAgreement :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TotallyRamifiedResidueAgreement
        D.valuation V.valuation := by
    refine ⟨V.extension, ?_⟩
    intro hext
    have htotal' :
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08TotallyRamified
          D.valuation V.valuation hext := htotal
    rcases
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_total_ramification_iff_residue_fields_equal
          D.valuation V.valuation hext).mp htotal' with ⟨e⟩
    exact ⟨e.symm⟩
  refine ⟨hE.2.2.2.2, ?_, hPiVal⟩
  exact ⟨V.extension, hscaleFinal, hresAgreement⟩

theorem chapter06_torsion_field_is_finite_and_galois
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn) :
    FiniteDimensional K (chapter06TorsionField D n ω.point) ∧
      IsGalois K (chapter06TorsionField D n ω.point) := by
  have hfinite : FiniteDimensional K (chapter06TorsionField D n ω.point) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic ω.point).isIntegral
  refine ⟨hfinite, ?_⟩
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
