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
  sorry

theorem chapter06_primitive_division_polynomial_monic
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).Monic := by
  sorry

theorem chapter06_primitive_division_polynomial_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).natDegree =
      chapter06ResidueCardinality D ^ n *
        (chapter06ResidueCardinality D - 1) := by
  sorry

theorem chapter06_primitive_division_polynomial_constant
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).eval 0 = D.uniformizer := by
  sorry

theorem chapter06_primitive_division_polynomial_mod_uniformizer
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).map
        (algebraMap (Chapter06ValuationRing D) (Chapter06ResidueField D)) =
      Polynomial.X ^
        (chapter06ResidueCardinality D ^ n *
          (chapter06ResidueCardinality D - 1)) := by
  sorry

theorem chapter06_primitive_division_polynomial_is_eisenstein
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    (chapter06PrimitiveDivisionPolynomial D n).IsEisensteinAt
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) := by
  sorry

theorem chapter06_Qn_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).natDegree =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
  sorry

theorem chapter06_Qn_monic
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).Monic := by
  sorry

theorem chapter06_Qn_constant
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).eval 0 = D.uniformizer := by
  sorry

theorem chapter06_Qn_is_eisenstein
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n) :
    (chapter06Qn D n).IsEisensteinAt
      (IsLocalRing.maximalIdeal (Chapter06ValuationRing D)) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem chapter06_torsion_polynomial_roots_simple
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ)
    (x : AlgebraicClosure K)
    (hx : x ∈ chapter06TorsionSet D n) :
    Polynomial.aeval x (chapter06TorsionPolynomialOverK D n).derivative ≠ 0 := by
  sorry

theorem chapter06_torsion_set_finite
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Set.Finite (chapter06TorsionSet D n) := by
  sorry

theorem chapter06_torsion_set_cardinality
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Nat.card {x : AlgebraicClosure K // x ∈ chapter06TorsionSet D n} =
      chapter06ResidueCardinality D ^ n := by
  sorry

theorem chapter06_primitive_torsion_set_cardinality
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ)
    (hn : 0 < n) :
    Nat.card {x : AlgebraicClosure K // x ∈ chapter06PrimitiveTorsionSet D n} =
      chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1) := by
  sorry

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
