import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section03CompletenessOfTheExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

open scoped WithZero

/-! # Book 2, Chapter 1, Section 1.4

The two absolute-value conventions are defined as separate functions.  Their
restriction laws and the degree factor are stated explicitly, so a later proof
cannot accidentally replace normalized valuation equality by literal equality.
-/

/-! ### The base-compatible normalization -/

/-- The absolute value `c ^ v(x)` attached to an additive valuation. -/
def chapter01BaseAbsoluteValue {K : Type*} [Field K]
    (c : ℝ) (v : AddValuation K (WithTop ℤ)) : K → ℝ :=
  by
    classical
    exact fun x => if x = 0 then 0 else
      Real.rpow c (((v x).untopD 0 : ℤ) : ℝ)

/-- The absolute value `c ^ (v_L(y) / e)` that literally restricts to the base. -/
def chapter01RelativeAbsoluteValue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : ℝ) (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : L → ℝ :=
  by
    classical
    exact fun y => if y = 0 then 0 else
      Real.rpow c ((((vL y).untopD 0 : ℤ) : ℝ) / (e : ℝ))

/-- A positive normalized scale gives the literal restriction formula. -/
theorem chapter01_relative_absolute_value_restricts
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : ℝ) (hc : 0 < c ∧ c < 1)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e) :
    ∀ x : K,
      chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e
          (algebraMap K L x) =
        chapter01BaseAbsoluteValue c vK x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [chapter01RelativeAbsoluteValue, chapter01BaseAbsoluteValue]
  · have hmapx : algebraMap K L x ≠ 0 := by
      intro h
      apply hx
      apply FaithfulSMul.algebraMap_injective K L
      simpa using h
    have hvKx : vK x ≠ (⊤ : WithTop ℤ) :=
      (AddValuation.ne_top_iff vK).2 hx
    have hvLx : vL (algebraMap K L x) ≠ (⊤ : WithTop ℤ) :=
      (AddValuation.ne_top_iff vL).2 hmapx
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hvKx
    have hn' : vK x = (n : WithTop ℤ) := hn.symm
    have hval := hscale.2 x hx
    have hvLint : (vL (algebraMap K L x)).untopD 0 = e * n := by
      rw [hval, hn', ← WithTop.coe_nsmul (n : ℤ) e]
      rfl
    have hexp :
        (((vL (algebraMap K L x)).untopD 0 : ℤ) : ℝ) / (e : ℝ) =
          (((vK x).untopD 0 : ℤ) : ℝ) := by
      rw [hvLint, hn']
      simp only [WithTop.untopD_coe]
      push_cast
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hscale.1)]
    simp only [chapter01RelativeAbsoluteValue, chapter01BaseAbsoluteValue,
      hmapx, hx, if_false]
    rw [hexp]

/-- Completeness and normalized discreteness for an additive valuation. -/
def chapter01CompleteAdditiveValuation {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v ∧
    IsAdicComplete
      (IsLocalRing.maximalIdeal v.toValuation.valuationSubring)
      v.toValuation.valuationSubring

/-- For a finite complete extension, the relative absolute value is the norm root. -/
-- STATEMENT_NEEDS_UPDATE: The hypotheses constrain `vL` only on the image of `K`,
-- while the norm formula also requires the valuation of every finite-extension
-- element to be the normalized extension valuation. Add an explicit valuation/norm
-- compatibility hypothesis (or weaken the conclusion to the restriction statement).
theorem chapter01_relative_absolute_value_norm_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (c : ℝ) (hc : 0 < c ∧ c < 1)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hvK : chapter01CompleteAdditiveValuation vK)
    (hvL : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hscale : chapter01ValuationRestrictionScale vK vL e) :
    ∀ y : L,
      chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e y =
        Real.rpow
          (chapter01BaseAbsoluteValue c vK (Algebra.norm K y))
          ((Module.finrank K L : ℝ)⁻¹) := by
  sorry

/-! ### The intrinsic finite-residue-field normalization -/

/-- The residue-cardinality parameter used by canonical local-field norms. -/
noncomputable def chapter01ResidueCardinality
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : ℕ :=
  Nat.card (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField v)

/-- The canonical absolute value `q ^ (-v(x))` attached to a finite residue field. -/
def chapter01CanonicalAbsoluteValue {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (q : ℕ) : K → ℝ :=
  by
    classical
    exact fun x => if x = 0 then 0 else
      Real.rpow (q : ℝ) (-(((v x).untopD 0 : ℤ) : ℝ))

/-- Finite residue extensions have cardinality `q_L = q_K ^ f`. -/
theorem chapter01_residue_cardinality_power
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (f : ℕ)
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)]
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL)]
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree vK vL hext = f) :
    chapter01ResidueCardinality vL = chapter01ResidueCardinality vK ^ f := by
  letI : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
  letI : FiniteDimensional
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_residue_degree_finite
      vK.toValuation vL.toValuation
  change Nat.card
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL) =
    Nat.card
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK) ^ f
  rw [Module.natCard_eq_pow_finrank
    (K := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)
    (V := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL)]
  congr 1

-- SOURCE_ISSUE: Section 1.4 uses `[L : K] = e f` without a defectless
-- hypothesis.  Finite defect extensions over complete discretely valued
-- fields with imperfect residue field can violate that equality.  The
-- corrected declaration below assumes the needed degree equality explicitly.
/-- Canonical norms restrict with the full field degree as exponent. -/
theorem chapter01_canonical_absolute_value_restricts_by_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e f : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e)
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)]
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL)]
    (hcard : chapter01ResidueCardinality vL =
      chapter01ResidueCardinality vK ^ f)
    (hdegree : Module.finrank K L = e * f) :
    ∀ x : K,
      chapter01CanonicalAbsoluteValue vL (chapter01ResidueCardinality vL)
          (algebraMap K L x) =
        (chapter01CanonicalAbsoluteValue vK (chapter01ResidueCardinality vK) x) ^
          Module.finrank K L := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [chapter01CanonicalAbsoluteValue,
      Nat.ne_of_gt (Module.finrank_pos : 0 < Module.finrank K L)]
  · have hmapx : algebraMap K L x ≠ 0 := by
      intro h
      apply hx
      apply FaithfulSMul.algebraMap_injective K L
      simpa using h
    have hvKx : vK x ≠ (⊤ : WithTop ℤ) :=
      (AddValuation.ne_top_iff vK).2 hx
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hvKx
    have hn' : vK x = (n : WithTop ℤ) := hn.symm
    have hvLint : (vL (algebraMap K L x)).untopD 0 = e * n := by
      rw [hscale.2 x hx, hn']
      rw [← WithTop.coe_nsmul (n : ℤ) e]
      rfl
    have hval :
        (((vL (algebraMap K L x)).untopD 0 : ℤ) : ℝ) =
          (e : ℝ) * (n : ℝ) := by
      rw [hvLint]
      push_cast
      rfl
    have hqcard :
        (chapter01ResidueCardinality vL : ℝ) =
          (chapter01ResidueCardinality vK : ℝ) ^ f := by
      exact_mod_cast hcard
    have hqpos : 0 < (chapter01ResidueCardinality vK : ℝ) := by
      exact_mod_cast
        (Nat.card_pos : 0 <
          Nat.card
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK))
    simp only [chapter01CanonicalAbsoluteValue, hmapx, hx, if_false]
    rw [hn', hqcard, hval, hdegree]
    calc
      Real.rpow ((chapter01ResidueCardinality vK : ℝ) ^ f)
          (-((e : ℝ) * (n : ℝ))) =
          Real.rpow (chapter01ResidueCardinality vK : ℝ)
            ((f : ℝ) * (-((e : ℝ) * (n : ℝ)))) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul hqpos.le (f : ℝ) (-((e : ℝ) * (n : ℝ)))).symm
      _ = Real.rpow (chapter01ResidueCardinality vK : ℝ)
            ((-(n : ℝ)) * ((e * f : ℕ) : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = (Real.rpow (chapter01ResidueCardinality vK : ℝ) (-(n : ℝ))) ^ (e * f) := by
        exact Real.rpow_mul_natCast hqpos.le (-(n : ℝ)) (e * f)

-- SOURCE_ISSUE: The final warning in Section 1.4 also relies on the same
-- defectless equality: a nontrivial immediate defect extension can have
-- `e * f = 1`, so its canonical normalization can restrict literally.  The
-- corrected declaration below retains the explicit degree equality.
/-- A nontrivial finite extension cannot have the canonical norm literally restrict. -/
theorem chapter01_canonical_normalization_not_literal_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e f : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e)
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)]
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL)]
    (hcard : chapter01ResidueCardinality vL =
      chapter01ResidueCardinality vK ^ f)
    (hdegree : Module.finrank K L = e * f)
    (hdeg : 1 < Module.finrank K L)
    (hnontrivial : ∃ x : K,
      chapter01CanonicalAbsoluteValue vK (chapter01ResidueCardinality vK) x ≠ 0 ∧
        chapter01CanonicalAbsoluteValue vK (chapter01ResidueCardinality vK) x ≠ 1) :
    ¬ ∀ x : K,
      chapter01CanonicalAbsoluteValue vL (chapter01ResidueCardinality vL)
          (algebraMap K L x) =
        chapter01CanonicalAbsoluteValue vK (chapter01ResidueCardinality vK) x := by
  intro hliteral
  obtain ⟨x, hx0, hx1⟩ := hnontrivial
  let a := chapter01CanonicalAbsoluteValue vK
    (chapter01ResidueCardinality vK) x
  have hx : x ≠ 0 := by
    intro h
    subst x
    simpa [a, chapter01CanonicalAbsoluteValue] using hx0
  have hqpos : 0 < (chapter01ResidueCardinality vK : ℝ) := by
    exact_mod_cast
      (Nat.card_pos : 0 <
        Nat.card
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK))
  have ha_pos : 0 < a := by
    dsimp [a, chapter01CanonicalAbsoluteValue]
    rw [if_neg hx]
    exact Real.rpow_pos_of_pos hqpos _
  have hcanonical :=
    chapter01_canonical_absolute_value_restricts_by_degree
      vK vL e f hscale hcard hdegree
  have hpow : a ^ Module.finrank K L = a := by
    calc
      a ^ Module.finrank K L =
          chapter01CanonicalAbsoluteValue vL (chapter01ResidueCardinality vL)
            (algebraMap K L x) := (hcanonical x).symm
      _ = a := hliteral x
  by_cases halt : a < 1
  · have hlt := pow_lt_self_of_lt_one₀ ha_pos halt hdeg
    exact (ne_of_lt hlt) hpow
  · have hagt : 1 < a := lt_of_le_of_ne (le_of_not_gt halt) hx1.symm
    have hlt : a < a ^ Module.finrank K L := by
      simpa using (pow_lt_pow_right₀ hagt hdeg)
    exact (ne_of_lt hlt) hpow.symm

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
