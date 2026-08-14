import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section07NormsAndIdeals

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

@[simp] theorem chapter01BaseAbsoluteValue_zero {K : Type*} [Field K]
    (c : ℝ) (v : AddValuation K (WithTop ℤ)) :
    chapter01BaseAbsoluteValue c v 0 = 0 := by
  simp [chapter01BaseAbsoluteValue]

@[simp] theorem chapter01BaseAbsoluteValue_one {K : Type*} [Field K]
    (c : ℝ) (v : AddValuation K (WithTop ℤ)) :
    chapter01BaseAbsoluteValue c v 1 = 1 := by
  simp [chapter01BaseAbsoluteValue]

/-- The absolute value `c ^ (v_L(y) / e)` that literally restricts to the base. -/
def chapter01RelativeAbsoluteValue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : ℝ) (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : L → ℝ :=
  by
    classical
    exact fun y => if y = 0 then 0 else
      Real.rpow c ((((vL y).untopD 0 : ℤ) : ℝ) / (e : ℝ))

@[simp] theorem chapter01RelativeAbsoluteValue_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : ℝ) (vL : AddValuation L (WithTop ℤ)) (e : ℕ) :
    chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e 0 = 0 := by
  simp [chapter01RelativeAbsoluteValue]

@[simp] theorem chapter01RelativeAbsoluteValue_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : ℝ) (vL : AddValuation L (WithTop ℤ)) (e : ℕ) :
    chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e 1 = 1 := by
  simp [chapter01RelativeAbsoluteValue]

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
  sorry

/-- Completeness and normalized discreteness for an additive valuation. -/
def chapter01CompleteAdditiveValuation {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v ∧
    IsAdicComplete
      (IsLocalRing.maximalIdeal v.toValuation.valuationSubring)
      v.toValuation.valuationSubring

/-- For a finite complete extension, the relative absolute value is the norm root.

The declaration is formulated for chosen valuations without packaging
henselianity, so uniqueness of the extending valuation is recorded explicitly.
In the book's complete discretely valued setting, that uniqueness follows from
completeness. -/
theorem chapter01_relative_absolute_value_norm_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (c : ℝ) (hc : 0 < c ∧ c < 1)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hvK : chapter01CompleteAdditiveValuation vK)
    (hvL : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hscale : chapter01ValuationRestrictionScale vK vL e)
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w) :
    ∀ y : L,
      chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e y =
        Real.rpow
          (chapter01BaseAbsoluteValue c vK (Algebra.norm K y))
          ((Module.finrank K L : ℝ)⁻¹) := by
  sorry

/-! ### The intrinsic finite-residue-field normalization -/

/-- The residue-cardinality parameter used by canonical local-field norms. -/
noncomputable def chapter01ResidueCardinality
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    [Finite (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField v)] : ℕ :=
  Nat.card (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField v)

/-- The canonical absolute value `q ^ (-v(x))` attached to a finite residue field. -/
def chapter01CanonicalAbsoluteValue {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (q : ℕ) : K → ℝ :=
  by
    classical
    exact fun x => if x = 0 then 0 else
      Real.rpow (q : ℝ) (-(((v x).untopD 0 : ℤ) : ℝ))

@[simp] theorem chapter01CanonicalAbsoluteValue_zero {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (q : ℕ) :
    chapter01CanonicalAbsoluteValue v q 0 = 0 := by
  simp [chapter01CanonicalAbsoluteValue]

@[simp] theorem chapter01CanonicalAbsoluteValue_one {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (q : ℕ) :
    chapter01CanonicalAbsoluteValue v q 1 = 1 := by
  simp [chapter01CanonicalAbsoluteValue]

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
  sorry

/-- Canonical norms restrict with the full field degree as exponent.

This generic interface does not assume completeness, so it takes the degree
identity as explicit data.  For the complete discrete extensions treated in
the book, finite freeness of the valuation ring gives `[L : K] = e f`. -/
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
  sorry

/-- A nontrivial finite extension cannot have the canonical norm literally restrict.

As above, the declaration retains the degree identity explicitly because its
valuation interface is more general than the complete discrete setting in
which that identity is automatic. -/
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
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
