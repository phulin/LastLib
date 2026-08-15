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
    (c : ℝ) (_hc : 0 < c ∧ c < 1)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e) :
    ∀ x : K,
      chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e
          (algebraMap K L x) =
        chapter01BaseAbsoluteValue c vK x := by
  rcases hscale with ⟨he, hscale⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hax : algebraMap K L x ≠ 0 :=
      (map_ne_zero_iff (algebraMap K L) (FaithfulSMul.algebraMap_injective K L)).2 hx
    simp only [chapter01RelativeAbsoluteValue, chapter01BaseAbsoluteValue,
      if_neg hax, if_neg hx]
    have hvK : vK x ≠ ⊤ := (vK.ne_top_iff).2 hx
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hvK
    have hv := hscale x hx
    rw [← hz] at hv
    have hnsmul : ∀ n : ℕ, n • (z : WithTop ℤ) = (n * z : ℤ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul, ih]
          norm_cast
          simp only [Nat.cast_add, Nat.cast_one]
          ring
    have hv' : vL (algebraMap K L x) = (e * z : ℤ) := by
      simpa [hnsmul] using hv
    rw [hv']
    rw [← hz]
    simp only [WithTop.untopD_coe, Int.cast_mul]
    congr 1
    field_simp
    exact mul_comm _ _

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
The defectless degree identity is also explicit, so the norm interface does not
silently use a fundamental-equality theorem from a later layer. In the book's
complete discretely valued setting, both facts follow from completeness. -/
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
    (hdegree : Module.finrank K L =
      e * LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hext)
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w) :
    ∀ y : L,
      chapter01RelativeAbsoluteValue (K := K) (L := L) c vL e y =
        Real.rpow
          (chapter01BaseAbsoluteValue c vK (Algebra.norm K y))
          ((Module.finrank K L : ℝ)⁻¹) := by
  intro y
  by_cases hy : y = 0
  · subst y
    have hdim : 0 < Module.finrank K L := Module.finrank_pos
    have hdim' : (Module.finrank K L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hdim)
    have hdim_inv : (Module.finrank K L : ℝ)⁻¹ ≠ 0 := inv_ne_zero hdim'
    simp [chapter01RelativeAbsoluteValue, chapter01BaseAbsoluteValue,
      Real.zero_rpow hdim_inv]
  · have hnorm_ne : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
    rcases hvK.1 with ⟨_, _, _, hvKdisc⟩
    rcases hvL with ⟨_, _, _, hvLdisc⟩
    obtain ⟨zK, hzK⟩ := hvKdisc (Algebra.norm K y) hnorm_ne
    obtain ⟨zL, hzL⟩ := hvLdisc y hy
    have hzK' : (zK : WithTop ℤ) = vK (Algebra.norm K y) := hzK.symm
    have hzL' : (zL : WithTop ℤ) = vL y := hzL.symm
    let f := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
      vK vL hext
    have hrestrict : ∀ x : K,
        vL (algebraMap K L x) = (e : WithTop ℤ) * vK x := by
      intro x
      by_cases hx : x = 0
      · subst x
        simpa using
          (WithTop.mul_top
            (show (e : WithTop ℤ) ≠ 0 by exact_mod_cast hscale.1.ne')).symm
      · obtain ⟨z, hz⟩ := hvKdisc x hx
        calc
          vL (algebraMap K L x) = e • vK x := hscale.2 x hx
          _ = e • (z : WithTop ℤ) := by rw [hz]
          _ = (e : WithTop ℤ) * (z : WithTop ℤ) := by
            change ((e : ℤ) * z : WithTop ℤ) =
              (e : WithTop ℤ) * (z : WithTop ℤ)
            rw [← WithTop.coe_mul]
            norm_num
          _ = (e : WithTop ℤ) * vK x := by rw [hz]
    have hdegree' : Module.finrank K L = e * f := by
      simpa [f] using hdegree
    have hnorm :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_single_branch_norm_valuation_formula
        K L e f hext hrestrict rfl hunique hdegree' y hy
    simp only [chapter01RelativeAbsoluteValue, chapter01BaseAbsoluteValue,
      if_neg hy, if_neg hnorm_ne]
    have hnorm' : (zK : WithTop ℤ) =
        (f : WithTop ℤ) * (zL : WithTop ℤ) := by
      calc
        (zK : WithTop ℤ) = vK (Algebra.norm K y) := hzK'
        _ = (f : WithTop ℤ) * vL y := hnorm
        _ = (f : WithTop ℤ) * (zL : WithTop ℤ) := by rw [hzL']
    have hnorm_int : zK = (f : ℤ) * zL := by
      exact_mod_cast hnorm'
    rw [← hzL', ← hzK']
    simp only [WithTop.untopD_coe]
    rw [hnorm_int]
    have hdegree_real : (Module.finrank K L : ℝ) = (e : ℝ) * (f : ℝ) := by
      exact_mod_cast hdegree'
    rw [hdegree_real]
    simp only [Int.cast_mul]
    have hfne : f ≠ 0 := by
      intro hf
      have hzero : Module.finrank K L = 0 := by
        calc
          Module.finrank K L = e * f := hdegree'
          _ = 0 := by simp [hf]
      exact (Nat.ne_of_gt (Module.finrank_pos)) hzero
    calc
      c.rpow (↑zL / ↑e) =
          c.rpow ((↑↑f * ↑zL) * ((↑e * ↑f)⁻¹)) := by
        congr 1
        field_simp [show (e : ℝ) ≠ 0 by exact_mod_cast hscale.1.ne',
          show (f : ℝ) ≠ 0 by exact_mod_cast hfne]
      _ = (c.rpow (↑↑f * ↑zL)).rpow ((↑e * ↑f)⁻¹) := by
        exact Real.rpow_mul (le_of_lt hc.1) _ _

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
  let _ : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
  have hcard :=
    Module.natCard_eq_pow_finrank
      (K := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)
      (V := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL)
  have hf' :
      Module.finrank
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL) = f := by
    simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree] using hf
  rw [hf'] at hcard
  simpa [chapter01ResidueCardinality] using hcard

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
  intro x
  by_cases hx : x = 0
  · subst x
    have hdim : 0 < Module.finrank K L := Module.finrank_pos
    simpa using (zero_pow (Nat.ne_of_gt hdim)).symm
  · have hax : algebraMap K L x ≠ 0 :=
      (map_ne_zero_iff (algebraMap K L) (FaithfulSMul.algebraMap_injective K L)).2 hx
    have hvK : vK x ≠ ⊤ := (vK.ne_top_iff).2 hx
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hvK
    have hv := hscale.2 x hx
    rw [← hz] at hv
    have hnsmul : ∀ n : ℕ, n • (z : WithTop ℤ) = (n * z : ℤ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul, ih]
          norm_cast
          simp only [Nat.cast_add, Nat.cast_one]
          ring
    have hv' : vL (algebraMap K L x) = (e * z : ℤ) := by
      simpa [hnsmul] using hv
    simp only [chapter01CanonicalAbsoluteValue, if_neg hax, if_neg hx]
    rw [hcard, hv', ← hz, hdegree]
    simp only [WithTop.untopD_coe]
    rw [Nat.cast_pow]
    have hq : 0 ≤ (chapter01ResidueCardinality vK : ℝ) := Nat.cast_nonneg _
    have hcast : ((↑e * z : ℤ) : ℝ) = (e : ℝ) * (z : ℝ) := by
      norm_num [Int.cast_mul]
    have hdegcast : ((e * f : ℕ) : ℝ) = (e : ℝ) * (f : ℝ) := by
      norm_num
    rw [hcast]
    calc
      ((chapter01ResidueCardinality vK : ℝ) ^ f).rpow
          (-((e : ℝ) * (z : ℝ))) =
          (((chapter01ResidueCardinality vK : ℝ).rpow (f : ℝ))).rpow
            (-((e : ℝ) * (z : ℝ))) := by
              congr 1
              exact (Real.rpow_natCast _ _).symm
      _ = (chapter01ResidueCardinality vK : ℝ).rpow
            ((f : ℝ) * (-((e : ℝ) * (z : ℝ)))) := by
              exact (Real.rpow_mul hq _ _).symm
      _ = (chapter01ResidueCardinality vK : ℝ).rpow
            ((-((z : ℝ))) * ((e : ℝ) * (f : ℝ))) := by
              congr 1
              ring
      _ = (((chapter01ResidueCardinality vK : ℝ).rpow (-((z : ℝ))))).rpow
            ((e : ℝ) * (f : ℝ)) := by
              exact Real.rpow_mul hq _ _
      _ = (((chapter01ResidueCardinality vK : ℝ).rpow (-((z : ℝ)))).rpow
            ((e * f : ℕ) : ℝ)) := by
              rw [hdegcast]
      _ = (chapter01ResidueCardinality vK : ℝ).rpow (-((z : ℝ))) ^ (e * f) := by
              exact Real.rpow_natCast _ _

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
  intro hrestrict
  obtain ⟨x, hx0, hx1⟩ := hnontrivial
  let a : ℝ :=
    chapter01CanonicalAbsoluteValue vK (chapter01ResidueCardinality vK) x
  have ha0 : a ≠ 0 := by
    simpa [a] using hx0
  have ha1 : a ≠ 1 := by
    simpa [a] using hx1
  have ha_nonneg : 0 ≤ a := by
    dsimp [a, chapter01CanonicalAbsoluteValue]
    split
    · simp
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hformula :=
    chapter01_canonical_absolute_value_restricts_by_degree
      (K := K) (L := L) vK vL e f hscale hcard hdegree x
  have hpow : a ^ Module.finrank K L = a := by
    calc
      a ^ Module.finrank K L =
          chapter01CanonicalAbsoluteValue vL (chapter01ResidueCardinality vL)
            (algebraMap K L x) := by
              simpa [a] using hformula.symm
      _ = a := by
        simpa [a] using hrestrict x
  have hpow_sub : a ^ (Module.finrank K L - 1) = 1 := by
    apply (mul_right_cancel₀ ha0)
    calc
      a ^ (Module.finrank K L - 1) * a =
          a ^ ((Module.finrank K L - 1) + 1) := by rw [pow_succ]
      _ = a ^ Module.finrank K L := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega))]
      _ = a := hpow
      _ = 1 * a := by simp
  have hsub_ne : Module.finrank K L - 1 ≠ 0 := by omega
  have : a = 1 :=
    (pow_eq_one_iff_of_nonneg ha_nonneg hsub_ne).mp hpow_sub
  exact ha1 this

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
