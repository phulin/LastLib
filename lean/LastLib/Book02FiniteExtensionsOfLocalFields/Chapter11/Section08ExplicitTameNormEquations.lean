import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section07ExplicitUnramifiedNormEquations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open scoped Polynomial

/-! ## 11.8. Explicit norm equations in a tame totally ramified extension

The valuation coordinate is separated from the residue-unit coordinate.  The
resulting set is the elementary tame norm-equation obstruction; the stronger
principal-unit hypotheses are kept visible in the theorem that identifies it
with the actual norm image.
-/

/- The unit factor contributed by a chosen uniformizer.  The quotient is the
   source's `c = N(π_L) / π_K`; the equation API below keeps it explicit. -/
def chapter11TameNormUniformizerFactor
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (πK : K) (πL : L) : K :=
  Algebra.norm K πL / πK

theorem chapter11_tame_norm_uniformizer_factor_spec
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (πK : K) (πL : L) (hπK : πK ≠ 0) :
    chapter11TameNormUniformizerFactor K L πK πL * πK = Algebra.norm K πL := by
  unfold chapter11TameNormUniformizerFactor
  field_simp [hπK]

/- The full set of tame norm-equation candidates: powers of a chosen
   uniformizer times a unit whose residue, after correcting by `c⁻ʳ`, is an
   `e`th power. -/
def chapter11TameNormEquationSet
    {K k : Type*} [Field K] [Field k]
    (vK : AddValuation K (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k) (πK c : K) (e : ℕ) : Set K :=
  {a | ∃ r : ℤ, ∃ u : K,
    u ∈ chapter11UnitFiltration vK 0 ∧
      u * c ^ (-r) ∈ chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitPowerImage k e) ∧
      a = πK ^ r * u}

/- The norm image of units already lying in the base field. -/
def chapter11BaseUnitNormImage
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (e : ℕ) : Set K :=
  Set.range (fun u : (chapter11ValuationRing vK)ˣ =>
    ((u : chapter11ValuationRing vK) : K) ^ e)

theorem chapter11_mem_base_unit_norm_image_iff
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (e : ℕ) (x : K) :
    x ∈ chapter11BaseUnitNormImage K vK e ↔
      ∃ u : (chapter11ValuationRing vK)ˣ,
        ((u : chapter11ValuationRing vK) : K) ^ e = x := Iff.rfl

/- The elementary valuation coordinate in tame total ramification is
   surjective, although a particular target unit may still have a residue
   obstruction.  The displayed norm-value hypothesis is the missing bridge
   from a chosen uniformizer to the valuation formula. -/
-- SOURCE_ISSUE: The source suppresses the norm-valuation compatibility of a
-- chosen extension uniformizer.  It is stated explicitly here because the
-- valuation branch interface alone does not determine the norm of `πL`.
theorem chapter11_tame_total_norm_valuation_coordinate_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πL : L) (hπ : chapter11IsUniformizer vL πL)
    (hnormπ : vK (Algebra.norm K πL) = (1 : WithTop ℤ)) (r : ℤ) :
    ∃ x : L, x ≠ 0 ∧ vK (Algebra.norm K x) = (r : WithTop ℤ) := by
  have hnormπ0 : Algebra.norm K πL ≠ 0 := by
    intro hzero
    rw [hzero] at hnormπ
    simp at hnormπ
  refine ⟨πL ^ r, zpow_ne_zero r hπ.1, ?_⟩
  rw [Algebra.norm_zpow]
  have hpow (m : ℤ) : vK (Algebra.norm K πL ^ m) = (m : WithTop ℤ) := by
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih =>
        rw [zpow_add_one₀ hnormπ0, AddValuation.map_mul, ih, hnormπ]
        simp
    | pred m ih =>
        rw [zpow_sub_one₀ hnormπ0, AddValuation.map_mul, ih,
          AddValuation.map_inv, hnormπ]
        norm_cast
  exact hpow r

/- In the tame totally ramified situation, the valuation and residue-unit
   conditions together characterize the nonzero norm equations. -/
theorem chapter11_tame_total_norm_equation_iff
    (K L k : Type*) [Field K] [Field L] [Field k] [Fintype k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (he : 0 < e) (htame : chapter11TameAtResidueCharacteristic e p)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1))
    (hdegree : Module.finrank K L = e)
    (_hfres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hext = 1)
    (πK : K) (hπK : chapter11IsUniformizer vK πK)
    (πL : L) (hπL : chapter11IsUniformizer vL πL)
    (c : K) (hc : c ∈ chapter11UnitFiltration vK 0)
    (_hcdef : c = chapter11TameNormUniformizerFactor K L πK πL)
    (hnormπ : Algebra.norm K πL = c * πK)
    (a : K) (_ha : a ≠ 0) :
    chapter11NormEquationSolution K L a ↔
      a ∈ chapter11TameNormEquationSet vK ρK πK c e := by
  have hcunit : c ∈ chapter11UnitSet vK := by
    rw [← chapter11_unit_filtration_zero vK]
    exact hc
  have hcval : vK c = 0 :=
    (chapter11_mem_unit_set_iff_valuation_zero vK c).mp hcunit
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero] at hcval
    simp at hcval
  have hpow_zero (b : K) (hb : b ≠ 0) (hbval : vK b = 0) (m : ℤ) :
      vK (b ^ m) = 0 := by
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih =>
        rw [zpow_add_one₀ hb, AddValuation.map_mul, ih, hbval]
        simp
    | pred m ih =>
        rw [zpow_sub_one₀ hb, AddValuation.map_mul, ih,
          AddValuation.map_inv, hbval]
        simp
  have hmul_zpow (m : ℤ) : (c * πK) ^ m = c ^ m * πK ^ m := by
    have hcπ0 : c * πK ≠ 0 := mul_ne_zero hc0 hπK.1
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih =>
        rw [zpow_add_one₀ hcπ0, zpow_add_one₀ hc0, zpow_add_one₀ hπK.1, ih]
        ring
    | pred m ih =>
        rw [zpow_sub_one₀ hcπ0, zpow_sub_one₀ hc0, zpow_sub_one₀ hπK.1, ih]
        ring
  have hall :
      chapter11NormImage K L vL 0 =
        chapter11ResidueConditionSet vK ρK
          (chapter11ResidueUnitPowerImage k e) :=
    proposition_11_2_tame_totally_ramified_all_unit_norm_image K L k vK vL ρK ρL e p he
      htame hext hscale hres hdegree hred hcompleteK hcompleteL N hnormunit hnormred hprincipal
  constructor
  · intro hsolution
    rcases hsolution with ⟨x, hx, hxnorm⟩
    have hdiv : chapter11ValuationValueDivisibleBy vL 1 x := by
      unfold chapter11ValuationValueDivisibleBy
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp (vL.ne_top_iff.mpr hx)
      refine ⟨z, ?_⟩
      simpa using hz.symm
    obtain ⟨r, w, hw, hxrep⟩ :=
      chapter11_unramified_norm_equation_decomposition L vL 1 πL hπL x hx hdiv
    have hwunit : w ∈ chapter11UnitSet vL := by
      rw [← chapter11_unit_filtration_zero vL]
      exact hw
    rcases hwunit with ⟨uw, hwu⟩
    have hnormwunit : Algebra.norm K w ∈ chapter11UnitSet vK := by
      let uw' : (chapter11ValuationRing vL)ˣ :=
        vL.toValuation.valuationSubring.unitGroupMulEquiv uw
      refine ⟨vK.toValuation.valuationSubring.unitGroupMulEquiv.symm (N uw'), ?_⟩
      change Algebra.norm K w = ((N uw' : chapter11ValuationRing vK) : K)
      rw [hnormunit uw', hwu]
      rfl
    have hnormwval : vK (Algebra.norm K w) = 0 :=
      (chapter11_mem_unit_set_iff_valuation_zero vK _).mp hnormwunit
    have hnormwres :
        Algebra.norm K w ∈
          chapter11ResidueConditionSet vK ρK
            (chapter11ResidueUnitPowerImage k e) := by
      have hnormwimage : Algebra.norm K w ∈ chapter11NormImage K L vL 0 :=
        ⟨w, hw, rfl⟩
      rw [hall] at hnormwimage
      exact hnormwimage
    have hcancel :
        (c ^ r * Algebra.norm K w) * c ^ (-r) = Algebra.norm K w := by
      calc
        (c ^ r * Algebra.norm K w) * c ^ (-r) =
            Algebra.norm K w * (c ^ r * c ^ (-r)) := by ring
        _ = Algebra.norm K w * c ^ (r + (-r)) := by
          rw [← zpow_add₀ hc0]
        _ = Algebra.norm K w := by simp
    refine ⟨r, c ^ r * Algebra.norm K w, ?_, ?_, ?_⟩
    · rw [chapter11_unit_filtration_zero]
      apply (chapter11_mem_unit_set_iff_valuation_zero vK _).2
      rw [AddValuation.map_mul, hpow_zero c hc0 hcval r, hnormwval]
      simp
    · rw [hcancel]
      exact hnormwres
    · have hxrep' : x = πL ^ r * w := by
        simpa using hxrep
      calc
        a = Algebra.norm K x := hxnorm.symm
        _ = Algebra.norm K (πL ^ r * w) := by rw [hxrep']
        _ = Algebra.norm K (πL ^ r) * Algebra.norm K w := by
          rw [(Algebra.norm K).map_mul]
        _ = (c * πK) ^ r * Algebra.norm K w := by
          rw [Algebra.norm_zpow, hnormπ]
        _ = πK ^ r * (c ^ r * Algebra.norm K w) := by
          rw [hmul_zpow]
          ring
  · intro hcandidate
    rcases hcandidate with ⟨r, u, hu, hresidue, haeq⟩
    rw [← hall] at hresidue
    rcases hresidue with ⟨y, hy, hnormy⟩
    have hyunit : y ∈ chapter11UnitSet vL := by
      rw [← chapter11_unit_filtration_zero vL]
      exact hy
    have hy0 : y ≠ 0 := by
      intro hyzero
      rw [hyzero] at hyunit
      have hyval := (chapter11_mem_unit_set_iff_valuation_zero vL 0).mp hyunit
      simp at hyval
    unfold chapter11NormEquationSolution
    refine ⟨πL ^ r * y, mul_ne_zero (zpow_ne_zero r hπL.1) hy0, ?_⟩
    have hnormpow : Algebra.norm K (πL ^ r) = (c * πK) ^ r := by
      rw [Algebra.norm_zpow, hnormπ]
    calc
      Algebra.norm K (πL ^ r * y) =
          Algebra.norm K (πL ^ r) * Algebra.norm K y := by
        rw [(Algebra.norm K).map_mul]
      _ = (c * πK) ^ r * (u * c ^ (-r)) := by
        rw [hnormpow, hnormy]
      _ = πK ^ r * u := by
        rw [hmul_zpow]
        calc
          c ^ r * πK ^ r * (u * c ^ (-r)) =
              πK ^ r * u * (c ^ r * c ^ (-r)) := by ring
          _ = πK ^ r * u * c ^ (r + (-r)) := by
            rw [← zpow_add₀ hc0]
          _ = πK ^ r * u := by simp
      _ = a := haeq.symm

/- A Kummer polynomial records the example in which a totally ramified
   uniformizer is an `e`th root of the base uniformizer. -/
def chapter11KummerPolynomial {K : Type*} [Field K] (π : K) (e : ℕ) : K[X] :=
  Polynomial.X ^ e - Polynomial.C π

/- All `e`th roots of unity in a chosen algebraic closure already come from
   the base field; this is the formal version of `μ_e ⊂ K`. -/
def chapter11ContainsEThRootsOfUnity
    (K E : Type*) [Field K] [Field E] [Algebra K E] (e : ℕ) : Prop :=
  ∀ ζ : E, ζ ^ e = 1 → ∃ z : K, algebraMap K E z = ζ

/- The constant coefficient of the Kummer polynomial gives the norm sign. -/
theorem chapter11_kummer_uniformizer_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (π : K) (root : L) (e : ℕ)
    (hminpoly : minpoly K root = chapter11KummerPolynomial π e)
    (hgenerates : Algebra.adjoin K ({root} : Set L) = ⊤)
    (hdegree : Module.finrank K L = e) :
    Algebra.norm K root = (-1 : K) ^ (e + 1) * π := by
  have hxint : IsIntegral K root := IsIntegral.of_finite K root
  have he : 0 < e := by
    rw [← hdegree]
    exact Module.finrank_pos
  have he0 : 0 ≠ e := (Nat.ne_of_gt he).symm
  have hgenIF : IntermediateField.adjoin K ({root} : Set L) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra (F := K) (S := ({root} : Set L)) hgenerates
  have hfinrank : Module.finrank (IntermediateField.adjoin K ({root} : Set L)) L = 1 := by
    rw [hgenIF]
    simp
  have hdegpoly : (minpoly K root).natDegree = e := by
    calc
      (minpoly K root).natDegree =
          Module.finrank K (IntermediateField.adjoin K ({root} : Set L)) :=
        (IntermediateField.adjoin.finrank hxint).symm
      _ = Module.finrank K L := by
        have htower :=
          Module.finrank_mul_finrank K (IntermediateField.adjoin K ({root} : Set L)) L
        rw [hfinrank, mul_one] at htower
        exact htower
      _ = e := hdegree
  have hnormeq :
      Algebra.norm K root = Algebra.norm K (IntermediateField.AdjoinSimple.gen K root) := by
    rw [Algebra.norm_eq_norm_adjoin K root, hfinrank, pow_one]
  have hpb :=
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hxint)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at hpb
  have hpb' :
      Algebra.norm K (IntermediateField.AdjoinSimple.gen K root) =
        (-1) ^ (minpoly K root).natDegree * (minpoly K root).coeff 0 := by
    exact hpb
  calc
    Algebra.norm K root = Algebra.norm K (IntermediateField.AdjoinSimple.gen K root) := hnormeq
    _ = (-1) ^ (e + 1) * π := by
      rw [hpb', hdegpoly, hminpoly, chapter11KummerPolynomial]
      simp [he0, pow_succ]

/- Norms of elements embedded from the base field are powers by the extension
   degree. -/
theorem chapter11_norm_of_base_unit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (e : ℕ)
    (hdegree : Module.finrank K L = e) (u : K) :
    Algebra.norm K (algebraMap K L u) = u ^ e := by
  rw [Algebra.norm_algebraMap, hdegree]

/- The base-unit formula gives an inclusion in the full unit norm image; it
   does not identify that image with the base-field power image.  The source
   units are restricted to the valuation-ring unit group so the target really
   is a zeroth unit layer. -/
theorem chapter11_base_unit_norm_image_subset
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (hscale : chapter11ValuationScaling vK vL e)
    (hdegree : Module.finrank K L = e) :
    chapter11BaseUnitNormImage K vK e ⊆ chapter11NormImage K L vL 0 := by
  intro x hx
  rcases hx with ⟨u, rfl⟩
  rw [chapter11_mem_norm_image_iff]
  refine ⟨algebraMap K L ((u : chapter11ValuationRing vK) : K), ?_, ?_⟩
  · rw [chapter11_unit_filtration_zero]
    apply (chapter11_mem_unit_set_iff_valuation_zero vL _).2
    rw [hscale, (chapter11_mem_unit_set_iff_valuation_zero vK _).mp]
    · simp
    · refine ⟨vK.toValuation.valuationSubring.unitGroupMulEquiv.symm u, ?_⟩
      rfl
  · exact chapter11_norm_of_base_unit K L e hdegree
      ((u : chapter11ValuationRing vK) : K)

/- The finite-residue tame quotient is the residue-unit obstruction, with no
   additional valuation index because a norm of a uniformizer has valuation
   one. -/
theorem chapter11_tame_total_norm_unit_quotient_index
    (k : Type*) [Field k] [Fintype k] (e : ℕ) :
    Nat.card (kˣ ⧸ chapter11PowerSubgroup k e) =
      Nat.gcd e (Fintype.card k - 1) := by
  exact chapter11_tame_residue_power_quotient_index k e

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
