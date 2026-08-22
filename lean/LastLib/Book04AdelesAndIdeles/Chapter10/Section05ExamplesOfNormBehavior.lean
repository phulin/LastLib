import LastLib.Book04AdelesAndIdeles.Chapter10.Section04LocalConditionsVersusGlobalNorm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators

/-! ## 10.5. Examples of norm behavior -/

theorem chapter10_complex_real_norm_formula (z : ℂ) :
    Algebra.norm ℝ z = Complex.normSq z := by
  exact Algebra.norm_complex_apply z

theorem chapter10_complex_real_norm_formula_expanded (z : ℂ) :
    Algebra.norm ℝ z = z.re ^ 2 + z.im ^ 2 := by
  simp [Algebra.norm_complex_apply, Complex.normSq_apply, pow_two]

theorem chapter10_complex_real_norm_positive (z : ℂ) (hz : z ≠ 0) :
    0 < Algebra.norm ℝ z := by
  rw [Algebra.norm_complex_apply, Complex.normSq_pos]
  exact hz

theorem chapter10_negative_real_not_a_complex_norm (r : ℝ) (hr : r < 0) :
    ¬ ∃ z : ℂ, Algebra.norm ℝ z = r := by
  exact by
    rintro ⟨z, hz⟩
    rw [Algebra.norm_complex_apply] at hz
    exact (not_lt_of_ge (Complex.normSq_nonneg z)) (hz ▸ hr)

/-- A complexified real place is represented by a map into the complex local
factor together with the local determinant compatibility. -/
theorem chapter10_global_norm_positive_at_a_complexified_real_place
    {G : Type*} [CommGroup G]
    (place : G →* ℂˣ) (placeNorm : ℂˣ →* ℝˣ)
    (hcompat : placeNorm.comp place =
      (chapter10LocalNormUnitHom ℝ ℂ).comp place) (a : G) :
    0 < (placeNorm (place a) : ℝ) := by
  have hnorm : (placeNorm (place a) : ℝ) = Algebra.norm ℝ (place a : ℂ) := by
    have h := congrArg (fun u : ℝˣ => (u : ℝ)) (DFunLike.congr_fun hcompat a)
    simpa [MonoidHom.comp_apply, chapter10LocalNormUnitHom, chapter10LocalNorm, Units.map] using h
  rw [hnorm]
  exact chapter10_complex_real_norm_positive (place a : ℂ) (Units.ne_zero (place a))

/-! ### Unramified and totally ramified local obstructions -/

/-- The full multiplicative norm subgroup of `Fˣ`.  For a field, `Fˣ` is
the group of all nonzero elements, so this records the valuation obstruction
as well as the unit obstruction. -/
def chapter10NormSubgroup
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Subgroup Fˣ :=
  Subgroup.map (chapter10LocalNormUnitHom F E) ⊤

abbrev chapter10FullNormQuotient
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Type _ :=
  Fˣ ⧸ chapter10NormSubgroup F E

private theorem chapter10_uniformizer_value_unit_decomposition
    (F : Type*) [Field F]
    (vF : AddValuation F (WithTop ℤ)) (πF : F)
    (hπF : chapter10NormalizedUniformizer vF πF) (a : F) (ha : a ≠ 0) :
    ∃ r : ℤ, ∃ u : F, u ∈ chapter10LocalUnitSet vF ∧
      a = πF ^ r * u := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (vF.ne_top_iff.mpr ha)
  have hpow : ∀ m : ℤ, vF (πF ^ m) = (m : WithTop ℤ) := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih =>
        rw [zpow_add_one₀ hπF.1, AddValuation.map_mul, ih,
          chapter10_normalized_uniformizer_value vF πF hπF]
        simp
    | pred m ih =>
        rw [zpow_sub_one₀ hπF.1, AddValuation.map_mul, ih,
          AddValuation.map_inv, chapter10_normalized_uniformizer_value vF πF hπF]
        norm_cast
  refine ⟨r, a / πF ^ r, ?_, ?_⟩
  · apply (chapter10_mem_local_unit_set_iff vF _).2
    rw [AddValuation.map_div, ← hr, hpow]
    simp [WithTop.coe_ne_top]
  · field_simp [hπF.1]

theorem chapter10_unramified_full_norm_quotient_cyclic_of_order
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (d : ℕ) (hunram : chapter10UnramifiedLocalExtension vF vE)
    (hdegree : Module.finrank F E = d) (πF : F)
    (hπF : chapter10NormalizedUniformizer vF πF)
    (hnorm : chapter10NormValuationFormula F E vF vE d)
    (hfres : d =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vF vE hunram.1)
    [Finite (chapter10ResidueField vF)]
    [Algebra (chapter10ResidueField vF) (chapter10ResidueField vE)]
    [FiniteDimensional (chapter10ResidueField vF) (chapter10ResidueField vE)]
    [Algebra.IsSeparable (chapter10ResidueField vF) (chapter10ResidueField vE)]
    (hred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
        vF vE (chapter10ResidueMap vF) (chapter10ResidueMap vE))
    (N : (chapter10ValuationRing vE)ˣ →* (chapter10ValuationRing vF)ˣ)
    (hnormunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormUnitLiftCompatibility
        F E vF vE N)
    (hnormred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormResidueCompatibility
        F E (chapter10ResidueField vF) (chapter10ResidueField vE) vF vE
          (chapter10ResidueMap vF) (chapter10ResidueMap vE) 1 N) :
    IsCyclic (chapter10FullNormQuotient F E) ∧
      Nat.card (chapter10FullNormQuotient F E) = d := by
  have hunit_eq :=
    (lemma_10_1_norms_in_an_unramified_extension F E vF vE d hunram hdegree πF hπF
      hnorm hfres hred N hnormunit hnormred).1
  let πunit : Fˣ := Units.mk0 πF hπF.1
  have hunit_norm : ∀ u : Fˣ, (u : F) ∈ chapter10LocalUnitSet vF →
      u ∈ chapter10NormSubgroup F E := by
    intro u hu
    have hu' : (u : F) ∈ chapter10ValuationUnitNormImage F E vE := by
      rw [hunit_eq]
      exact hu
    rcases hu' with ⟨y, hy, hyu⟩
    have hy0 : y ≠ 0 := by
      intro hy0
      subst y
      have hyval := (chapter10_mem_local_unit_set_iff vE (0 : E)).mp hy
      simp at hyval
    let yu : Eˣ := Units.mk0 y hy0
    have hyu' : chapter10LocalNormUnitHom F E yu = u := by
      apply Units.ext
      change chapter10LocalNorm F E y = (u : F)
      exact hyu
    apply (Subgroup.mem_map).2
    exact ⟨yu, trivial, hyu'⟩
  have hdecomp : ∀ x : Fˣ, ∃ r : ℤ, ∃ u : F,
      u ∈ chapter10LocalUnitSet vF ∧ (x : F) = πF ^ r * u := by
    intro x
    exact chapter10_uniformizer_value_unit_decomposition F vF πF hπF (x : F) x.ne_zero
  let g : Multiplicative ℤ →* chapter10FullNormQuotient F E :=
    { toFun := fun z => QuotientGroup.mk' (chapter10NormSubgroup F E) (πunit ^ z.toAdd)
      map_one' := by simp
      map_mul' := by
        intro x y
        change QuotientGroup.mk' (chapter10NormSubgroup F E)
            (πunit ^ (x.toAdd + y.toAdd)) =
          QuotientGroup.mk' (chapter10NormSubgroup F E) (πunit ^ x.toAdd) *
            QuotientGroup.mk' (chapter10NormSubgroup F E) (πunit ^ y.toAdd)
        rw [zpow_add πunit, ← map_mul] }
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (chapter10NormSubgroup F E) q
    rcases hdecomp x with ⟨r, u, hu, hxu⟩
    have hu0 : u ≠ 0 := by
      intro hu0
      rw [hu0] at hxu
      simp at hxu
    let uu : Fˣ := Units.mk0 u hu0
    have hxu' : x = πunit ^ r * uu := by
      apply Units.ext
      simpa [πunit, uu, Units.val_zpow_eq_zpow_val] using hxu
    have huu : uu ∈ chapter10NormSubgroup F E := hunit_norm uu hu
    have hmk_uu : QuotientGroup.mk' (chapter10NormSubgroup F E) uu = 1 :=
      (QuotientGroup.eq_one_iff uu).2 huu
    refine ⟨Multiplicative.ofAdd r, ?_⟩
    change QuotientGroup.mk' (chapter10NormSubgroup F E) (πunit ^ r) =
      QuotientGroup.mk' (chapter10NormSubgroup F E) x
    rw [hxu', map_mul, hmk_uu]
    exact (mul_one (QuotientGroup.mk' (chapter10NormSubgroup F E) (πunit ^ r))).symm
  have hcyc : IsCyclic (chapter10FullNormQuotient F E) := isCyclic_of_surjective g hg
  have hcard0 :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_norm_subgroup_index
      F E vF vE πF d hunram hπF hnorm hdegree hfres hred N hnormunit hnormred
  have hcard : Nat.card (chapter10FullNormQuotient F E) = d := by
    simpa [chapter10FullNormQuotient, chapter10NormSubgroup,
      chapter10LocalNormUnitHom, chapter10LocalNorm,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormSubgroup] using hcard0
  exact ⟨hcyc, hcard⟩

def chapter10NormValuationImage
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (vF : AddValuation F (WithTop ℤ)) : Set ℤ :=
  {z | ∃ y : E, y ≠ 0 ∧ vF (chapter10LocalNorm F E y) = z}

theorem chapter10_totally_ramified_norm_valuation_unrestricted
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (hformula : chapter10NormValuationFormula F E vF vE 1)
    (πE : E) (hπE : chapter10NormalizedUniformizer vE πE) :
    chapter10NormValuationImage F E vF = Set.univ := by
  ext z
  constructor
  · intro hz
    exact Set.mem_univ z
  · intro _
    have hone : ∀ n : ℕ, n • (1 : WithTop ℤ) = (n : WithTop ℤ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul, Nat.cast_succ, ih]
    have hnegcast : ∀ n : ℕ,
        (Int.negSucc n : WithTop ℤ) = -((n + 1 : ℕ) : WithTop ℤ) := by
      intro n
      simp [Int.negSucc_eq]
    have hpow : ∀ n : ℤ, vE (πE ^ n) = (n : WithTop ℤ) := by
      intro n
      cases n with
      | ofNat n =>
          change vE (πE ^ (n : ℤ)) = (n : WithTop ℤ)
          rw [zpow_natCast, vE.map_pow, chapter10_normalized_uniformizer_value vE πE hπE,
            hone]
      | negSucc n =>
          rw [zpow_negSucc, vE.map_inv, vE.map_pow,
            chapter10_normalized_uniformizer_value vE πE hπE]
          rw [hnegcast n, hone]
    refine ⟨πE ^ z, zpow_ne_zero z (chapter10_normalized_uniformizer_ne_zero vE πE hπE), ?_⟩
    rw [hformula _ (zpow_ne_zero z (chapter10_normalized_uniformizer_ne_zero vE πE hπE)),
      hpow]
    simp

/-! The source warns that this image need not be the whole base unit set. -/
def chapter10TotallyRamifiedUnitNormIsProper
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ))
    (vE : AddValuation E (WithTop ℤ)) : Prop :=
  chapter10ValuationUnitNormImage F E vE ≠ chapter10LocalUnitSet vF

theorem chapter10_totally_ramified_unit_norm_properness_is_an_extra_condition
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ))
    (vE : AddValuation E (WithTop ℤ)) :
    chapter10TotallyRamifiedUnitNormIsProper F E vF vE ↔
      chapter10ValuationUnitNormImage F E vE ≠ chapter10LocalUnitSet vF := Iff.rfl

/-! ### The Gaussian rational example -/

def chapter10GaussianRational := ℚ × ℚ

def chapter10GaussianRationalNorm (z : chapter10GaussianRational) : ℚ :=
  z.1 ^ 2 + z.2 ^ 2

theorem chapter10_gaussian_rational_norm_formula (a b : ℚ) :
    chapter10GaussianRationalNorm (a, b) = a ^ 2 + b ^ 2 := by
  rfl

private theorem chapter10_prime_three_divides_gaussian_sum_implies_both_divisible_aux
    (a b : ℤ) (h : 3 ∣ a ^ 2 + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
  have hmod : (a : ZMod 3) ^ 2 + (b : ZMod 3) ^ 2 = 0 := by
    have hcast : ((a ^ 2 + b ^ 2 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2) 3).2 h
    simpa only [Int.cast_add, Int.cast_pow] using hcast
  have hzero : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 := by
    intro x y hxy
    have hxlt : x.val < 3 := x.val_lt
    have hylt : y.val < 3 := y.val_lt
    have hval := congrArg ZMod.val hxy
    simp only [pow_two] at hval
    rw [ZMod.val_add, ZMod.val_mul, ZMod.val_mul] at hval
    have hx_cases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    have hy_cases : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 := by omega
    rcases hx_cases with hx0 | hx1 | hx2
    · exact (ZMod.val_eq_zero x).mp hx0
    · rcases hy_cases with hy0 | hy1 | hy2
      · norm_num [hx1, hy0] at hval
      · norm_num [hx1, hy1] at hval
      · norm_num [hx1, hy2] at hval
    · rcases hy_cases with hy0 | hy1 | hy2
      · norm_num [hx2, hy0] at hval
      · norm_num [hx2, hy1] at hval
      · norm_num [hx2, hy2] at hval
  have ha : (a : ZMod 3) = 0 := hzero _ _ hmod
  have hb : (b : ZMod 3) = 0 := by
    apply hzero
    simpa [add_comm] using hmod
  constructor
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb

theorem chapter10_three_not_a_gaussian_rational_norm :
    ¬ ∃ z : chapter10GaussianRational,
      chapter10GaussianRationalNorm z = 3 := by
  have hno : ∀ n : ℕ, ∀ A B : ℤ,
      A ^ 2 + B ^ 2 = 3 * (n : ℤ) ^ 2 →
        (A ≠ 0 ∨ B ≠ 0) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A B heq hne
        have hdiv : (3 : ℤ) ∣ A ^ 2 + B ^ 2 := by
          rw [heq]
          exact dvd_mul_right _ _
        rcases chapter10_prime_three_divides_gaussian_sum_implies_both_divisible_aux
          A B hdiv with ⟨hA, hB⟩
        rcases hA with ⟨A', rfl⟩
        rcases hB with ⟨B', rfl⟩
        have hne' : A' ≠ 0 ∨ B' ≠ 0 := by
          by_contra h'
          push Not at h'
          rcases h' with ⟨rfl, rfl⟩
          simp at hne
        have h9 : (9 : ℤ) ∣ (3 * A') ^ 2 + (3 * B') ^ 2 := by
          refine ⟨A' ^ 2 + B' ^ 2, ?_⟩
          ring
        have h9rhs : (9 : ℤ) ∣ 3 * (n : ℤ) ^ 2 := by
          rw [← heq]
          exact h9
        rcases h9rhs with ⟨k, hk⟩
        have hn2 : (3 : ℤ) ∣ (n : ℤ) ^ 2 := by
          refine ⟨k, ?_⟩
          nlinarith
        have hn2_nat : 3 ∣ n ^ 2 := by
          exact_mod_cast hn2
        have hn : 3 ∣ n :=
          (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hn2_nat
        rcases hn with ⟨m, hm⟩
        have hm_lt : m < n := by
          have hnpos : 0 < n := by
            by_contra hn0
            have hnzero : n = 0 := by omega
            have heq0 := heq
            rw [hnzero] at heq0
            norm_num at heq0
            have hA0 : 3 * A' = 0 := by
              nlinarith [heq0, sq_nonneg (3 * A'), sq_nonneg (3 * B')]
            have hB0 : 3 * B' = 0 := by
              nlinarith [heq0, sq_nonneg (3 * A'), sq_nonneg (3 * B')]
            rcases hne with hA_ne | hB_ne
            · exact hA_ne hA0
            · exact hB_ne hB0
          omega
        have hm_cast : (n : ℤ) = 3 * (m : ℤ) := by
          exact_mod_cast hm
        rw [hm_cast] at heq
        have hnew : A' ^ 2 + B' ^ 2 = 3 * (m : ℤ) ^ 2 := by
          nlinarith [heq]
        exact ih m hm_lt A' B' hnew hne'
  rintro ⟨⟨a, b⟩, h⟩
  have ha : (a : ℚ) = (a.num : ℚ) / a.den := by
    exact (Rat.num_div_den a).symm
  have hb : (b : ℚ) = (b.num : ℚ) / b.den := by
    exact (Rat.num_div_den b).symm
  change a ^ 2 + b ^ 2 = 3 at h
  rw [ha, hb] at h
  field_simp [Rat.den_nz] at h
  have hclear0 : a.num ^ 2 * (b.den : ℤ) ^ 2 +
      (a.den : ℤ) ^ 2 * b.num ^ 2 =
      (a.den : ℤ) ^ 2 * (b.den : ℤ) ^ 2 * 3 := by
    exact_mod_cast h
  have hclear : (a.num * (b.den : ℤ)) ^ 2 +
      (b.num * (a.den : ℤ)) ^ 2 =
      3 * ((a.den : ℤ) * (b.den : ℤ)) ^ 2 := by
    calc
      (a.num * (b.den : ℤ)) ^ 2 + (b.num * (a.den : ℤ)) ^ 2 =
          a.num ^ 2 * (b.den : ℤ) ^ 2 +
            (a.den : ℤ) ^ 2 * b.num ^ 2 := by ring
      _ = (a.den : ℤ) ^ 2 * (b.den : ℤ) ^ 2 * 3 := hclear0
      _ = 3 * ((a.den : ℤ) * (b.den : ℤ)) ^ 2 := by ring
  have hne : a.num * b.den ≠ 0 ∨ b.num * a.den ≠ 0 := by
    by_contra h'
    push Not at h'
    rcases h' with ⟨hA, hB⟩
    rw [hA, hB] at hclear
    have hdena : (a.den : ℤ) ≠ 0 := by
      exact_mod_cast Rat.den_nz a
    have hdenb : (b.den : ℤ) ≠ 0 := by
      exact_mod_cast Rat.den_nz b
    have hden : (a.den : ℤ) * (b.den : ℤ) ≠ 0 := mul_ne_zero hdena hdenb
    have hpos : 0 < ((a.den : ℤ) * (b.den : ℤ)) ^ 2 := sq_pos_of_ne_zero hden
    nlinarith [hclear]
  exact hno (a.den * b.den) (a.num * b.den) (b.num * a.den) hclear hne

theorem chapter10_prime_three_divides_gaussian_sum_implies_both_divisible
    (a b : ℤ) (h : 3 ∣ a ^ 2 + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
  exact chapter10_prime_three_divides_gaussian_sum_implies_both_divisible_aux a b h

theorem chapter10_three_gaussian_obstruction_by_parity :
    ¬ ∃ a b : ℚ, a ^ 2 + b ^ 2 = 3 := by
  rintro ⟨a, b, h⟩
  apply chapter10_three_not_a_gaussian_rational_norm
  refine ⟨(a, b), ?_⟩
  simpa [chapter10GaussianRationalNorm] using h

private theorem chapter10_three_adic_unit_square_add_one_norm
    (u : ℚ_[3]) (hu : ‖u‖ = 1) : ‖u ^ 2 + 1‖ = 1 := by
  let z : ℤ_[3] := ⟨u, le_of_eq hu⟩
  have hz : ‖z‖ = 1 := by
    change ‖u‖ = 1
    exact hu
  have hle : ‖z ^ 2 + 1‖ ≤ 1 := by
    calc
      ‖z ^ 2 + 1‖ ≤ max ‖z ^ 2‖ ‖(1 : ℤ_[3])‖ :=
        PadicInt.nonarchimedean _ _
      _ = 1 := by rw [norm_pow, hz]; simp
  apply le_antisymm hle
  by_contra hnot
  have hlt : ‖z ^ 2 + 1‖ < 1 := lt_of_not_ge hnot
  have hmem : z ^ 2 + 1 ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact hlt
  have hres : PadicInt.toZMod (z ^ 2 + 1) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact hmem
  have hres' : (PadicInt.toZMod z) ^ 2 + 1 = 0 := by
    simpa using hres
  have hunit : IsUnit z := PadicInt.isUnit_iff.mpr hz
  have hnotmem : z ∉ IsLocalRing.maximalIdeal ℤ_[3] :=
    IsLocalRing.notMem_maximalIdeal.mpr hunit
  have hzres : PadicInt.toZMod z ≠ 0 := by
    intro hzres
    have hker : z ∈ RingHom.ker PadicInt.toZMod := (RingHom.mem_ker).2 hzres
    rw [PadicInt.ker_toZMod] at hker
    exact hnotmem hker
  have hval := congrArg ZMod.val hres'
  simp only [pow_two] at hval
  rw [ZMod.val_add, ZMod.val_mul] at hval
  have hzlt : (PadicInt.toZMod z).val < 3 :=
    (PadicInt.toZMod z).val_lt
  have hcases : (PadicInt.toZMod z).val = 0 ∨
      (PadicInt.toZMod z).val = 1 ∨ (PadicInt.toZMod z).val = 2 := by
    omega
  rcases hcases with hz0 | hz1 | hz2
  · exact hzres ((ZMod.val_eq_zero _).mp hz0)
  · norm_num [hz1, ZMod.val_one_eq_one_mod] at hval
  · norm_num [hz2, ZMod.val_one_eq_one_mod] at hval

private theorem chapter10_three_adic_large_square_sum_norm
    (x y : ℚ_[3]) (hlarge : ‖x‖ > 1 ∨ ‖y‖ > 1) :
    ‖x ^ 2 + y ^ 2‖ = (max ‖x‖ ‖y‖) ^ 2 := by
  by_cases hxy : ‖x‖ = ‖y‖
  · have hx0 : x ≠ 0 := by
      intro hx
      have hxn : ‖x‖ = 0 := by simp [hx]
      have hyn : ‖y‖ = 0 := hxy.symm.trans hxn
      rcases hlarge with hlarge | hlarge <;> nlinarith
    have hy0 : y ≠ 0 := by
      intro hy
      have hyn : ‖y‖ = 0 := by simp [hy]
      have hxn : ‖x‖ = 0 := hxy.trans hyn
      rcases hlarge with hlarge | hlarge <;> nlinarith
    let u : ℚ_[3] := y / x
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      simp [norm_div, hxy, hy0]
    have hu' := chapter10_three_adic_unit_square_add_one_norm u hu
    have hident : x ^ 2 + y ^ 2 = x ^ 2 * (u ^ 2 + 1) := by
      dsimp [u]
      field_simp [hx0]
      ring
    calc
      ‖x ^ 2 + y ^ 2‖ = ‖x ^ 2 * (u ^ 2 + 1)‖ := by rw [hident]
      _ = ‖x‖ ^ 2 * ‖u ^ 2 + 1‖ := by rw [norm_mul, norm_pow]
      _ = (max ‖x‖ ‖y‖) ^ 2 := by simp [hu', hxy]
  · have hxy' : ‖x ^ 2‖ ≠ ‖y ^ 2‖ := by
      intro hsq
      rw [norm_pow, norm_pow] at hsq
      apply hxy
      nlinarith [norm_nonneg x, norm_nonneg y]
    rw [Padic.add_eq_max_of_ne hxy', norm_pow, norm_pow]
    by_cases hle : ‖x‖ ≤ ‖y‖
    · have hsq : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
        nlinarith [norm_nonneg x, norm_nonneg y]
      rw [max_eq_right hsq, max_eq_right hle]
    · have hle' : ‖y‖ ≤ ‖x‖ := le_of_not_ge hle
      have hsq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        nlinarith [norm_nonneg x, norm_nonneg y]
      rw [max_eq_left hsq, max_eq_left hle']

theorem chapter10_three_not_a_three_adic_gaussian_norm :
    ¬ ∃ a b : ℚ_[3], a ^ 2 + b ^ 2 = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hnorm3eq : ‖(3 : ℚ_[3])‖ = (3 : ℝ)⁻¹ := Padic.norm_p
  have hlarge_impossible : ∀ x y : ℚ_[3], x ^ 2 + y ^ 2 = 3 →
      ‖x‖ ≤ 1 := by
    intro x y hxy
    by_contra hx
    have hx' : ‖x‖ > 1 := lt_of_not_ge hx
    have hsum := chapter10_three_adic_large_square_sum_norm x y (Or.inl hx')
    have hmax : 1 < max ‖x‖ ‖y‖ := lt_of_lt_of_le hx' (le_max_left _ _)
    have hmaxsq : 1 < (max ‖x‖ ‖y‖) ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg y]
    have hnorm3 : ‖(3 : ℚ_[3])‖ < 1 := by
      rw [hnorm3eq]
      norm_num
    rw [hxy] at hsum
    nlinarith
  rintro ⟨a, b, h⟩
  have ha_le : ‖a‖ ≤ 1 := hlarge_impossible a b h
  have hb_le : ‖b‖ ≤ 1 := by
    apply hlarge_impossible b a
    simpa [add_comm] using h
  let za : ℤ_[3] := ⟨a, ha_le⟩
  let zb : ℤ_[3] := ⟨b, hb_le⟩
  have hab_int : za ^ 2 + zb ^ 2 = (3 : ℤ_[3]) := by
    apply Subtype.ext
    change a ^ 2 + b ^ 2 = 3
    exact h
  have hres : (PadicInt.toZMod za) ^ 2 + (PadicInt.toZMod zb) ^ 2 = 0 := by
    have hres' := congrArg PadicInt.toZMod hab_int
    have hthree : PadicInt.toZMod (3 : ℤ_[3]) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact (PadicInt.norm_lt_one_iff_dvd (3 : ℤ_[3])).2 (dvd_refl _)
    rw [map_add, map_pow, map_pow, hthree] at hres'
    exact hres'
  have hzero : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 := by
    intro x y hxy
    have hxlt : x.val < 3 := x.val_lt
    have hylt : y.val < 3 := y.val_lt
    have hval := congrArg ZMod.val hxy
    simp only [pow_two] at hval
    rw [ZMod.val_add, ZMod.val_mul, ZMod.val_mul] at hval
    have hx_cases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    have hy_cases : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 := by omega
    rcases hx_cases with hx0 | hx1 | hx2
    · exact (ZMod.val_eq_zero x).mp hx0
    · rcases hy_cases with hy0 | hy1 | hy2
      · norm_num [hx1, hy0] at hval
      · norm_num [hx1, hy1] at hval
      · norm_num [hx1, hy2] at hval
    · rcases hy_cases with hy0 | hy1 | hy2
      · norm_num [hx2, hy0] at hval
      · norm_num [hx2, hy1] at hval
      · norm_num [hx2, hy2] at hval
  have hza0 : PadicInt.toZMod za = 0 := hzero _ _ hres
  have hzb0 : PadicInt.toZMod zb = 0 := by
    apply hzero
    simpa [add_comm] using hres
  have hza_nonunit : ¬ IsUnit za := by
    intro hu
    have hnotmem : za ∉ IsLocalRing.maximalIdeal ℤ_[3] :=
      IsLocalRing.notMem_maximalIdeal.mpr hu
    have hker : za ∈ RingHom.ker PadicInt.toZMod := (RingHom.mem_ker).2 hza0
    rw [PadicInt.ker_toZMod] at hker
    exact hnotmem hker
  have hzb_nonunit : ¬ IsUnit zb := by
    intro hu
    have hnotmem : zb ∉ IsLocalRing.maximalIdeal ℤ_[3] :=
      IsLocalRing.notMem_maximalIdeal.mpr hu
    have hker : zb ∈ RingHom.ker PadicInt.toZMod := (RingHom.mem_ker).2 hzb0
    rw [PadicInt.ker_toZMod] at hker
    exact hnotmem hker
  have ha_lt : ‖za‖ < 1 := PadicInt.not_isUnit_iff.mp hza_nonunit
  have hb_lt : ‖zb‖ < 1 := PadicInt.not_isUnit_iff.mp hzb_nonunit
  have ha_le3 : ‖a‖ ≤ ‖(3 : ℚ_[3])‖ := by
    rcases (PadicInt.norm_lt_one_iff_dvd za).mp ha_lt with ⟨ca, hca⟩
    have hca' := congrArg (fun w : ℤ_[3] => (w : ℚ_[3])) hca
    change a = (3 : ℚ_[3]) * (ca : ℚ_[3]) at hca'
    rw [hca', norm_mul]
    nlinarith [norm_nonneg (3 : ℚ_[3]), ca.2]
  have hb_le3 : ‖b‖ ≤ ‖(3 : ℚ_[3])‖ := by
    rcases (PadicInt.norm_lt_one_iff_dvd zb).mp hb_lt with ⟨cb, hcb⟩
    have hcb' := congrArg (fun w : ℤ_[3] => (w : ℚ_[3])) hcb
    change b = (3 : ℚ_[3]) * (cb : ℚ_[3]) at hcb'
    rw [hcb', norm_mul]
    nlinarith [norm_nonneg (3 : ℚ_[3]), cb.2]
  have ha_sq : ‖a‖ ^ 2 ≤ ‖(3 : ℚ_[3])‖ ^ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg (3 : ℚ_[3])]
  have hb_sq : ‖b‖ ^ 2 ≤ ‖(3 : ℚ_[3])‖ ^ 2 := by
    nlinarith [norm_nonneg b, norm_nonneg (3 : ℚ_[3])]
  have hsum_le : ‖a ^ 2 + b ^ 2‖ ≤ ‖(3 : ℚ_[3])‖ ^ 2 := by
    calc
      ‖a ^ 2 + b ^ 2‖ ≤ max ‖a ^ 2‖ ‖b ^ 2‖ := Padic.nonarchimedean _ _
      _ = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by rw [norm_pow, norm_pow]
      _ ≤ max (‖(3 : ℚ_[3])‖ ^ 2) (‖(3 : ℚ_[3])‖ ^ 2) :=
        max_le (ha_sq.trans (le_max_left _ _)) (hb_sq.trans (le_max_right _ _))
      _ = ‖(3 : ℚ_[3])‖ ^ 2 := max_self _
  have hnorm3sq_lt : ‖(3 : ℚ_[3])‖ ^ 2 < ‖(3 : ℚ_[3])‖ := by
    rw [hnorm3eq]
    norm_num
  have hnorm_eq : ‖a ^ 2 + b ^ 2‖ = ‖(3 : ℚ_[3])‖ := by rw [h]
  have hcontra : ‖(3 : ℚ_[3])‖ ≤ ‖(3 : ℚ_[3])‖ ^ 2 := by
    calc
      ‖(3 : ℚ_[3])‖ = ‖a ^ 2 + b ^ 2‖ := hnorm_eq.symm
      _ ≤ ‖(3 : ℚ_[3])‖ ^ 2 := hsum_le
  exact (not_le_of_gt hnorm3sq_lt) hcontra

end
end LastLib.Book04AdelesAndIdeles.Chapter10
