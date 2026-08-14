import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section01TheMeaningOfTotalRamification
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped BigOperators WithTop

/-! # 8.2. Why Eisenstein coefficients have their shape -/

/-- The power-basis expression used in the integral-basis conclusion of
Book §8.2. -/
def chapter08PowerBasisExpansion
    {A L : Type*} [CommRing A] [Ring L] [Algebra A L]
    {n : ℕ} (α : L) (a : Fin n → A) : L :=
  ∑ i, algebraMap A L (a i) * α ^ (i : ℕ)

/-- Book §8.2: in a normalized DVR, the coefficient condition and the
valuation condition are equivalent formulations of Eisenstein. -/
theorem chapter08_eisenstein_coefficient_valuation_form
    {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (vK : AddValuation K (WithTop ℤ)) (π : A) (g : A[X])
    (hπ : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A)
    (hvalue_ideal : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ↔
        0 < vK (algebraMap A K a))
    (hvalue_square : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ∧
        a ∉ (IsLocalRing.maximalIdeal A) ^ 2 ↔
        vK (algebraMap A K a) = 1) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π g ↔
      g.Monic ∧ 0 < g.natDegree ∧
        (∀ i < g.natDegree,
          0 < vK (algebraMap A K (g.coeff i))) ∧
        vK (algebraMap A K g.constantCoeff) = 1 := by
  constructor
  · intro hg
    rcases hg with ⟨hmonic, hdegree, hcoeff, hconstant, hspan⟩
    refine ⟨hmonic, hdegree, ?_, ?_⟩
    · intro i hi
      apply (hvalue_ideal (g.coeff i)).mp
      rw [← hspan]
      exact hcoeff i hi
    · apply (hvalue_square g.constantCoeff).mp
      refine ⟨?_, ?_⟩
      · rw [← hspan]
        exact hcoeff 0 hdegree
      · intro hconstant_square
        apply hconstant
        rw [← Ideal.span_singleton_pow, hspan]
        exact hconstant_square
  · rintro ⟨hmonic, hdegree, hcoeff, hconstant⟩
    refine ⟨hmonic, hdegree, ?_, ?_, hπ⟩
    · intro i hi
      rw [hπ]
      exact (hvalue_ideal (g.coeff i)).mpr (hcoeff i hi)
    · intro hconstant_square
      apply ((hvalue_square g.constantCoeff).mpr hconstant).2
      rw [← hπ, Ideal.span_singleton_pow]
      exact hconstant_square

/-- Book §8.2, Theorem 8.1: an Eisenstein root gives an irreducible
polynomial, a totally ramified extension of the polynomial degree, a
uniformizer, and the full integral order. -/
theorem chapter08_eisenstein_extension
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (π : A) (g : A[X]) (α : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π g)
    (hroot : aeval α g = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hvalue_ideal : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ↔
        0 < vK (algebraMap A K a))
    (hvalue_square : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ∧
        a ∉ (IsLocalRing.maximalIdeal A) ^ 2 ↔
        vK (algebraMap A K a) = 1)
    (hrestrict : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = g.natDegree • vK x)
    (hπ : vK (algebraMap A K π) = 1) :
    Irreducible (g.map (algebraMap A K)) ∧
      Module.finrank K L = g.natDegree ∧
      chapter08TotallyRamified vK vL hval ∧
      vL α = 1 ∧
      (integralClosure A L : Set L) =
        (Algebra.adjoin A ({α} : Set L) : Set L) ∧
      (∀ x : L, IsIntegral A x →
        ∃! a : Fin g.natDegree → A,
          x = chapter08PowerBasisExpansion α a) := by
  let n : ℕ := g.natDegree
  have hn : 0 < n := by
    dsimp [n]
    exact hf.2.1
  have hspan : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A :=
    hf.2.2.2.2
  have hconstmem : g.constantCoeff ∈ IsLocalRing.maximalIdeal A := by
    rw [← hspan]
    simpa [Polynomial.constantCoeff] using hf.2.2.1 0 hf.2.1
  have hconstnot : g.constantCoeff ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
    intro h
    apply hf.2.2.2.1
    rw [← Ideal.span_singleton_pow, hspan]
    exact h
  have hconstval : vK (algebraMap A K g.constantCoeff) = 1 :=
    (hvalue_square g.constantCoeff).mp ⟨hconstmem, hconstnot⟩
  have hconstne : g.constantCoeff ≠ 0 := by
    intro hzero
    have hbad := hconstval
    rw [hzero, map_zero, AddValuation.map_zero] at hbad
    simp at hbad
  have hcoeff_value (i : Fin (n + 1)) (hci : g.coeff (i : ℕ) ≠ 0) :
      ∃ s : ℤ,
        vK (algebraMap A K (g.coeff (i : ℕ))) = (s : WithTop ℤ) := by
    have hmapne : algebraMap A K (g.coeff (i : ℕ)) ≠ 0 := by
      intro hzero
      apply hci
      apply IsFractionRing.injective A K
      simpa using hzero
    rcases WithTop.ne_top_iff_exists.mp (vK.ne_top_iff.mpr hmapne) with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  have hcoeff_lower (i : Fin (n + 1)) (hi : (i : ℕ) < n)
      (hci : g.coeff (i : ℕ) ≠ 0) :
      (1 : WithTop ℤ) ≤ vK (algebraMap A K (g.coeff (i : ℕ))) := by
    have hmem : g.coeff (i : ℕ) ∈ IsLocalRing.maximalIdeal A := by
      rw [← hspan]
      exact hf.2.2.1 (i : ℕ) hi
    have hpos := (hvalue_ideal (g.coeff (i : ℕ))).mp hmem
    rcases hcoeff_value i hci with ⟨s, hs⟩
    rw [hs]
    apply WithTop.coe_le_coe.mpr
    rw [hs] at hpos
    have hspos : (0 : ℤ) < s := WithTop.coe_lt_coe.mp hpos
    omega
  let terms : Fin (n + 1) → L :=
    fun i => algebraMap A L (g.coeff (i : ℕ)) * α ^ (i : ℕ)
  have hterm_ne_coeff (i : Fin (n + 1)) (hti : terms i ≠ 0) :
      g.coeff (i : ℕ) ≠ 0 := by
    intro hzero
    apply hti
    dsimp [terms]
    rw [hzero, map_zero, zero_mul]
  have hsum : (∑ i, terms i) = 0 := by
    simpa [terms, n, Polynomial.aeval_eq_sum_range,
      Algebra.smul_def, ← Fin.sum_univ_eq_sum_range] using hroot
  have hαne : α ≠ 0 := by
    intro hzero
    have hzeroL : algebraMap A L g.constantCoeff = 0 := by
      change algebraMap A L (g.coeff 0) = 0
      rw [Polynomial.coeff_zero_eq_aeval_zero' g]
      simpa [hzero] using hroot
    have hzeroK : algebraMap A K g.constantCoeff = 0 := by
      apply (algebraMap K L).injective
      rw [← IsScalarTower.algebraMap_apply A K L]
      simpa using hzeroL
    have hbad := hconstval
    rw [hzeroK, AddValuation.map_zero] at hbad
    simp at hbad
  have hαtop : vL α ≠ (⊤ : WithTop ℤ) := vL.ne_top_iff.mpr hαne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hαtop
  have hterm_value (i : Fin (n + 1))
      (hci : g.coeff (i : ℕ) ≠ 0) :
      vL (terms i) =
        n • vK (algebraMap A K (g.coeff (i : ℕ))) +
          (i : ℕ) • vL α := by
    dsimp [terms]
    have hmapne : algebraMap A K (g.coeff (i : ℕ)) ≠ 0 := by
      intro hzero
      apply hci
      apply IsFractionRing.injective A K
      simpa using hzero
    rw [AddValuation.map_mul, IsScalarTower.algebraMap_apply A K L,
      hrestrict _ hmapne, AddValuation.map_pow]
  have hterm_value_coe (i : Fin (n + 1))
      (hci : g.coeff (i : ℕ) ≠ 0) :
      ∃ s : ℤ,
        vK (algebraMap A K (g.coeff (i : ℕ))) = (s : WithTop ℤ) ∧
          vL (terms i) =
            (((n : ℤ) * s + (i : ℤ) * r : ℤ) : WithTop ℤ) := by
    rcases hcoeff_value i hci with ⟨s, hs⟩
    refine ⟨s, hs, ?_⟩
    rw [hterm_value i hci, hs, ← hr]
    norm_cast
  have hterm0 : terms (0 : Fin (n + 1)) ≠ 0 := by
    dsimp [terms]
    have hmap : algebraMap A L g.constantCoeff ≠ 0 := by
      intro hzero
      apply hconstne
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      rw [← IsScalarTower.algebraMap_apply A K L]
      simpa using hzero
    exact mul_ne_zero hmap (pow_ne_zero _ hαne)
  have hterm0_value : vL (terms (0 : Fin (n + 1))) = (n : WithTop ℤ) := by
    have hcoeff0 : g.coeff (0 : ℕ) ≠ 0 := by
      simpa [Polynomial.constantCoeff] using hconstne
    rw [hterm_value (0 : Fin (n + 1)) hcoeff0]
    have hscaled := congrArg (fun z : WithTop ℤ => n • z) hconstval
    simpa [Polynomial.constantCoeff] using hscaled
  have hleading_coeff : g.coeff n = 1 := by
    simpa [n] using hf.1.coeff_natDegree
  have htermN : terms ⟨n, Nat.lt_succ_self n⟩ ≠ 0 := by
    dsimp [terms]
    rw [hleading_coeff]
    simp [hαne]
  have htermN_value :
      vL (terms ⟨n, Nat.lt_succ_self n⟩) = ((n : ℤ) * r : WithTop ℤ) := by
    have hleading_ne : g.coeff n ≠ 0 := by
      rw [hleading_coeff]
      exact one_ne_zero
    rw [hterm_value ⟨n, Nat.lt_succ_self n⟩ hleading_ne,
      hleading_coeff, ← hr]
    simp only [map_one]
    rw [← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  have hno_strict_least (i₀ : Fin (n + 1)) (hti : terms i₀ ≠ 0)
      (hleast : ∀ j, j ≠ i₀ → vL (terms i₀) < vL (terms j)) : False := by
    have hlt : vL (terms i₀) <
        vL (∑ i ∈ (Finset.univ \ {i₀}), terms i) := by
      apply vL.map_lt_sum
      · exact vL.ne_top_iff.mpr hti
      · intro j hj
        exact hleast j (by simpa using (Finset.mem_sdiff.mp hj).2)
    have hcancel : vL (∑ i, terms i) = vL (terms i₀) := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
      exact AddValuation.map_add_eq_of_lt_left vL hlt
    have hfinite : vL (terms i₀) ≠ (⊤ : WithTop ℤ) :=
      vL.ne_top_iff.mpr hti
    apply hfinite
    calc
      vL (terms i₀) = vL (∑ i, terms i) := hcancel.symm
      _ = vL 0 := by rw [hsum]
      _ = ⊤ := AddValuation.map_zero vL
  have hr_le_one : r ≤ 1 := by
    by_contra hnot
    have hgt : (1 : ℤ) < r := lt_of_not_ge hnot
    have hrpos : (0 : ℤ) < r := by omega
    have hleast :
        ∀ j, j ≠ (0 : Fin (n + 1)) →
          vL (terms (0 : Fin (n + 1))) < vL (terms j) := by
      intro j hj
      by_cases ht : terms j = 0
      · rw [ht, AddValuation.map_zero]
        exact (vL.ne_top_iff.mpr hterm0).lt_top
      · have hj0 : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj
          apply Fin.ext
          simpa using hz
        have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
        by_cases hjn : (j : ℕ) = n
        · have hjvalue : vL (terms j) = ((n : ℤ) * r : WithTop ℤ) := by
            have hjc : g.coeff (j : ℕ) ≠ 0 := by
              rw [hjn, hleading_coeff]
              exact one_ne_zero
            rw [hterm_value j hjc, hjn, hleading_coeff, ← hr]
            simp only [map_one]
            rw [← WithTop.coe_nsmul]
            norm_num [nsmul_eq_mul]
          have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
          have hnr : (n : ℤ) < (n : ℤ) * r := by
            simpa using mul_lt_mul_of_pos_left hgt hnZ
          rw [hterm0_value, hjvalue]
          exact WithTop.coe_lt_coe.mpr hnr
        · have hjlt : (j : ℕ) < n := by
            have hjlt' := j.isLt
            omega
          have hjc := hterm_ne_coeff j ht
          rcases hterm_value_coe j hjc with ⟨s, hs, hsterm⟩
          have hs_lower : (1 : ℤ) ≤ s := by
            apply WithTop.coe_le_coe.mp
            rw [← hs]
            exact hcoeff_lower j hjlt hjc
          have hjZ : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hjpos
          have hns : (n : ℤ) ≤ (n : ℤ) * s := by
            calc
              (n : ℤ) = (n : ℤ) * 1 := by ring
              _ ≤ (n : ℤ) * s := mul_le_mul_of_nonneg_left hs_lower (by omega)
          have hir : (0 : ℤ) < (j : ℤ) * r := mul_pos hjZ hrpos
          have hrat : (n : ℤ) < (n : ℤ) * s + (j : ℤ) * r := by
            linarith
          rw [hterm0_value, hsterm]
          exact WithTop.coe_lt_coe.mpr hrat
    exact hno_strict_least (0 : Fin (n + 1)) hterm0 hleast
  have one_le_r : (1 : ℤ) ≤ r := by
    by_contra hnot
    have hlt : r < (1 : ℤ) := lt_of_not_ge hnot
    have hleast :
        ∀ j, j ≠ ⟨n, Nat.lt_succ_self n⟩ →
          vL (terms ⟨n, Nat.lt_succ_self n⟩) < vL (terms j) := by
      intro j hj
      by_cases hjzero : (j : ℕ) = 0
      · have hj' : j = (0 : Fin (n + 1)) := by
          apply Fin.ext
          simpa using hjzero
        have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
        have hnr : (n : ℤ) * r < (n : ℤ) := by
          simpa using mul_lt_mul_of_pos_left hlt hnZ
        rw [htermN_value, hj', hterm0_value]
        exact WithTop.coe_lt_coe.mpr hnr
      · by_cases ht : terms j = 0
        · rw [ht, AddValuation.map_zero]
          exact (vL.ne_top_iff.mpr htermN).lt_top
        · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
          have hjn : (j : ℕ) ≠ n := by
            intro hjn
            apply hj
            apply Fin.ext
            simpa using hjn
          have hjlt : (j : ℕ) < n := by
            have hjlt' := j.isLt
            omega
          have hjc := hterm_ne_coeff j ht
          rcases hterm_value_coe j hjc with ⟨s, hs, hsterm⟩
          have hs_lower : (1 : ℤ) ≤ s := by
            apply WithTop.coe_le_coe.mp
            rw [← hs]
            exact hcoeff_lower j hjlt hjc
          have hjZ : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hjpos
          have hdiffpos : (0 : ℤ) < (n : ℤ) - (j : ℤ) := by
            apply sub_pos.mpr
            exact_mod_cast hjlt
          have hdifflt : (n : ℤ) - (j : ℤ) < (n : ℤ) := by
            have : (0 : ℤ) < (j : ℤ) := hjZ
            linarith
          have hmul :
              ((n : ℤ) - (j : ℤ)) * r <
                ((n : ℤ) - (j : ℤ)) * 1 := by
            simpa using mul_lt_mul_of_pos_left hlt hdiffpos
          have hbase :
              (n : ℤ) * r < (n : ℤ) * 1 + (j : ℤ) * r := by
            calc
              (n : ℤ) * r = (j : ℤ) * r +
                  ((n : ℤ) - (j : ℤ)) * r := by ring
              _ < (j : ℤ) * r + ((n : ℤ) - (j : ℤ)) * 1 := by linarith
              _ ≤ (j : ℤ) * r + (n : ℤ) * 1 := by
                gcongr
              _ = (n : ℤ) * 1 + (j : ℤ) * r := by ring
          have hns : (n : ℤ) * 1 ≤ (n : ℤ) * s := by
            exact mul_le_mul_of_nonneg_left hs_lower (by omega)
          have hrat :
              (n : ℤ) * r < (n : ℤ) * s + (j : ℤ) * r := by
            linarith
          rw [htermN_value, hsterm]
          exact WithTop.coe_lt_coe.mpr hrat
    exact hno_strict_least ⟨n, Nat.lt_succ_self n⟩ htermN hleast
  have hr_one : r = 1 := by omega
  have hα : vL α = 1 := by
    calc
      vL α = (r : WithTop ℤ) := hr.symm
      _ = 1 := by rw [hr_one]; norm_num
  let _ : (Ideal.span ({π} : Set A)).IsPrime := by
    rw [hspan]
    infer_instance
  have hE : g.IsEisensteinAt (Ideal.span ({π} : Set A)) := by
    apply hf.1.isEisensteinAt_of_mem_of_notMem
    · rw [hspan]
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    · intro i hi
      exact hf.2.2.1 i hi
    · simpa [Ideal.span_singleton_pow] using hf.2.2.2.1
  have hirrA : Irreducible g :=
    hE.irreducible inferInstance hf.1.isPrimitive hf.2.1
  have hirrK : Irreducible (g.map (algebraMap A K)) :=
    (hf.1.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have hrootK : aeval α (g.map (algebraMap A K)) = 0 := by
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hroot
  have hmin : g.map (algebraMap A K) = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hirrK hrootK
      (hf.1.map (algebraMap A K))
  have hαintegralK : IsIntegral K α := by
    have hαintegralA : IsIntegral A α := ⟨g, hf.1, hroot⟩
    exact hαintegralA.tower_top
  let B : PowerBasis K L := PowerBasis.ofAdjoinEqTop hαintegralK hgen
  have hBdim : B.dim = n := by
    rw [PowerBasis.ofAdjoinEqTop_dim, ← hmin,
      natDegree_map_eq_of_injective (IsFractionRing.injective A K)]
  have hdegree : Module.finrank K L = n := by
    exact (PowerBasis.finrank B).trans hBdim
  have hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation
        vK := by
    have hπKne : algebraMap A K π ≠ 0 := by
      intro hzero
      have hbad := hπ
      rw [hzero, AddValuation.map_zero] at hbad
      simp at hbad
    refine ⟨algebraMap A K π, hπKne, hπ, ?_⟩
    intro x hx
    rcases WithTop.ne_top_iff_exists.mp (vK.ne_top_iff.mpr hx) with ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  have hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation
        vL := by
    refine ⟨α, hαne, hα, ?_⟩
    intro x hx
    rcases WithTop.ne_top_iff_exists.mp (vL.ne_top_iff.mpr hx) with ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  obtain ⟨d⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_extension_data_exists
      vK vL hval
  let : Finite
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
        d.valueGroupMap.range) :=
    d.finite_quotient
  have hram :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_ramification_index_eq_scale
      vK vL hdiscreteK hdiscreteL hval d n hn hrestrict
  have hfund :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_single_extension_fundamental_inequality
      vK vL hval d
  have hprod : n * d.residueDegree ≤ n := by
    simpa [hram.2, hdegree] using hfund
  have hdres_le : d.residueDegree ≤ 1 := by
    by_contra hnot
    have hdres_two : 2 ≤ d.residueDegree := by omega
    have hmul : n * 2 ≤ n * d.residueDegree := Nat.mul_le_mul_left n hdres_two
    have hn_two : n < n * 2 := by omega
    exact (Nat.not_lt_of_ge hprod) (hn_two.trans_le hmul)
  have hdres_pos : 0 < d.residueDegree := by
    rw [d.residueDegree_eq]
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousResidueDegree
    let vk : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := vK
    let vl : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ) := vL
    let : Valuation.HasExtension vk vl := ⟨hval⟩
    let : Algebra vk.valuationSubring vl.valuationSubring :=
      Valuation.HasExtension.instAlgebra_valuationSubring vk vl
    let : IsLocalHom
        (algebraMap vk.valuationSubring vl.valuationSubring) :=
      Valuation.HasExtension.instIsLocalHomValuationInteger
        (vR := vk) (vS := vl)
    let : Algebra
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField
          vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField
          vl) := inferInstance
    let : Module
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField
          vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField
          vl) := Algebra.toModule
    let : FiniteDimensional
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField
          vk)
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField
          vl) :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_residue_degree_finite
        vk vl
    change 0 < Module.finrank
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vk)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vl)
    exact Module.finrank_pos
  have hdres : d.residueDegree = 1 := by omega
  have htotal : chapter08TotallyRamified vK vL hval := by
    change
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousResidueDegree
          vK vL hval = 1
    exact d.residueDegree_eq.symm.trans hdres
  have hclosure : (integralClosure A L : Set L) =
      (Algebra.adjoin A ({α} : Set L) : Set L) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_integral_closure_is_root_order
      π g α hf hroot (by rfl) hgen
  have hexpK : ∀ x : L, ∃! b : Fin n → K,
      x = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion α b :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_power_basis_expansion_unique
      π g α hf hroot (by rfl) hgen
  have hexpansion : ∀ x : L, IsIntegral A x →
      ∃! a : Fin n → A, x = chapter08PowerBasisExpansion α a := by
    intro x hx
    obtain ⟨b, hxb, hbuniq⟩ := hexpK x
    have hbintegral : ∀ i, IsLocalization.IsInteger A (b i) := by
      intro i
      have hiff :=
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_expansion_integrality_iff
          π g α hf hroot (by rfl) hgen b
      apply hiff.mp
      rw [← hxb]
      exact hx
    choose a ha using hbintegral
    have hxa : x = chapter08PowerBasisExpansion α a := by
      calc
        x = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion α b := hxb
        _ = chapter08PowerBasisExpansion α a := by
          dsimp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion,
            chapter08PowerBasisExpansion]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← ha i]
          simp [IsScalarTower.algebraMap_apply A K L]
    refine ⟨a, hxa, ?_⟩
    intro a' ha'
    have ha'K : x =
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion α
          (fun i => algebraMap A K (a' i)) := by
      calc
        x = chapter08PowerBasisExpansion α a' := ha'
        _ = LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion α
            (fun i => algebraMap A K (a' i)) := by
          dsimp [chapter08PowerBasisExpansion,
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion]
          apply Finset.sum_congr rfl
          intro i hi
          simp [IsScalarTower.algebraMap_apply A K L]
    have hb' := hbuniq (fun i => algebraMap A K (a' i)) ha'K
    apply _root_.funext
    intro i
    apply IsFractionRing.injective A K
    calc
      algebraMap A K (a' i) = (fun i => algebraMap A K (a' i)) i := rfl
      _ = b i := congrFun hb' i
      _ = algebraMap A K (a i) := (ha i).symm
  refine ⟨hirrK, ?_, htotal, hα, hclosure, ?_⟩
  · simpa [n] using hdegree
  · intro x hx
    simpa [n] using hexpansion x hx

/-- The additive value of the `i`th term in a root equation. -/
def chapter08RootEquationTermValue
    {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedAddCommGroupWithTop Γ] [Algebra K L]
    (vL : AddValuation L Γ) (a : K) (α : L) (i : ℕ) : Γ :=
  vL (algebraMap K L a) + i • vL α

/-- A strictly least nonzero additive-valued term cannot cancel in a finite
sum, the additive form of the key Newton-polygon calculation in Book §8.2. -/
theorem chapter08_strictly_least_valued_term_does_not_cancel
    {L Γ : Type*} [Field L]
    [LinearOrderedAddCommGroupWithTop Γ]
    (v : AddValuation L Γ) {ι : Type*} [Fintype ι]
    (terms : ι → L) (i₀ : ι)
    (hnonzero : terms i₀ ≠ 0)
    (hleast : ∀ j, j ≠ i₀ → v (terms i₀) < v (terms j)) :
    v (∑ i, terms i) = v (terms i₀) := by
  classical
  have hlt : v (terms i₀) < v (∑ i ∈ (Finset.univ \ {i₀}), terms i) := by
    apply v.map_lt_sum
    · exact v.ne_top_iff.mpr hnonzero
    · intro j hj
      exact hleast j (by simpa using (Finset.mem_sdiff.mp hj).2)
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
  exact AddValuation.map_add_eq_of_lt_left v hlt

/-- Book §8.2: after extending a normalized valuation to a root field, the
root of an Eisenstein polynomial has value `1/n`. -/
theorem chapter08_eisenstein_root_has_reciprocal_value
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    (vK : AddValuation K (WithTop ℚ))
    (vL : AddValuation L (WithTop ℚ))
    (hrestrict : ∀ x : K, vL (algebraMap K L x) = vK x)
    (n : ℕ) (hn : 0 < n) (g : A[X]) (α : L)
    (hdegree : g.natDegree = n)
    (hmonic : g.Monic)
    (hcoeff : ∀ i < n, 1 ≤ vK (algebraMap A K (g.coeff i)))
    (hconstant : vK (algebraMap A K g.constantCoeff) = 1)
    (hroot : aeval α g = 0) :
    vL α = ((1 : ℚ) / (n : ℚ) : WithTop ℚ) := by
  classical
  let terms : Fin (n + 1) → L :=
    fun i => algebraMap A L (g.coeff (i : ℕ)) * α ^ (i : ℕ)
  have hsum : (∑ i, terms i) = 0 := by
    simpa [terms, hdegree, Polynomial.aeval_eq_sum_range,
      Algebra.smul_def, ← Fin.sum_univ_eq_sum_range] using hroot
  have hconstant_coeff :
      vK (algebraMap A K (g.coeff 0)) = 1 := by
    simpa [Polynomial.constantCoeff] using hconstant
  have hconstant_ne : g.constantCoeff ≠ 0 := by
    intro hzero
    simp [hzero] at hconstant
  have hαne : α ≠ 0 := by
    intro hzero
    have hzeroL : algebraMap A L g.constantCoeff = 0 := by
      change algebraMap A L (g.coeff 0) = 0
      rw [Polynomial.coeff_zero_eq_aeval_zero' g]
      simpa [hzero] using hroot
    have hzeroK : algebraMap A K g.constantCoeff = 0 := by
      apply (algebraMap K L).injective
      rw [← IsScalarTower.algebraMap_apply A K L]
      simpa using hzeroL
    have hbad := hconstant
    rw [hzeroK, AddValuation.map_zero] at hbad
    simp at hbad
  have hαtop : vL α ≠ (⊤ : WithTop ℚ) := vL.ne_top_iff.mpr hαne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hαtop
  have hr' : vL α = (r : WithTop ℚ) := hr.symm
  let q : ℚ := (1 : ℚ) / (n : ℚ)
  have hnqpos : (0 : ℚ) < (n : ℚ) := by
    exact Nat.cast_pos.mpr hn
  have hqpos : (0 : ℚ) < q := by
    dsimp [q]
    exact div_pos (by norm_num) hnqpos
  have hnqone : (n : ℚ) * q = 1 := by
    dsimp [q]
    field_simp [ne_of_gt hnqpos]
  have hterm_value (i : Fin (n + 1)) :
    vL (terms i) =
        vK (algebraMap A K (g.coeff (i : ℕ))) +
          (i : ℕ) • vL α := by
    dsimp [terms]
    rw [AddValuation.map_mul, IsScalarTower.algebraMap_apply A K L,
      hrestrict, AddValuation.map_pow]
  have hterm_coeff_ne (i : Fin (n + 1)) (hti : terms i ≠ 0) :
      g.coeff (i : ℕ) ≠ 0 := by
    intro hzero
    apply hti
    dsimp [terms]
    rw [hzero, map_zero, zero_mul]
  have hcoeff_value (i : Fin (n + 1)) (hti : terms i ≠ 0) :
      ∃ s : ℚ,
        vK (algebraMap A K (g.coeff (i : ℕ))) = (s : WithTop ℚ) := by
    have htop : vK (algebraMap A K (g.coeff (i : ℕ))) ≠ (⊤ : WithTop ℚ) := by
      apply vK.ne_top_iff.mpr
      intro hzero
      apply hterm_coeff_ne i hti
      apply IsFractionRing.injective A K
      simpa using hzero
    rcases WithTop.ne_top_iff_exists.mp htop with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  have hterm_value_coe (i : Fin (n + 1)) (hti : terms i ≠ 0) :
      ∃ s : ℚ,
        vK (algebraMap A K (g.coeff (i : ℕ))) = (s : WithTop ℚ) ∧
          vL (terms i) = ((s + (i : ℚ) * r : ℚ) : WithTop ℚ) := by
    rcases hcoeff_value i hti with ⟨s, hs⟩
    refine ⟨s, hs, ?_⟩
    rw [hterm_value i, hs, hr']
    rw [← WithTop.coe_nsmul, ← WithTop.coe_add]
    norm_num [nsmul_eq_mul]
  have hleading_coeff : g.coeff n = 1 := by
    simpa [hdegree] using hmonic.coeff_natDegree
  have hleading_value :
      vK (algebraMap A K (g.coeff n)) = 0 := by
    rw [hleading_coeff]
    simp
  have hterm0 : terms (0 : Fin (n + 1)) ≠ 0 := by
    dsimp [terms]
    have hmap : algebraMap A L (g.coeff 0) ≠ 0 := by
      intro hzero
      apply hconstant_ne
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      rw [← IsScalarTower.algebraMap_apply A K L]
      simpa using hzero
    exact mul_ne_zero hmap (pow_ne_zero _ hαne)
  have hterm0_value : vL (terms (0 : Fin (n + 1))) = 1 := by
    rw [hterm_value]
    simpa [Polynomial.constantCoeff] using hconstant
  let iN : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hiN : (iN : ℕ) = n := rfl
  have htermN : terms iN ≠ 0 := by
    dsimp [terms, iN]
    rw [hleading_coeff]
    simp [hαne]
  have htermN_value :
      vL (terms iN) = ((n : ℚ) * r : WithTop ℚ) := by
    rw [hterm_value iN, hiN, hleading_value, hr', zero_add,
      ← WithTop.coe_nsmul]
    congr 1
  have hno_strict_least (i₀ : Fin (n + 1)) (hti : terms i₀ ≠ 0)
      (hleast : ∀ j, j ≠ i₀ → vL (terms i₀) < vL (terms j)) : False := by
    have hcancel :=
      chapter08_strictly_least_valued_term_does_not_cancel
        vL terms i₀ hti hleast
    have hfinite : vL (terms i₀) ≠ (⊤ : WithTop ℚ) :=
      vL.ne_top_iff.mpr hti
    apply hfinite
    calc
      vL (terms i₀) = vL (∑ i, terms i) := hcancel.symm
      _ = vL 0 := by rw [hsum]
      _ = ⊤ := AddValuation.map_zero vL
  have hconstant_least (hgt : q < r) : False := by
    have hrpos : (0 : ℚ) < r := lt_trans hqpos hgt
    have hlead_rat : (1 : ℚ) < (n : ℚ) * r := by
      calc
        (1 : ℚ) = (n : ℚ) * q := hnqone.symm
        _ < (n : ℚ) * r := mul_lt_mul_of_pos_left hgt hnqpos
    have hleast :
        ∀ j, j ≠ (0 : Fin (n + 1)) →
          vL (terms (0 : Fin (n + 1))) < vL (terms j) := by
      intro j hj
      by_cases ht : terms j = 0
      · rw [ht, AddValuation.map_zero]
        exact (vL.ne_top_iff.mpr hterm0).lt_top
      · have hj0 : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj
          apply Fin.ext
          simpa using hz
        have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
        by_cases hjn : (j : ℕ) = n
        · have hjvalue : vL (terms j) = ((n : ℚ) * r : WithTop ℚ) := by
            rw [hterm_value j, hjn, hleading_value, hr', zero_add,
              ← WithTop.coe_nsmul]
            congr 1
          rw [hterm0_value, hjvalue]
          exact WithTop.coe_lt_coe.mpr hlead_rat
        · have hjlt : (j : ℕ) < n := by
            have hjlt' := j.isLt
            omega
          rcases hterm_value_coe j ht with ⟨s, hs, hsterm⟩
          have hs_lower_top : (1 : WithTop ℚ) ≤ (s : WithTop ℚ) := by
            rw [← hs]
            exact hcoeff (j : ℕ) hjlt
          have hs_lower : (1 : ℚ) ≤ s := by
            exact WithTop.coe_le_coe.mp hs_lower_top
          have hjqpos : (0 : ℚ) < (j : ℚ) := by
            exact Nat.cast_pos.mpr hjpos
          have hrat : (1 : ℚ) < s + (j : ℚ) * r := by
            have : 0 < (j : ℚ) * r := mul_pos hjqpos hrpos
            linarith
          rw [hterm0_value, hsterm]
          exact WithTop.coe_lt_coe.mpr hrat
    exact hno_strict_least (0 : Fin (n + 1)) hterm0 hleast
  have hleading_least (hlt : r < q) : False := by
    have hnr : (n : ℚ) * r < 1 := by
      calc
        (n : ℚ) * r < (n : ℚ) * q := mul_lt_mul_of_pos_left hlt hnqpos
        _ = 1 := hnqone
    have hleast :
        ∀ j, j ≠ iN → vL (terms iN) < vL (terms j) := by
      intro j hj
      by_cases hjzero : (j : ℕ) = 0
      · have hj' : j = (0 : Fin (n + 1)) := by
          apply Fin.ext
          simpa using hjzero
        rw [hj', htermN_value, hterm0_value]
        exact WithTop.coe_lt_coe.mpr hnr
      · by_cases ht : terms j = 0
        · rw [ht, AddValuation.map_zero]
          exact (vL.ne_top_iff.mpr htermN).lt_top
        · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
          have hjn : (j : ℕ) ≠ n := by
            intro hjn
            apply hj
            apply Fin.ext
            simpa [hiN] using hjn
          have hjlt : (j : ℕ) < n := by
            have hjlt' := j.isLt
            omega
          rcases hterm_value_coe j ht with ⟨s, hs, hsterm⟩
          have hs_lower_top : (1 : WithTop ℚ) ≤ (s : WithTop ℚ) := by
            rw [← hs]
            exact hcoeff (j : ℕ) hjlt
          have hs_lower : (1 : ℚ) ≤ s := by
            exact WithTop.coe_le_coe.mp hs_lower_top
          have hjqpos : (0 : ℚ) < (j : ℚ) := by
            exact Nat.cast_pos.mpr hjpos
          have hdiffpos : (0 : ℚ) < (n : ℚ) - (j : ℚ) := by
            have : (j : ℚ) < (n : ℚ) := Nat.cast_lt.mpr hjlt
            linarith
          have hdifflt : (n : ℚ) - (j : ℚ) < (n : ℚ) := by
            have : (0 : ℚ) < (j : ℚ) := hjqpos
            linarith
          have hmul :
              ((n : ℚ) - (j : ℚ)) * r <
                ((n : ℚ) - (j : ℚ)) * q :=
            mul_lt_mul_of_pos_left hlt hdiffpos
          have hmulq :
              ((n : ℚ) - (j : ℚ)) * q < 1 := by
            calc
              ((n : ℚ) - (j : ℚ)) * q < (n : ℚ) * q :=
                mul_lt_mul_of_pos_right hdifflt hqpos
              _ = 1 := hnqone
          have hbase : (n : ℚ) * r < 1 + (j : ℚ) * r := by
            have hdiff :
                ((n : ℚ) - (j : ℚ)) * r < 1 := hmul.trans hmulq
            calc
              (n : ℚ) * r = (j : ℚ) * r +
                  ((n : ℚ) - (j : ℚ)) * r := by ring
              _ < (j : ℚ) * r + 1 := by linarith
              _ = 1 + (j : ℚ) * r := by ring
          have hrat : (n : ℚ) * r < s + (j : ℚ) * r := by
            apply lt_of_lt_of_le hbase
            linarith
          rw [htermN_value, hsterm]
          exact WithTop.coe_lt_coe.mpr hrat
    exact hno_strict_least iN htermN hleast
  have hr_le_q : r ≤ q := by
    by_contra hnot
    exact hconstant_least (lt_of_not_ge hnot)
  have hq_le_r : q ≤ r := by
    by_contra hnot
    exact hleading_least (lt_of_not_ge hnot)
  have hrq : r = q := le_antisymm hr_le_q hq_le_r
  have hcoe : (r : WithTop ℚ) = (q : WithTop ℚ) := by
    exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hrq
  simpa [hr', q] using hcoe

/-- Book §8.2: the value group generated by an Eisenstein root contains the
fractional lattice `(1/n)ℤ`. -/
theorem chapter08_eisenstein_value_group_contains_fractional_lattice
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℚ))
    (n : ℕ) (_hn : n ≠ 0) (α : L) (_hα : α ≠ 0)
    (hvalue : vL α = ((1 : ℚ) / (n : ℚ) : WithTop ℚ)) :
    ∀ z : ℤ, ∃ x : L,
      vL x = ((z : ℚ) / (n : ℚ) : WithTop ℚ) := by
  intro z
  cases z with
  | ofNat z =>
      refine ⟨α ^ z, ?_⟩
      rw [AddValuation.map_pow, hvalue]
      rw [← WithTop.coe_nsmul]
      congr 1
      norm_num [nsmul_eq_mul, div_eq_mul_inv]
  | negSucc z =>
      refine ⟨(α⁻¹) ^ (z + 1), ?_⟩
      rw [AddValuation.map_pow, AddValuation.map_inv, hvalue]
      change
        ((↑((z + 1) • (-((1 : ℚ) / (n : ℚ)))) : WithTop ℚ)) =
          ((↑((-((z + 1 : ℕ) : ℚ) / (n : ℚ))) : WithTop ℚ))
      congr 1
      norm_num [nsmul_eq_mul, div_eq_mul_inv]
      ring

/-- Book §8.2: the value-group lower bound and the root-equation upper bound
force the degree of an Eisenstein extension to be exactly `n`. -/
theorem chapter08_eisenstein_value_group_forces_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℚ))
    (vL : AddValuation L (WithTop ℚ))
    (_hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hrestrict : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = vK x)
    (n : ℕ) (hn : 0 < n) (πK : K)
    (_hπK : vK πK = 1)
    (hbase : ∀ x : K, x ≠ 0 →
      ∃ z : ℤ, vK x = ((z : ℚ) : WithTop ℚ))
    (hvalue_group : ∀ z : ℤ, ∃ x : L,
      vL x = ((z : ℚ) / (n : ℚ) : WithTop ℚ))
    (hupper : Module.finrank K L ≤ n) :
    n ≤ Module.finrank K L ∧ Module.finrank K L = n := by
  classical
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn.ne'
  obtain ⟨β, hβ⟩ := hvalue_group 1
  have hβ0 : β ≠ 0 := by
    apply vL.ne_top_iff.mp
    rw [hβ]
    simp
  have hli : LinearIndependent K (fun i : Fin n => β ^ (i : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let terms : Fin n → L :=
      fun i => algebraMap K L (c i) * β ^ (i : ℕ)
    have hterm_value (i : Fin n) (hci : c i ≠ 0) :
        ∃ z : ℤ,
          vL (terms i) =
            (((z : ℚ) + (i : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) := by
      rcases hbase (c i) hci with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      dsimp [terms]
      rw [AddValuation.map_mul, hrestrict (c i) hci,
        AddValuation.map_pow, hβ, hz]
      rw [← WithTop.coe_nsmul]
      congr 1
      norm_num [nsmul_eq_mul, div_eq_mul_inv]
    have hdistinct (i j : Fin n) (hij : i ≠ j)
        (hci : c i ≠ 0) (hcj : c j ≠ 0) :
        vL (terms i) ≠ vL (terms j) := by
      intro heq
      rcases hterm_value i hci with ⟨zi, hzi⟩
      rcases hterm_value j hcj with ⟨zj, hzj⟩
      rw [hzi, hzj] at heq
      have hq :
          (zi : ℚ) + (i : ℚ) / (n : ℚ) =
            (zj : ℚ) + (j : ℚ) / (n : ℚ) := by
        exact_mod_cast heq
      have hq' := hq
      field_simp [hnq] at hq'
      have hz :
          (n : ℤ) * zi + (i : ℤ) =
            (n : ℤ) * zj + (j : ℤ) := by
        have hz' :
            zi * (n : ℤ) + (i : ℤ) =
              (n : ℤ) * zj + (j : ℤ) := by
          exact_mod_cast hq'
        calc
          (n : ℤ) * zi + (i : ℤ) = zi * (n : ℤ) + (i : ℤ) := by
            rw [mul_comm]
          _ = (n : ℤ) * zj + (j : ℤ) := hz'
      have hmod := congrArg (fun z : ℤ => z % (n : ℤ)) hz
      have hi0 : 0 ≤ (i : ℤ) := by omega
      have hj0 : 0 ≤ (j : ℤ) := by omega
      have hin : (i : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
      have hjn : (j : ℤ) < (n : ℤ) := by exact_mod_cast j.isLt
      have hmi :
          ((n : ℤ) * zi + (i : ℤ)) % (n : ℤ) = (i : ℤ) := by
        rw [show (n : ℤ) * zi + (i : ℤ) =
            (i : ℤ) + (n : ℤ) * zi by ring,
          Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi0 hin]
      have hmj :
          ((n : ℤ) * zj + (j : ℤ)) % (n : ℤ) = (j : ℤ) := by
        rw [show (n : ℤ) * zj + (j : ℤ) =
            (j : ℤ) + (n : ℤ) * zj by ring,
          Int.add_mul_emod_self_left, Int.emod_eq_of_lt hj0 hjn]
      rw [hmi, hmj] at hmod
      apply hij
      apply Fin.ext
      exact_mod_cast hmod
    let s : Finset (Fin n) := Finset.univ.filter (fun i => c i ≠ 0)
    by_contra hnot
    have hnonzero : ∃ i, c i ≠ 0 := by
      by_contra hnone
      apply hnot
      intro i
      by_contra hci
      exact hnone ⟨i, hci⟩
    rcases hnonzero with ⟨i, hci⟩
    have hs : s.Nonempty := ⟨i, by simp [s, hci]⟩
    obtain ⟨i₀, hi₀, hmin⟩ :=
      Finset.exists_min_image s (fun i => vL (terms i)) hs
    have hci₀ : c i₀ ≠ 0 := by simpa [s] using hi₀
    have hterm₀ : terms i₀ ≠ 0 := by
      dsimp [terms]
      refine mul_ne_zero ?_ (pow_ne_zero _ hβ0)
      intro hzero
      apply hci₀
      apply (algebraMap K L).injective
      simpa using hzero
    have hleast : ∀ j, j ≠ i₀ → vL (terms i₀) < vL (terms j) := by
      intro j hji
      by_cases hcj : c j = 0
      · dsimp [terms]
        rw [hcj, map_zero, zero_mul, AddValuation.map_zero]
        exact (vL.ne_top_iff.mpr hterm₀).lt_top
      · have hj : j ∈ s := by simp [s, hcj]
        have hle := hmin j hj
        have hneval := hdistinct i₀ j (Ne.symm hji) hci₀ hcj
        exact lt_of_le_of_ne hle hneval
    have hcancel :=
      chapter08_strictly_least_valued_term_does_not_cancel
        vL terms i₀ hterm₀ hleast
    have hsum : (∑ i, terms i) = 0 := by
      simpa [terms, Algebra.smul_def] using hc
    have hnotop : vL (terms i₀) ≠ (⊤ : WithTop ℚ) :=
      vL.ne_top_iff.mpr hterm₀
    exfalso
    apply hnotop
    calc
      vL (terms i₀) = vL (∑ i, terms i) := hcancel.symm
      _ = vL 0 := by rw [hsum]
      _ = ⊤ := AddValuation.map_zero vL
  have hlower : n ≤ Module.finrank K L := by
    simpa using hli.fintype_card_le_finrank
  exact ⟨hlower, Nat.le_antisymm hupper hlower⟩

/-- Distinctness of the valuation residues used in the Eisenstein basis
calculation (Book 2, Section 8.2). -/
theorem chapter08_eisenstein_terms_distinct_mod_degree
    (n : ℕ) (ω : ℕ → ℤ) (a : Fin n → ℕ) :
    ∀ i j : Fin n, i ≠ j →
      ((n : ℤ) * ω (a i) + (i : ℤ)) % (n : ℤ) ≠
        ((n : ℤ) * ω (a j) + (j : ℤ)) % (n : ℤ) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_term_values_are_distinct_modulo_degree ω a

/-- Integrality of an Eisenstein power-basis expansion is coefficientwise
integrality (Book 2, Section 8.2). -/
theorem chapter08_eisenstein_expansion_integrality_iff
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (varpi : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval varpi f = 0)
    (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({varpi} : Set L) = ⊤)
    (a : Fin n → K) :
    IsIntegral A (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisensteinExpansion varpi a) ↔
      ∀ i, IsLocalization.IsInteger A (a i) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_expansion_integrality_iff
    π f varpi hf hroot hdegree hgenerates a

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
