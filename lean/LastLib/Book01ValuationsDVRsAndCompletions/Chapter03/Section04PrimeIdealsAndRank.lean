import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section03IdealsAreOrdered
import Mathlib.RingTheory.Valuation.RankOne

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter03

open Set
open scoped BigOperators WithZero LaurentSeries PowerSeries

/-!
# Chapter 3: Valuation rings and divisibility

Mathlib uses multiplicative valuations, so bounded elements are written `v x ≤ 1`.
The additive convention in the book is recorded below with `AddValuation`; under the
usual sign change, `v x ≤ 1` is the same assertion as `0 ≤ v x`.
-/

universe u v w

/-! # Book 1, Chapter 3, Section 3.4: Prime Ideals and Rank
-/

section PrimeIdealsAndRank

variable {K : Type*} [Field K]

/-! ### 3.4. Prime ideals and rank -/

/-- A chapter-local interface for a convex additive subgroup of an ordered group. -/
structure ChapterConvexAddSubgroup (G : Type*) [AddCommGroup G] [LinearOrder G] where
  carrier : AddSubgroup G
  convex : ∀ {a b c : G}, a ≤ b → b ≤ c → a ∈ carrier → c ∈ carrier → b ∈ carrier

noncomputable def valuationPrimeSpectrum_orderEquiv (A : ValuationSubring K) :
    (PrimeSpectrum A)ᵒᵈ ≃o {S : ValuationSubring K // A ≤ S} :=
  ValuationSubring.primeSpectrumOrderEquiv A

noncomputable def valuationPrimeSpectrum_equiv_coarsenings (A : ValuationSubring K) :
    PrimeSpectrum A ≃ {S : ValuationSubring K // A ≤ S} :=
  ValuationSubring.primeSpectrumEquiv A

theorem convex_scales_correspond_to_prime_ideals (A : ValuationSubring K) :
    Nonempty ((PrimeSpectrum A)ᵒᵈ ≃o {S : ValuationSubring K // A ≤ S}) :=
  ⟨valuationPrimeSpectrum_orderEquiv A⟩

/- Rank one is the nontrivial Archimedean case. -/

def IsRankOneValuation {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  Nonempty (Valuation.RankOne v)

theorem isRankOneValuation_iff_archimedean_valueGroup
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [v.IsNontrivial] :
    IsRankOneValuation v ↔
      MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
  change Nonempty (Valuation.RankOne v) ↔ _
  exact Valuation.nonempty_rankOne_iff_mulArchimedean

private theorem rankOne_prime_bot_or_maximal
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (P : Ideal (valuationRingOf v)) (hP : P.IsPrime) :
    P = ⊥ ∨ P = maximalIdealOf v := by
  classical
  letI : P.IsPrime := hP
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
    letI : v.IsNontrivial := by
      exact hrank.some.toIsNontrivial
    exact (isRankOneValuation_iff_archimedean_valueGroup v).mp hrank
  letI : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := harch
  by_cases hP0 : P = ⊥
  · exact Or.inl hP0
  right
  apply le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime P)
  have hnonzero : ∃ x : valuationRingOf v, x ∈ P ∧ x ≠ 0 := by
    by_contra h
    apply hP0
    apply le_antisymm
    · intro z hz
      have hz0 : z = 0 := by
        by_contra hz0
        exact h ⟨z, hz, hz0⟩
      simpa [hz0]
    · exact bot_le
  obtain ⟨x, hxP, hx0⟩ := hnonzero
  intro y hymax
  by_cases hy0 : y = 0
  · simpa [hy0] using P.zero_mem
  have hylt : v.restrict (y : K) < 1 := by
    rw [Valuation.restrict_lt_one_iff]
    exact (mem_maximalIdealOf_iff v y).mp hymax
  have hxK : (x : K) ≠ 0 := by
    intro hzero
    apply hx0
    exact Subtype.ext hzero
  have hxpos : 0 < v.restrict (x : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr hxK
  have hypos : 0 < v.restrict (y : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr (by
      exact fun hzero => hy0 (Subtype.ext hzero))
  have hyinv : 1 < (v.restrict (y : K))⁻¹ :=
    (one_lt_inv₀ hypos).2 hylt
  obtain ⟨n, hn⟩ := harch.arch (v.restrict (x : K))⁻¹ hyinv
  have hpowR : (v.restrict (y : K)) ^ n ≤ v.restrict (x : K) := by
    apply (inv_le_inv₀ hxpos (pow_pos hypos n)).mp
    simpa [inv_pow] using hn
  have hpow : v ((y : K) ^ n) ≤ v (x : K) := by
    rw [← Valuation.restrict_le_iff]
    simpa [v.map_pow] using hpowR
  have hcval : v ((y : K) ^ n / (x : K)) ≤ 1 := by
    rw [v.map_div, div_le_iff₀ (v.pos_iff.mpr hxK)]
    simpa using hpow
  let c : valuationRingOf v :=
    ⟨(y : K) ^ n / (x : K), (mem_valuationRingOf_iff v _).2 hcval⟩
  have hcy : (c : K) * (x : K) = (y : K) ^ n := by
    dsimp [c]
    field_simp [hxK]
  have hpowP : y ^ n ∈ P := by
    have hmul : c * x ∈ P := P.mul_mem_left c hxP
    convert hmul using 1
    apply Subtype.ext
    exact hcy.symm
  exact hP.mem_of_pow_mem n hpowP

private theorem nonarch_valuation_has_intermediate_prime
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    (hnotarch : ¬ MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v))) :
    ∃ P : Ideal (valuationRingOf v), P.IsPrime ∧ P ≠ ⊥ ∧
      P ≠ maximalIdealOf v := by
  classical
  let G₀ := MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)
  have hforall : ¬ (∀ α : G₀, ∀ β : G₀, 1 < β →
      ∃ n : ℕ, α ≤ β ^ n) := by
    intro h
    apply hnotarch
    exact ⟨by
      intro α β hβ
      exact h α β hβ⟩
  obtain ⟨α, hα⟩ := not_forall.mp hforall
  obtain ⟨β, hβnot⟩ := not_forall.mp hα
  obtain ⟨hβ, hbad⟩ := Classical.not_imp.mp hβnot
  have hα1 : 1 < α := by
    have hbad0 : ¬ α ≤ β ^ 0 := by
      intro h
      exact hbad ⟨0, h⟩
    simpa using (lt_of_not_ge hbad0)
  have hαpos : 0 < α := zero_lt_one.trans hα1
  have hβpos : 0 < β := zero_lt_one.trans hβ
  have hmq : ∀ n : ℕ, α⁻¹ < (β⁻¹) ^ n := by
    intro n
    have hbadn : ¬ α ≤ β ^ n := by
      intro h
      exact hbad ⟨n, h⟩
    have hba : β ^ n < α := lt_of_not_ge hbadn
    have hinv : α⁻¹ < (β ^ n)⁻¹ :=
      (inv_lt_inv₀ hαpos (pow_pos hβpos n)).2 hba
    simpa [inv_pow] using hinv
  have hqpos : 0 < β⁻¹ := inv_pos.mpr hβpos
  have hq_lt : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  let f := MonoidWithZeroHom.ofClass v
  obtain ⟨xm, hxm⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective f (α⁻¹)
  obtain ⟨xq, hxq⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective f (β⁻¹)
  have hxmR : v.restrict xm = α⁻¹ := by
    simpa [Valuation.restrict_def, f] using hxm
  have hxqR : v.restrict xq = β⁻¹ := by
    simpa [Valuation.restrict_def, f] using hxq
  have hxm_lt : v xm < 1 := by
    rw [← Valuation.restrict_lt_one_iff, hxmR]
    exact inv_lt_one_of_one_lt₀ hα1
  have hxq_lt : v xq < 1 := by
    rw [← Valuation.restrict_lt_one_iff, hxqR]
    exact hq_lt
  let xmA : valuationRingOf v :=
    ⟨xm, (mem_valuationRingOf_iff v xm).2 hxm_lt.le⟩
  let xqA : valuationRingOf v :=
    ⟨xq, (mem_valuationRingOf_iff v xq).2 hxq_lt.le⟩
  let P : Ideal (valuationRingOf v) :=
    { carrier := {x | ∀ n : ℕ, v.restrict (x : K) < (β⁻¹) ^ n}
      zero_mem' := by
        intro n
        simpa using (pow_pos hqpos n)
      add_mem' := by
        intro x y hx hy n
        change v.restrict ((x : K) + (y : K)) < (β⁻¹) ^ n
        exact v.restrict.map_add_lt (hx n) (hy n)
      smul_mem' := by
        intro r x hx
        change ∀ n : ℕ, v.restrict ((r : K) * (x : K)) < (β⁻¹) ^ n
        intro n
        rw [v.restrict.map_mul]
        have hr : v.restrict (r : K) ≤ 1 := by
          rw [Valuation.restrict_le_one_iff]
          exact (mem_valuationRingOf_iff v (r : K)).mp r.property
        exact (mul_le_of_le_one_left' hr).trans_lt (hx n) }
  have hxm_mem : xmA ∈ P := by
    change ∀ n : ℕ, v.restrict xm < (β⁻¹) ^ n
    rw [hxmR]
    exact hmq
  have hxm_ne : xmA ≠ 0 := by
    intro hzero
    have hz' : v.restrict (xmA : K) = v.restrict (0 : K) :=
      congrArg (fun z : valuationRingOf v => v.restrict (z : K)) hzero
    have hz : v.restrict xm = 0 := by
      simpa [xmA] using hz'
    rw [hxmR] at hz
    exact (inv_ne_zero hαpos.ne') hz
  have hxq_not_mem : xqA ∉ P := by
    intro hmem
    change ∀ n : ℕ, v.restrict xq < (β⁻¹) ^ n at hmem
    have hone := hmem 1
    rw [hxqR, pow_one] at hone
    exact (lt_irrefl _ hone)
  have hP_ne_top : P ≠ ⊤ := by
    intro htop
    apply hxq_not_mem
    rw [htop]
    trivial
  have hP_prime : P.IsPrime := by
    refine ⟨hP_ne_top, ?_⟩
    intro x y hxy
    by_cases hx : x ∈ P
    · exact Or.inl hx
    by_cases hy : y ∈ P
    · exact Or.inr hy
    exfalso
    change ¬ (∀ n : ℕ, v.restrict (x : K) < (β⁻¹) ^ n) at hx
    change ¬ (∀ n : ℕ, v.restrict (y : K) < (β⁻¹) ^ n) at hy
    obtain ⟨m, hm⟩ := not_forall.mp hx
    obtain ⟨n, hn⟩ := not_forall.mp hy
    have hm' : (β⁻¹) ^ m ≤ v.restrict (x : K) := le_of_not_gt hm
    have hn' : (β⁻¹) ^ n ≤ v.restrict (y : K) := le_of_not_gt hn
    have hlow : (β⁻¹) ^ (m + n) ≤
        v.restrict (x : K) * v.restrict (y : K) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg hm' hn'
        (pow_pos hqpos m).le ((pow_pos hqpos n).le.trans hn')
    change ∀ n : ℕ, v.restrict ((x * y : valuationRingOf v) : K) <
      (β⁻¹) ^ n at hxy
    have hxy' := hxy (m + n)
    have hxy'' : v.restrict (x : K) * v.restrict (y : K) <
        (β⁻¹) ^ (m + n) := by
      simpa [v.restrict.map_mul] using hxy'
    exact (not_lt_of_ge hlow) hxy''
  have hP_le_max : P ≤ maximalIdealOf v := by
    intro z hz
    apply (mem_maximalIdealOf_iff v z).2
    change ∀ n : ℕ, v.restrict (z : K) < (β⁻¹) ^ n at hz
    have hz0 := hz 0
    exact (Valuation.restrict_lt_one_iff (v := v)).mp (by simpa using hz0)
  have hxq_max : xqA ∈ maximalIdealOf v :=
    (mem_maximalIdealOf_iff v xqA).2 hxq_lt
  have hP_ne_max : P ≠ maximalIdealOf v := by
    intro heq
    apply hxq_not_mem
    rw [heq]
    exact hxq_max
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have hzero : xmA ∈ (⊥ : Ideal (valuationRingOf v)) := by
      rw [← hbot]
      exact hxm_mem
    have : xmA = 0 := by simpa using hzero
    exact hxm_ne this
  exact ⟨P, hP_prime, hP_ne_bot, hP_ne_max⟩


 theorem valuationRing_rankOne_iff_krullDim_one
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hnontrivial : v.IsNontrivial) :
    IsRankOneValuation v ↔ ringKrullDim (valuationRingOf v) = 1 := by
  classical
  letI : v.IsNontrivial := hnontrivial
  constructor
  · intro hrank
    have hradical_of_nonzero_proper : ∀ (I : Ideal (valuationRingOf v)),
        I ≠ ⊥ → I ≠ ⊤ → Ideal.radical I = maximalIdealOf v := by
      intro I hI0 hItop
      have hle : Ideal.radical I ≤ maximalIdealOf v := by
        apply (Ideal.IsPrime.radical_le_iff
          (IsLocalRing.maximalIdeal.isMaximal (valuationRingOf v)).isPrime).2
        exact IsLocalRing.le_maximalIdeal hItop
      have hge : maximalIdealOf v ≤ Ideal.radical I := by
        rw [Ideal.radical_eq_sInf]
        refine le_sInf (fun J hJ => ?_)
        rcases rankOne_prime_bot_or_maximal v hrank J hJ.2 with hbot | hmax
        · exfalso
          apply hI0
          apply le_antisymm
          · simpa [hbot] using hJ.1
          · exact bot_le
        · simpa [hmax]
      exact le_antisymm hle hge
    apply (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain).2
    constructor
    · intro hfield
      letI : IsField (valuationRingOf v) := hfield
      have hbot : maximalIdealOf v = ⊥ :=
        (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
      obtain ⟨z, hz0, hz1⟩ := hnontrivial.exists_val_nontrivial
      obtain hz | hz := Valuation.val_le_one_or_val_inv_le_one v z
      · have hzlt : v z < 1 := lt_of_le_of_ne hz hz1
        let hzA : valuationRingOf v :=
          ⟨z, (mem_valuationRingOf_iff v z).2 hz⟩
        have hzm : hzA ∈ maximalIdealOf v :=
          (mem_maximalIdealOf_iff v hzA).2 (by simpa [hzA] using hzlt)
        have hzbot : hzA ∈ (⊥ : Ideal (valuationRingOf v)) := by
          rw [← hbot]
          exact hzm
        have hzero : hzA = 0 := by simpa using hzbot
        have hzeroK : (hzA : K) = 0 := congrArg Subtype.val hzero
        dsimp [hzA] at hzeroK
        exact hz0 (by rw [hzeroK, map_zero])
      · have hz1' : v z⁻¹ ≠ 1 := by
          intro h
          apply hz1
          have hinv : (v z)⁻¹ = 1 := by simpa [v.map_inv] using h
          exact inv_eq_one.mp hinv
        have hzlt : v z⁻¹ < 1 := lt_of_le_of_ne hz hz1'
        let hzA : valuationRingOf v :=
          ⟨z⁻¹, (mem_valuationRingOf_iff v z⁻¹).2 hz⟩
        have hzm : hzA ∈ maximalIdealOf v :=
          (mem_maximalIdealOf_iff v hzA).2 (by simpa [hzA] using hzlt)
        have hzbot : hzA ∈ (⊥ : Ideal (valuationRingOf v)) := by
          rw [← hbot]
          exact hzm
        have hzero : hzA = 0 := by simpa using hzbot
        have hzeroK : (hzA : K) = 0 := congrArg Subtype.val hzero
        dsimp [hzA] at hzeroK
        have hzzero : z = 0 := inv_eq_zero.mp hzeroK
        exact hz0 (by rw [hzzero, map_zero])
    · intro x hx
      have hradical_span :
          maximalIdealOf v ≤ Ideal.radical (Ideal.span ({x} : Set (valuationRingOf v))) := by
        by_cases hxM : x ∈ maximalIdealOf v
        · have hspan0 : Ideal.span ({x} : Set (valuationRingOf v)) ≠ ⊥ := by
            intro hzero
            apply hx
            have hxbot : x ∈ (⊥ : Ideal (valuationRingOf v)) := by
              rw [← hzero]
              exact Ideal.subset_span (by simp)
            simpa using hxbot
          have hspanTop : Ideal.span ({x} : Set (valuationRingOf v)) ≠ ⊤ := by
            intro htop
            have hunit : IsUnit x := Ideal.span_singleton_eq_top.mp htop
            have hxnot : x ∉ maximalIdealOf v := by
              intro hxmax
              have hxlt := (mem_maximalIdealOf_iff v x).mp hxmax
              have hxeq := (valuationRingOf_isUnit_iff v x).mp hunit
              exact (ne_of_gt hxlt) hxeq.symm
            exact hxnot hxM
          rw [hradical_of_nonzero_proper _ hspan0 hspanTop]
        · have hunit : IsUnit x := by
            apply (valuationRingOf_isUnit_iff v x).2
            apply le_antisymm ((mem_valuationRingOf_iff v (x : K)).mp x.property)
            apply le_of_not_gt
            intro hxlt
            exact hxM ((mem_maximalIdealOf_iff v x).2 hxlt)
          have htop : Ideal.span ({x} : Set (valuationRingOf v)) = ⊤ :=
            Ideal.span_singleton_eq_top.mpr hunit
          rw [htop, Ideal.radical_top]
          exact le_top
      exact hradical_span
  · intro hdim
    have harch : MulArchimedean
        (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
      by_contra hnotarch
      obtain ⟨P, hP, hP0, hPmax⟩ :=
        nonarch_valuation_has_intermediate_prime v hnotarch
      letI : Ring.KrullDimLE 1 (valuationRingOf v) := by
        apply Ring.krullDimLE_iff.mpr
        simpa [hdim]
      have hPm : P.IsMaximal := hP.isMaximal_of_ne_bot hP0
      have hPeq : P = maximalIdealOf v :=
        (maximalIdealOf_unique v P).mp hPm
      exact hPmax hPeq
    exact (isRankOneValuation_iff_archimedean_valueGroup v).2 harch

theorem rankOne_valuationRing_only_prime_ideals
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (hnontrivial : v.IsNontrivial) (P : Ideal (valuationRingOf v))
    (hP : P.IsPrime) :
    P = ⊥ ∨ P = maximalIdealOf v := by
  exact rankOne_prime_bot_or_maximal v hrank P hP

theorem rankOne_nonzero_proper_ideal_radical
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (hnontrivial : v.IsNontrivial) (I : Ideal (valuationRingOf v))
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    Ideal.radical I = maximalIdealOf v := by
  classical
  letI : v.IsNontrivial := hnontrivial
  have hle : Ideal.radical I ≤ maximalIdealOf v := by
    apply (Ideal.IsPrime.radical_le_iff
      (IsLocalRing.maximalIdeal.isMaximal (valuationRingOf v)).isPrime).2
    exact IsLocalRing.le_maximalIdeal hItop
  have hge : maximalIdealOf v ≤ Ideal.radical I := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf (fun J hJ => ?_)
    rcases rankOne_prime_bot_or_maximal v hrank J hJ.2 with hbot | hmax
    · exfalso
      apply hI0
      apply le_antisymm
      · simpa [hbot] using hJ.1
      · exact bot_le
    · simpa [hmax]
  exact le_antisymm hle hge

theorem rankOne_power_divisibility
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hrank : IsRankOneValuation v)
    (a b : valuationRingOf v) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_m : a ∈ maximalIdealOf v) (hb_m : b ∈ maximalIdealOf v) :
    ∃ n : ℕ, v ((a : K) ^ n) ≤ v (b : K) ∧
      a ^ n ∈ Ideal.span ({b} : Set (valuationRingOf v)) := by
  classical
  letI : v.IsNontrivial := by
    exact hrank.some.toIsNontrivial
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
    exact (isRankOneValuation_iff_archimedean_valueGroup v).mp hrank
  letI : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := harch
  have hav : v (a : K) < 1 := (mem_maximalIdealOf_iff v a).mp ha_m
  have hbv : 0 < v.restrict (b : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr (by
      intro hzero
      apply hb
      exact Subtype.ext hzero)
  have havpos : 0 < v.restrict (a : K) := by
    rw [Valuation.restrict_pos_iff]
    exact v.pos_iff.mpr (by
      exact fun hzero => ha (Subtype.ext hzero))
  have havR : v.restrict (a : K) < 1 := by
    rw [Valuation.restrict_lt_one_iff]
    exact hav
  have havinv : 1 < (v.restrict (a : K))⁻¹ := (one_lt_inv₀ havpos).2 havR
  obtain ⟨n, hn⟩ := harch.arch (v.restrict (b : K))⁻¹ havinv
  have hpowR : (v.restrict (a : K)) ^ n ≤ v.restrict (b : K) := by
    apply (inv_le_inv₀ hbv (pow_pos havpos n)).mp
    simpa [inv_pow] using hn
  have hpow : v ((a : K) ^ n) ≤ v (b : K) := by
    rw [← Valuation.restrict_le_iff]
    simpa [v.map_pow] using hpowR
  have hdiv : v ((a : K) ^ n / (b : K)) ≤ 1 := by
    rw [v.map_div, div_le_iff₀ (v.pos_iff.mpr (by
      intro hzero
      apply hb
      exact Subtype.ext hzero))]
    simpa using hpow
  let c : valuationRingOf v :=
    ⟨(a : K) ^ n / (b : K), (mem_valuationRingOf_iff v _).2 hdiv⟩
  have hcb : (c : K) * (b : K) = (a : K) ^ n := by
    dsimp [c]
    field_simp [hb]
  refine ⟨n, hpow, ?_⟩
  exact Ideal.mem_span_singleton'.mpr ⟨c, by
    apply Subtype.ext
    exact hcb⟩

/- The two-scale lexicographic example. -/

abbrev LexicographicIntegerPair := Lex (ℤ × ℤ)

instance : IsOrderedAddMonoid LexicographicIntegerPair where
  add_le_add_left a b hab c := by
    rw [Prod.Lex.le_iff] at hab ⊢
    rcases hab with hab | ⟨hfirst, hsecond⟩
    · apply Or.inl
      change (ofLex a).1 + (ofLex c).1 < (ofLex b).1 + (ofLex c).1
      simpa [add_comm] using add_lt_add_right hab (ofLex c).1
    · apply Or.inr
      constructor
      · change (ofLex a).1 + (ofLex c).1 = (ofLex b).1 + (ofLex c).1
        exact congrArg (fun x => x + (ofLex c).1) hfirst
      · change (ofLex a).2 + (ofLex c).2 ≤ (ofLex b).2 + (ofLex c).2
        simpa [add_comm] using add_le_add_right hsecond (ofLex c).2

def lexicographicPair (a b : ℤ) : LexicographicIntegerPair :=
  toLex (a, b)

def lexicographicInfinitesimal (n : ℕ) : LexicographicIntegerPair :=
  lexicographicPair 0 n

def lexicographicDominant : LexicographicIntegerPair :=
  lexicographicPair 1 0

theorem lexicographic_infinitesimals_are_all_below_dominant (n : ℕ) :
    lexicographicInfinitesimal n < lexicographicDominant := by
  change Prod.Lex (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
    (0, (n : ℤ)) (1, 0)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by norm_num))

def ChapterArchimedean (A : Type*) [AddCommGroup A] [LinearOrder A] : Prop :=
  ∀ a b : A, 0 < a → 0 < b → ∃ n : ℕ, b ≤ n • a

theorem lexicographic_integer_pair_is_not_archimedean :
    ¬ ChapterArchimedean LexicographicIntegerPair := by
  intro h
  have ha : (0 : LexicographicIntegerPair) <
      lexicographicPair (0 : ℤ) (1 : ℤ) := by
    change Prod.Lex (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
      (0, 0) (0, 1)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by norm_num⟩)
  have hb : (0 : LexicographicIntegerPair) <
      lexicographicPair (1 : ℤ) (0 : ℤ) := by
    change Prod.Lex (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
      (0, 0) (1, 0)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by norm_num))
  obtain ⟨n, hn⟩ := h (lexicographicPair (0 : ℤ) (1 : ℤ))
      (lexicographicPair (1 : ℤ) (0 : ℤ)) ha hb
  have hn' : lexicographicPair (1 : ℤ) (0 : ℤ) ≤
      n • lexicographicPair (0 : ℤ) (1 : ℤ) := hn
  have hnsmul : n • lexicographicPair (0 : ℤ) (1 : ℤ) =
      lexicographicPair (0 : ℤ) (n : ℤ) := by
    clear hn hn'
    induction n with
    | zero =>
        change (0, (0 : ℤ)) = (0, (0 : ℤ))
        rfl
    | succ n ih =>
        rw [succ_nsmul, ih]
        change (0, (n : ℤ) + 1) = (0, (n.succ : ℤ))
        simp
  rw [hnsmul] at hn'
  have hlex := (Prod.Lex.toLex_le_toLex.mp hn')
  have : False := by
    rcases hlex with hfirst | ⟨heq, _⟩ <;> omega
  exact this

theorem lexicographic_two_scale_has_intermediate_prime
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative LexicographicIntegerPair)))
    (hsurj : Function.Surjective v) :
    ∃ P : Ideal (valuationRingOf v), P.IsPrime ∧ P ≠ ⊥ ∧
      P ≠ maximalIdealOf v := by
  classical
  have htarget_not : ¬ MulArchimedean
      (WithZero (Multiplicative LexicographicIntegerPair)) := by
    intro htarget
    have hpair : ∀ n : ℕ, ¬ lexicographicPair (1 : ℤ) (0 : ℤ) ≤
        n • lexicographicPair (0 : ℤ) (1 : ℤ) := by
      intro n hn
      have hnsmul : n • lexicographicPair (0 : ℤ) (1 : ℤ) =
          lexicographicPair (0 : ℤ) (n : ℤ) := by
        clear hn
        induction n with
        | zero =>
            change (0, (0 : ℤ)) = (0, (0 : ℤ))
            rfl
        | succ n ih =>
            rw [succ_nsmul, ih]
            change (0, (n : ℤ) + 1) = (0, (n.succ : ℤ))
            simp
      rw [hnsmul] at hn
      rcases Prod.Lex.toLex_le_toLex.mp hn with hfirst | ⟨heq, _⟩ <;> omega
    let X : WithZero (Multiplicative LexicographicIntegerPair) :=
      WithZero.exp (lexicographicPair (1 : ℤ) (0 : ℤ))
    let Y : WithZero (Multiplicative LexicographicIntegerPair) :=
      WithZero.exp (lexicographicPair (0 : ℤ) (1 : ℤ))
    have hsmall : (0 : LexicographicIntegerPair) <
        lexicographicPair (0 : ℤ) (1 : ℤ) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, by norm_num⟩)
    have hY : 1 < Y := by
      dsimp [Y]
      rw [← WithZero.exp_zero]
      change (↑(Multiplicative.ofAdd (0 : LexicographicIntegerPair)) :
        WithZero (Multiplicative LexicographicIntegerPair)) <
        ↑(Multiplicative.ofAdd (lexicographicPair (0 : ℤ) (1 : ℤ)))
      exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr hsmall)
    obtain ⟨n, hn⟩ := htarget.arch X hY
    dsimp [X, Y] at hn
    change (↑(Multiplicative.ofAdd (lexicographicPair (1 : ℤ) (0 : ℤ))) :
        WithZero (Multiplicative LexicographicIntegerPair)) ≤
        ↑(Multiplicative.ofAdd (n • lexicographicPair (0 : ℤ) (1 : ℤ))) at hn
    apply hpair n
    exact Multiplicative.ofAdd_le.mp (WithZero.coe_le_coe.mp hn)
  have hgroup_not : ¬ MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v)) := by
    intro hgroup
    apply htarget_not
    exact ⟨by
      intro x y hy
      obtain ⟨a, ha⟩ := hsurj x
      obtain ⟨b, hb⟩ := hsurj y
      have hvb : 1 < v b := by simpa [hb] using hy
      have hyR : 1 < v.restrict b := by
        apply lt_of_not_ge
        intro hle
        have hle' : v b ≤ 1 := by
          rw [← Valuation.restrict_le_one_iff]
          exact hle
        exact (not_le_of_gt hvb) hle'
      obtain ⟨n, hn⟩ := hgroup.arch (v.restrict a) hyR
      have hn' : v.restrict a ≤ v.restrict (b ^ n) := by
        simpa [v.restrict.map_pow] using hn
      have hn'' : v a ≤ v (b ^ n) :=
        (Valuation.restrict_le_iff (v := v)).mp hn'
      exact ⟨n, by simpa [ha, hb, v.map_pow] using hn''⟩⟩
  exact nonarch_valuation_has_intermediate_prime v hgroup_not

end PrimeIdealsAndRank

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter03
