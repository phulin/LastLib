import LastLib.Book03RamificationTheory.Chapter09.Section02ProofByAWellChosenGenerator

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open LastLib.Book03RamificationTheory.Chapter03
open LastLib.Book03RamificationTheory.Chapter08
open scoped BigOperators

/-! ## 9.3. Tame and wild parts of the different -/

def chapter09RamificationIndex
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℕ :=
  Nat.card (chapter09LowerGroup D 0)

def chapter09TameBaseline
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℕ :=
  chapter09RamificationIndex D - 1

def chapter09WildExcess
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) : ℕ := by
  classical
  exact Finset.sum (Finset.Ico 1 (chapter09Cutoff D + 1))
    (fun i => Nat.card (chapter09LowerGroup D i) - 1)

def chapter09IsTame
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  chapter09LowerGroup D 1 = ⊥

theorem chapter09_tame_baseline_eq_inertia_card_sub_one
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter09TameBaseline D =
      Nat.card (chapter09LowerGroup D 0) - 1 :=
  rfl

theorem chapter09_different_decomposes_into_tame_and_wild
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d : ℕ)
    (hformula : d = chapter09GroupCountSum D) :
    d = chapter09TameBaseline D + chapter09WildExcess D := by
  rw [hformula]
  unfold chapter09GroupCountSum chapter09TameBaseline chapter09RamificationIndex
    chapter09WildExcess
  rw [← Finset.sum_range_add_sum_Ico
    (fun i : ℕ => Nat.card (chapter09LowerGroup D i) - 1)
    (Nat.le_add_left 1 (chapter09Cutoff D))]
  simp

theorem chapter09_different_decomposes_for_hilbert_setup
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL) :
    S.d = chapter09TameBaseline S.profile + chapter09WildExcess S.profile := by
  apply chapter09_different_decomposes_into_tame_and_wild
  exact (chapter09_hilbert_different_formula_group_counts vK vL S)

/- The norm formula turns the actual downstairs discriminant exponent into
   the Chapter 3 mixed-profile value.  The ideal-power hypotheses expose the
   canonical Chapter 8 discriminant/different and residue-norm interface. -/
theorem chapter09_mixed_unramified_tame_discriminant_exponent
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [IsGalois K L]
    [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL)
    (e f δ : ℕ)
    (hprofile : chapter09MixedUnramifiedTameProfile S.profile e)
    (hdisc :
      chapter08RelativeDiscriminantIdeal A B =
        (IsLocalRing.maximalIdeal A) ^ δ)
    (hnorm :
      Ideal.relNorm A (IsLocalRing.maximalIdeal B) =
        (IsLocalRing.maximalIdeal A) ^ f)
    (hδunique : ∃! n : ℕ,
      chapter08RelativeDiscriminantIdeal A B =
        (IsLocalRing.maximalIdeal A) ^ n) :
    δ = chapter03MixedDiscriminantExponent e f := by
  have hd : δ = f * S.d :=
    chapter08_discriminant_exponent_eq_residue_degree_mul_different
      A B K L (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
      f S.d δ hdisc S.different_power hnorm hδunique
  have hS : S.d = chapter03MixedDifferentExponent e :=
    chapter09_mixed_unramified_tame_different_exponent vK vL S e hprofile
  calc
    δ = f * S.d := hd
    _ = f * chapter03MixedDifferentExponent e := by rw [hS]
    _ = chapter03MixedDiscriminantExponent e f := rfl

theorem chapter09_wild_excess_nonnegative
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) :
    0 ≤ chapter09WildExcess D := by
  exact Nat.zero_le _

theorem chapter09_wild_excess_vanishes_iff
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) :
    chapter09WildExcess D = 0 ↔ chapter09LowerGroup D 1 = ⊥ := by
  classical
  unfold chapter09WildExcess
  constructor
  · intro hzero
    by_cases hcut : chapter09Cutoff D = 0
    · exact chapter09_lower_group_trivial_at_cutoff D 1 (by omega)
    · have hcutpos : 1 ≤ chapter09Cutoff D := Nat.one_le_iff_ne_zero.mpr hcut
      have hone : 1 ∈ Finset.Ico 1 (chapter09Cutoff D + 1) := by
        simp only [Finset.mem_Ico]
        omega
      have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _hi => Nat.zero_le
            (Nat.card (chapter09LowerGroup D i) - 1))).mp hzero 1 hone
      have hcard_le : Nat.card (chapter09LowerGroup D 1) ≤ 1 :=
        Nat.sub_eq_zero_iff_le.mp hterm
      exact (chapter09LowerGroup D 1).eq_bot_of_card_le hcard_le
  · intro hbot
    apply Finset.sum_eq_zero
    intro i hi
    have hi_one : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hle : D.lowerGroup (i : ℝ) ≤ D.lowerGroup (1 : ℝ) := by
      apply D.lower_antitone
      exact_mod_cast hi_one
    have hbot_i : chapter09LowerGroup D i = ⊥ := by
      change D.lowerGroup (i : ℝ) = ⊥
      apply le_antisymm
      · rw [← hbot]
        simpa [chapter09LowerGroup] using hle
      · exact bot_le
    rw [hbot_i]
    simp

theorem chapter09_tame_iff_wild_group_trivial
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter09IsTame D ↔ chapter09LowerGroup D 1 = ⊥ :=
  Iff.rfl

theorem chapter09_wild_excess_zero_iff_tame
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) :
    chapter09WildExcess D = 0 ↔ chapter09IsTame D := by
  exact (chapter09_wild_excess_vanishes_iff D).trans
    (chapter09_tame_iff_wild_group_trivial D).symm

theorem chapter09_residue_separable_inertia_card_eq_e
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (e : ℕ)
    (he : e = chapter09RamificationIndex D) :
    Nat.card (chapter09LowerGroup D 0) = e := by
  exact he.symm

def chapter09SingleBreakProfile
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (p m : ℕ) : Prop :=
  Nat.Prime p ∧
    Nat.card (chapter09LowerGroup D 0) = p ∧
    (∀ i : ℕ, i ≤ m → Nat.card (chapter09LowerGroup D i) = p) ∧
    (∀ i : ℕ, m < i → chapter09LowerGroup D i = ⊥)

theorem chapter09_single_break_profile_different_exponent
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (p m d : ℕ)
    (hprofile : chapter09SingleBreakProfile D p m)
    (hformula : d = chapter09GroupCountSum D) :
    d = (m + 1) * (p - 1) := by
  have hcut : m ≤ chapter09Cutoff D := by
    by_contra hnot
    have hlt : chapter09Cutoff D < m := Nat.lt_of_not_ge hnot
    have hle : chapter09Cutoff D ≤ m := Nat.le_of_lt hlt
    have hcard : Nat.card (chapter09LowerGroup D (chapter09Cutoff D)) = p :=
      hprofile.2.2.1 _ hle
    have hbot : chapter09LowerGroup D (chapter09Cutoff D) = ⊥ :=
      chapter09_lower_group_trivial_at_cutoff D (chapter09Cutoff D) le_rfl
    have hpone : p = 1 := by
      calc
        p = Nat.card (chapter09LowerGroup D (chapter09Cutoff D)) := hcard.symm
        _ = Nat.card (⊥ : Subgroup G) := by rw [hbot]
        _ = 1 := Subgroup.card_bot
    have hpge : 2 ≤ p := (show Nat.Prime p from hprofile.1).two_le
    omega
  rw [hformula]
  unfold chapter09GroupCountSum
  have hmain :
    Finset.sum (Finset.range (m + 1))
          (fun i => Nat.card (chapter09LowerGroup D i) - 1) =
        (m + 1) * (p - 1) := by
    calc
      Finset.sum (Finset.range (m + 1))
          (fun i => Nat.card (chapter09LowerGroup D i) - 1) =
          Finset.sum (Finset.range (m + 1)) (fun _ => p - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_le : i ≤ m := by
          have hi' : i < m + 1 := Finset.mem_range.mp hi
          omega
        rw [hprofile.2.2.1 i hi_le]
      _ = (m + 1) * (p - 1) := by simp
  have htail :
      Finset.sum (Finset.Ico (m + 1) (chapter09Cutoff D + 1))
          (fun i => Nat.card (chapter09LowerGroup D i) - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi_gt : m < i := by
      have hi' := (Finset.mem_Ico.mp hi).1
      omega
    rw [hprofile.2.2.2 i hi_gt]
    simp
  rw [← Finset.sum_range_add_sum_Ico
    (fun i : ℕ => Nat.card (chapter09LowerGroup D i) - 1)
    (by omega : m + 1 ≤ chapter09Cutoff D + 1), hmain, htail, add_zero]

def chapter09QuadraticTwoAdicProfile
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  Nat.card (chapter09LowerGroup D 0) = 2 ∧
    Nat.card (chapter09LowerGroup D 1) = 2 ∧
    Nat.card (chapter09LowerGroup D 2) = 2 ∧
    ∀ i : ℕ, 2 < i → chapter09LowerGroup D i = ⊥

theorem chapter09_quadratic_two_adic_different_exponent
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (d : ℕ)
    (hprofile : chapter09QuadraticTwoAdicProfile D)
    (hformula : d = chapter09GroupCountSum D) :
    d = 3 := by
  have hsingle : chapter09SingleBreakProfile D 2 2 := by
    refine ⟨by norm_num, hprofile.1, ?_, hprofile.2.2.2⟩
    intro i hi
    interval_cases i
    · exact hprofile.1
    · exact hprofile.2.1
    · exact hprofile.2.2.1
  have h := chapter09_single_break_profile_different_exponent D 2 2 d
    hsingle hformula
  norm_num at h
  exact h

def chapter09WildKummerProfile
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (p : ℕ) : Prop :=
  Nat.Prime p ∧
    (∀ i : ℕ, i ≤ p → Nat.card (chapter09LowerGroup D i) = p) ∧
    (∀ i : ℕ, p < i → chapter09LowerGroup D i = ⊥)

theorem chapter09_wild_kummer_different_exponent
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (p d : ℕ)
    (hprofile : chapter09WildKummerProfile D p)
    (hformula : d = chapter09GroupCountSum D) :
    d = p ^ 2 - 1 := by
  have hsingle : chapter09SingleBreakProfile D p p := by
    refine ⟨hprofile.1, ?_, hprofile.2.1, hprofile.2.2⟩
    exact hprofile.2.1 0 (by omega)
  have h := chapter09_single_break_profile_different_exponent D p p d
    hsingle hformula
  calc
    d = (p + 1) * (p - 1) := h
    _ = p ^ 2 - 1 := by
      have hpone : 1 ≤ p := hprofile.1.one_le
      have hmul : p * p = p * (p - 1) + p := by
        calc
          p * p = p * ((p - 1) + 1) := by rw [Nat.sub_add_cancel hpone]
          _ = p * (p - 1) + p := by simp [Nat.mul_add]
      rw [Nat.add_mul, one_mul, pow_two]
      omega

theorem chapter09_wild_kummer_derivative_value
    (p : ℕ) (hp : Nat.Prime p)
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (α : L)
    (hvalp : vL (algebraMap K L (p : K)) =
      (p * (p - 1) : WithTop ℤ))
    (hvalpha : vL α = (1 : WithTop ℤ)) :
    vL (algebraMap K L (p : K) * α ^ (p - 1)) =
      (p ^ 2 - 1 : WithTop ℤ) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, hvalp, hvalpha]
  have hcast : ((p - 1 : ℕ) : WithTop ℤ) = (p : WithTop ℤ) - 1 := by
    calc
      ((p - 1 : ℕ) : WithTop ℤ) = (((p - 1 : ℕ) : ℤ) : WithTop ℤ) := by norm_num
      _ = (((p : ℤ) - 1 : ℤ) : WithTop ℤ) := by
        congr 1
        rw [Nat.cast_sub hp.one_le]
        norm_num
      _ = ((p : ℤ) : WithTop ℤ) - ((1 : ℤ) : WithTop ℤ) :=
        (WithTop.LinearOrderedAddCommGroup.coe_sub (p : ℤ) (1 : ℤ)).symm
      _ = (p : WithTop ℤ) - 1 := by norm_num
  change ↑p * (↑p - 1) + (p - 1) • ((1 : ℤ) : WithTop ℤ) = ↑p ^ 2 - 1
  rw [← WithTop.coe_nsmul]
  norm_num [nsmul_eq_mul]
  rw [hcast]
  have hpcast : (p : WithTop ℤ) = ((p : ℤ) : WithTop ℤ) := by norm_num
  have hone : (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) := by norm_num
  rw [hpcast, hone]
  change (((p : ℤ) : WithTop ℤ) *
      (((p : ℤ) : WithTop ℤ) - ((1 : ℤ) : WithTop ℤ)) +
        (((p : ℤ) : WithTop ℤ) - ((1 : ℤ) : WithTop ℤ))) =
    (((p : ℤ) : WithTop ℤ) ^ 2 - ((1 : ℤ) : WithTop ℤ))
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub,
    ← WithTop.coe_mul, ← WithTop.coe_add, ← WithTop.coe_pow,
    ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  ring

end

end LastLib.Book03RamificationTheory.Chapter09
