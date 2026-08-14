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
  sorry

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
  sorry

theorem chapter09_wild_excess_nonnegative
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) :
    0 ≤ chapter09WildExcess D := by
  exact Nat.zero_le _

theorem chapter09_wild_excess_vanishes_iff
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) :
    chapter09WildExcess D = 0 ↔ chapter09LowerGroup D 1 = ⊥ := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem chapter09_wild_kummer_derivative_value
    (p : ℕ) (hp : Nat.Prime p)
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (α : L)
    (hvalp : vL (algebraMap K L (p : K)) =
      (p * (p - 1) : WithTop ℤ))
    (hvalpha : vL α = (1 : WithTop ℤ)) :
    vL (algebraMap K L (p : K) * α ^ (p - 1)) =
      (p ^ 2 - 1 : WithTop ℤ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter09
