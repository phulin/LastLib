import LastLib.Book03RamificationTheory.Chapter03.Section06MixedUnramifiedTameExtension
import LastLib.Book03RamificationTheory.Chapter05.Section03TowerTransitivity
import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula
import LastLib.Book03RamificationTheory.Chapter07.Section06TameAndWildDerivativeBounds
import LastLib.Book03RamificationTheory.Chapter08.Section01FromADualLatticeToAnIdealDownstairs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.DedekindDomain.Different

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open LastLib.Book03RamificationTheory.Chapter03
open LastLib.Book03RamificationTheory.Chapter07
open LastLib.Book03RamificationTheory.Chapter08
open Polynomial
open scoped BigOperators Polynomial

/-! Common book-facing interfaces for Chapter 9.  The lower and upper
    filtrations are the canonical Chapter 5 records; Chapter 9 only names the
    integer and real evaluations that occur in Hilbert's formula. -/

/- The canonical Chapter 5 filtration records eventual triviality as an
   existential rather than as a named cutoff.  Chapter 9's finite sums use a
   chosen witness to that existential. -/
noncomputable def chapter09Cutoff
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : ℕ :=
  Classical.choose D.lower_eventually_trivial

theorem chapter09_lower_group_trivial_at_cutoff
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    ∀ m : ℕ, chapter09Cutoff D ≤ m → D.lowerGroup (m : ℝ) = ⊥ := by
  exact Classical.choose_spec D.lower_eventually_trivial

abbrev chapter09ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField v.toValuation.valuationSubring

def chapter09LowerGroup
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (i : ℕ) : Subgroup G :=
  D.lowerGroup (i : ℝ)

@[simp] theorem chapter09_lower_group_apply
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (i : ℕ) :
    chapter09LowerGroup D i = D.lowerGroup (i : ℝ) :=
  rfl

/- The lower-numbered shape of the mixed unramified--tame example from
   Chapter 3.  The residue degree is invisible to this group profile; it
   reappears only when the different is normed downstairs. -/
def chapter09MixedUnramifiedTameProfile
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) : Prop :=
  Nat.card (chapter09LowerGroup D 0) = e ∧
    chapter09LowerGroup D 1 = ⊥

theorem chapter09_lower_group_mem_iff
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    {σ : G} (hσ : σ ≠ 1) (i : ℕ) :
    σ ∈ chapter09LowerGroup D i ↔ i + 1 ≤ D.displacement σ := by
  exact D.lower_nat_mem_iff hσ i

theorem chapter09_lower_group_succ_le
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (i : ℕ) :
    chapter09LowerGroup D (i + 1) ≤ chapter09LowerGroup D i := by
  apply D.lower_antitone
  norm_num

def chapter09UpperGroup
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Subgroup G :=
  chapter05UpperRamificationGroup D v

@[simp] theorem chapter09_upper_group_apply
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) :
    chapter09UpperGroup D v = chapter05UpperRamificationGroup D v :=
  rfl

theorem chapter09_upper_group_eq_lower_at_inverse
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (_hbij : Function.Bijective (chapter05HerbrandFunction D))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter09UpperGroup D v =
      D.lowerGroup (chapter05HerbrandInverse D v) := by
  exact chapter05_upper_group_eq_lower_at_inverse D hv

theorem chapter09_upper_group_zero_eq_lower_zero
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter09UpperGroup D 0 = D.lowerGroup 0 := by
  exact chapter05_upper_group_zero_eq_lower_zero D hbij

theorem chapter09_upper_zero_plus_eq_lower_one
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperZeroPlus D = D.lowerGroup 1 := by
  exact chapter05_upper_zero_plus_eq_lower_one D hbij

noncomputable def chapter09DisplacementSum
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) : ℕ := by
  classical
  exact Finset.sum (Finset.univ.erase (1 : G)) D.displacement

noncomputable def chapter09GroupCountSum
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (D : Chapter05RamificationFiltration G) : ℕ := by
  classical
  exact Finset.sum (Finset.range (chapter09Cutoff D + 1))
    (fun i => Nat.card (chapter09LowerGroup D i) - 1)

def chapter09DifferentPower
    {B : Type*} [CommRing B]
    (mB D : Ideal B) (d : ℕ) : Prop :=
  D = mB ^ d

noncomputable def chapter09DifferentExponent
    {B : Type*} [CommRing B]
    (mB D : Ideal B)
    (hD : ∃! d : ℕ, chapter09DifferentPower mB D d) : ℕ :=
  Classical.choose hD

theorem chapter09DifferentExponent_spec
    {B : Type*} [CommRing B]
    (mB D : Ideal B)
    (hD : ∃! d : ℕ, chapter09DifferentPower mB D d) :
    chapter09DifferentPower mB D (chapter09DifferentExponent mB D hD) := by
  exact (Classical.choose_spec hD).1

theorem chapter09DifferentPower_iff
    {B : Type*} [CommRing B]
    (mB D : Ideal B) (d : ℕ) :
    chapter09DifferentPower mB D d ↔ D = mB ^ d :=
  Iff.rfl

/- The exact local hypotheses used by the classical formula.  No finiteness of
   the residue fields and no characteristic-zero assumption occur here. -/
structure Chapter09LocalGaloisData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Finite (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)] where
  valuation_extension :
    vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)
  base_rank_one_discrete : Valuation.IsRankOneDiscrete vK.toValuation
  extension_rank_one_discrete : Valuation.IsRankOneDiscrete vL.toValuation
  base_complete :
    IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring
  extension_complete :
    IsAdicComplete
      (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring)
      vL.toValuation.valuationSubring
  unique_normalized_extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
      vK.toValuation vL.toValuation
  residue_separable :
    Algebra.IsSeparable (chapter09ResidueField vK) (chapter09ResidueField vL)

noncomputable def chapter09ConjugateProductPolynomial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype (Gal(L / K))] (α : L) : L[X] := by
  classical
  exact ∏ σ : Gal(L / K), (X - C (σ α))

/- A generator/derivative certificate.  Its fields are independent inputs to
   the formula: monogenicity, the different ideal's power, the conjugate
   factorization, and the displacement calculation. -/
structure Chapter09HilbertFormulaSetup
    (A B K L : Type*)
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
      (chapter09ResidueField vL)] where
  local_data : Chapter09LocalGaloisData K L vK vL
  base_ring_is_valuation_ring :
    Nonempty (A ≃+* vK.toValuation.valuationSubring)
  extension_ring_is_valuation_ring :
    Nonempty (B ≃+* vL.toValuation.valuationSubring)
  profile : Chapter05RamificationFiltration (Gal(L / K))
  profile_canonical :
    ∀ i : ℕ,
      profile.lowerGroup (i : ℝ) =
        chapter05RamificationGroupInG
          (F := K) vL.toValuation.valuationSubring i
  α : B
  f : A[X]
  d : ℕ
  monogenic : chapter07MonogenicPresentation A B K L α f
  different_power :
    chapter08DifferentIdeal A B =
      (IsLocalRing.maximalIdeal B) ^ d
  different_power_unique :
    ∃! n : ℕ,
      chapter08DifferentIdeal A B =
        (IsLocalRing.maximalIdeal B) ^ n
  /- LOCAL_DEPENDENCY_GUESS: the preceding different chapter supplies the
     valuation realization of the different exponent for the chosen integral
     generator.  It is kept as a bridge, not as a Hilbert-sum conclusion. -/
  different_derivative_value :
    vL (algebraMap B L (chapter07DerivativeAt A B f α)) =
      (d : WithTop ℤ)
  conjugate_factorization :
    f.map (algebraMap A L) =
      chapter09ConjugateProductPolynomial (K := K) (L := L)
        (algebraMap B L α)
  displacement_formula :
    ∀ {σ : Gal(L / K)}, σ ≠ 1 →
      vL (σ (algebraMap B L α) - algebraMap B L α) =
        (profile.displacement σ : WithTop ℤ)
  orbit_separates :
    ∀ {σ : Gal(L / K)},
      σ (algebraMap B L α) = algebraMap B L α → σ = 1

end

end LastLib.Book03RamificationTheory.Chapter09
