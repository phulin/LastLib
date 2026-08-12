import LastLib.Book03RamificationTheory.Chapter05.Section05ATwoBreakTower
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

/-! ## 5.6. Hasse--Arf and the limits of integrality -/

/-- Perfectness of the residue field attached to a normalized additive valuation. -/
def chapter05PerfectResidueField
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  PerfectField (IsLocalRing.ResidueField v.toValuation.valuationSubring)

/-- Every upper break of a profile is integral. -/
def chapter05AllUpperBreaksIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  ∀ v : ℝ, chapter05UpperBreak D v → chapter05UpperBreakIsInteger v

/- LOCAL_DEPENDENCY_GUESS: The current checkout has no Book 3 Chapter 4
   module exposing the canonical lower profile.  This structure is the local
   bridge expected to be replaced by that earlier declaration in the global
   fixup pass.  Its `lower_canonical` field identifies the integer profile
   with the Book 2 congruence groups and does not assume any upper conclusion. -/
structure Chapter05LocalGaloisUpperData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))] where
  vK : AddValuation K (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  vK_rank_one_discrete : Valuation.IsRankOneDiscrete vK.toValuation
  vL_rank_one_discrete : Valuation.IsRankOneDiscrete vL.toValuation
  restriction :
    vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)
  base_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring
  unique_normalized_extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
      vK.toValuation vL.toValuation
  decomposition_top :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K vL.toValuation.valuationSubring = ⊤
  profile : Chapter05RamificationFiltration (Gal(L / K))
  lower_canonical :
    ∀ n : ℕ,
      profile.lowerGroup (n : ℝ) =
        chapter05RamificationGroupInG (F := K)
          vL.toValuation.valuationSubring n

namespace Chapter05LocalGaloisUpperData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]

theorem lower_canonical_at
    (D : Chapter05LocalGaloisUpperData K L) (n : ℕ) :
    D.profile.lowerGroup (n : ℝ) =
      chapter05RamificationGroupInG (F := K)
        D.vL.toValuation.valuationSubring n := by
  exact D.lower_canonical n

end Chapter05LocalGaloisUpperData

/-- The Hasse--Arf theorem in the local field interface of this chapter. -/
theorem chapter05_hasse_arf
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [Algebra (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring)]
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    (hresidue_separable :
      Algebra.IsSeparable
        (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
        (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring)) :
    chapter05AllUpperBreaksIntegral D.profile := by
  sorry

theorem chapter05_hasse_arf_upper_break_integer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [Algebra (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring)]
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    (hresidue_separable :
      Algebra.IsSeparable
        (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
        (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring))
    {v : ℝ} (hv : chapter05UpperBreak D.profile v) :
    chapter05UpperBreakIsInteger v := by
  exact chapter05_hasse_arf D habelian hresidue_separable v hv

/-- The boundary predicate for a fractional upper break in the nonabelian case. -/
def chapter05HasFractionalUpperBreak
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  ∃ v : ℝ, chapter05UpperBreak D v ∧ ¬chapter05UpperBreakIsInteger v

/-
 The theorem above has exactly the classical hypotheses: no finiteness of the
 residue field is present, while perfection of the residue field and
 commutativity of the finite Galois group are explicit.  The predicate
 `chapter05HasFractionalUpperBreak` is intentionally not ruled out for a
 nonabelian profile; this is the limit of the integrality statement.
-/
theorem chapter05_hasse_arf_does_not_assert_nonabelian_integrality
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hfrac : chapter05HasFractionalUpperBreak D) :
    ¬chapter05AllUpperBreaksIntegral D := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter05
