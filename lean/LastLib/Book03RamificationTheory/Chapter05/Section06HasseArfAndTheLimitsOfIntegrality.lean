import LastLib.Book03RamificationTheory.Chapter05.Section05ATwoBreakTower
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped BigOperators

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

/- Chapter 4 uses a separate integer-profile interface, while this chapter
   needs its real, left-continuous extension together with the local valuation
   hypotheses used by Hasse--Arf.  This structure is therefore a local bridge,
   and its canonical field points directly to the Book 2 congruence groups. -/
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
  extension_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring)
      vL.toValuation.valuationSubring
  /- Valuation extensions are unique up to valuation equivalence.  Requiring
     literal equality of every equivalent `WithTop ℤ`-valued valuation would
     impose an extra normalization not supplied by the local-field
     hypotheses. -/
  unique_valuation_extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension
      vK.toValuation vL.toValuation
  decomposition_top :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K vL.toValuation.valuationSubring = ⊤
  profile : Chapter05RamificationFiltration (Gal(L / K))
  lower_canonical :
    ∀ n : ℕ,
      profile.lowerGroup (n : ℝ) =
        chapter05RamificationGroupInG (F := K)
          vL.toValuation.valuationSubring (n + 1)

namespace Chapter05LocalGaloisUpperData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]

theorem lower_canonical_at
    (D : Chapter05LocalGaloisUpperData K L) (n : ℕ) :
    D.profile.lowerGroup (n : ℝ) =
      chapter05RamificationGroupInG (F := K)
        D.vL.toValuation.valuationSubring (n + 1) := by
  exact D.lower_canonical n

end Chapter05LocalGaloisUpperData

/-- The normalized lower-group sum in the cyclic Hasse--Arf lemma. -/
def chapter05CyclicHasseArfSum
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (b : ℕ) : ℚ :=
  (Finset.sum (Finset.Icc 1 b)
      (fun i => (Nat.card (D.lowerGroup (i : ℝ)) : ℚ))) /
    (Nat.card (D.lowerGroup 0) : ℚ)

/- The source's cyclic lemma is exposed separately so the abelian theorem can
   reduce to cyclic quotients without hiding the integrality input in its
   conclusion. -/
theorem chapter05_cyclic_hasse_arf_lemma
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (hcyclic : IsCyclic (Gal(L / K)))
    [Algebra (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring)]
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    (hresidue_separable :
      Algebra.IsSeparable
        (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
        (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring))
    {b : ℕ}
    (hlast : ∀ n : ℕ, b < n →
      D.profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      D.profile.lowerGroup (b : ℝ) ≠
        D.profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : D.profile.lowerGroup 0 = ⊤) :
    ∃ z : ℤ, (z : ℚ) = chapter05CyclicHasseArfSum D.profile b := by
  sorry

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

/- In the actual local-Galois interface, Hasse--Arf gives the sharper
   contrapositive: a fractional upper break rules out an abelian Galois group
   under the same perfect-residue hypotheses. -/
theorem chapter05_fractional_upper_break_forces_nonabelian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    [Algebra (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring)]
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    (hresidue_separable :
      Algebra.IsSeparable
        (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)
        (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring))
    (hfrac : chapter05HasFractionalUpperBreak D.profile) :
    ¬ (∀ σ τ : Gal(L / K), σ * τ = τ * σ) := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter05
