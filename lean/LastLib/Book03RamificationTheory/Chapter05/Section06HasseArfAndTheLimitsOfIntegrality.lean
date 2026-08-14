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

/-- The canonical fixed field cut out by a character kernel. -/
abbrev chapter05CharacterKernelFixedField
    {K L C : Type*} [Field K] [Field L] [Algebra K L] [Group C]
    (χ : Gal(L / K) →* C) : IntermediateField K L :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField
    (MonoidHom.ker χ)

/-!
 A character-kernel package records the field-level quotient needed by the
 cyclic Hasse--Arf argument.  The transfer field is the source of the
 normalized fixed-field valuation and canonical quotient profile; the local
 quotient record supplies the exact interface expected by the cyclic lemma.
-/
structure Chapter05CharacterKernelHasseArfData
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    [FiniteDimensional K (chapter05CharacterKernelFixedField χ)]
    [IsGalois K (chapter05CharacterKernelFixedField χ)]
    [Finite (Gal(chapter05CharacterKernelFixedField χ / K))]
    [FiniteDimensional (chapter05CharacterKernelFixedField χ) L]
    [IsGalois (chapter05CharacterKernelFixedField χ) L]
    [Finite (Gal(L / chapter05CharacterKernelFixedField χ))] where
  character_surjective : Function.Surjective χ
  character_cyclic : IsCyclic C
  local_data : Chapter05LocalGaloisUpperData K L
  transfer :
    Chapter05FixedFieldSubextensionTransfer (MonoidHom.ker χ) local_data.profile
  /- The abstract quotient setup is the structural input for applying the
     quotient theorem to the character kernel.  It records a local-field
     realization and a profile transport, rather than assuming the upper
     compatibility that the quotient theorem is meant to prove. -/
  quotient_setup :
    Chapter05QuotientRamificationSetup (Gal(L / K)) (MonoidHom.ker χ)
  quotient_setup_upstairs_eq : quotient_setup.upstairs = local_data.profile
  quotient_local :
    Chapter05LocalGaloisUpperData K (chapter05CharacterKernelFixedField χ)
  quotient_galois_equiv :
    (Gal(L / K) ⧸ MonoidHom.ker χ) ≃*
      Gal(chapter05CharacterKernelFixedField χ / K)
  quotient_profile_transport :
    ∀ u : ℝ,
      quotient_local.profile.lowerGroup u =
        (quotient_setup.downstairs.lowerGroup u).map
          quotient_galois_equiv.toMonoidHom
  quotient_profile_eq : quotient_local.profile = transfer.quotient_profile
  quotient_base_valuation_eq : quotient_local.vK = transfer.vK
  quotient_extension_valuation_eq : quotient_local.vL = transfer.vM
  quotient_cyclic :
    IsCyclic (Gal(chapter05CharacterKernelFixedField χ / K))
  base_residue_perfect :
      PerfectField
      (IsLocalRing.ResidueField local_data.vK.toValuation.valuationSubring)
  quotient_residue_perfect :
    PerfectField
      (IsLocalRing.ResidueField quotient_local.vK.toValuation.valuationSubring)

theorem chapter05_character_kernel_upper_break_integer
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {v : ℝ}
    (hv : chapter05UpperBreak R.quotient_local.profile v) :
    chapter05UpperBreakIsInteger v := by
  sorry

/-!
 The actual order-`p²` specialization.  The surviving subgroup in the
 two-break tower and the character kernel need not be the same line in the
 elementary abelian quotient; the latter is required only to miss the former,
 so its cyclic quotient still detects the second upper break.
-/
theorem chapter05_character_kernel_detects_two_break_second_upper
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))] [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {H : Subgroup (Gal(L / K))} [H.Normal]
    (T : Chapter05TwoBreakTowerData (Gal(L / K)) H)
    (hprofile : R.local_data.profile = T.twoBreak.profile)
    (hsubgroup_not_le_kernel : ¬H ≤ MonoidHom.ker χ) :
    chapter05UpperBreak R.quotient_local.profile
      (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) := by
  sorry

theorem chapter05_perfect_residue_p_squared_two_break_second_upper_integral
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))] [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {H : Subgroup (Gal(L / K))} [H.Normal]
    (T : Chapter05TwoBreakTowerData (Gal(L / K)) H)
    (hprofile : R.local_data.profile = T.twoBreak.profile)
    (hsubgroup_not_le_kernel : ¬H ≤ MonoidHom.ker χ) :
    chapter05UpperBreakIsInteger
        (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) ∧
      T.twoBreak.p ∣ T.twoBreak.b - T.twoBreak.a := by
  sorry

/- The source's cyclic lemma is exposed separately so the abelian theorem can
   reduce to cyclic quotients without hiding the integrality input in its
   conclusion. -/
theorem chapter05_cyclic_hasse_arf_lemma
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (hcyclic : IsCyclic (Gal(L / K)))
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {b : ℕ}
    (hlast : ∀ n : ℕ, b < n →
      D.profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      D.profile.lowerGroup (b : ℝ) ≠
        D.profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : D.profile.lowerGroup 0 = ⊤) :
    ∃ z : ℤ, (z : ℚ) = chapter05CyclicHasseArfSum D.profile b := by
  sorry

/-- The fixed-field transfer supplies the local quotient input for the cyclic
 Hasse--Arf lemma on a character-kernel quotient. -/
theorem chapter05_character_kernel_cyclic_hasse_arf
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {b : ℕ}
    (hlast : ∀ n : ℕ, b < n →
      R.quotient_local.profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      R.quotient_local.profile.lowerGroup (b : ℝ) ≠
        R.quotient_local.profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : R.quotient_local.profile.lowerGroup 0 = ⊤) :
    ∃ z : ℤ,
      (z : ℚ) = chapter05CyclicHasseArfSum R.quotient_local.profile b := by
  sorry

/-- The Hasse--Arf theorem in the local field interface of this chapter. -/
theorem chapter05_hasse_arf
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    :
    chapter05AllUpperBreaksIntegral D.profile := by
  sorry

theorem chapter05_hasse_arf_upper_break_integer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {v : ℝ} (hv : chapter05UpperBreak D.profile v) :
    chapter05UpperBreakIsInteger v := by
  exact chapter05_hasse_arf D habelian v hv

/- The two-break discussion in the source specializes Hasse--Arf directly:
   for an actual order-`p^2` local Galois group, the second upper label is an
   upper break of the local profile, hence it is integral and the arithmetic
   characterization from Section 5.5 gives `p ∣ b - a`. -/
theorem chapter05_perfect_residue_p_squared_two_break_second_upper_integral_direct
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {H : Subgroup (Gal(L / K))} [H.Normal]
    (T : Chapter05TwoBreakTowerData (Gal(L / K)) H)
    (hprofile : D.profile = T.twoBreak.profile) :
    chapter05UpperBreakIsInteger
        (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) ∧
      T.twoBreak.p ∣ T.twoBreak.b - T.twoBreak.a := by
  sorry

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
  intro hAll
  rcases hfrac with ⟨v, hv, hnot⟩
  exact hnot (hAll v hv)

/- In the actual local-Galois interface, Hasse--Arf gives the sharper
   contrapositive: a fractional upper break rules out an abelian Galois group
   under the same perfect-residue hypotheses. -/
theorem chapter05_fractional_upper_break_forces_nonabelian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    (hfrac : chapter05HasFractionalUpperBreak D.profile) :
    ¬ (∀ σ τ : Gal(L / K), σ * τ = τ * σ) := by
  intro habelian
  rcases hfrac with ⟨v, hv, hnot⟩
  exact hnot ((chapter05_hasse_arf D habelian) v hv)

end
end LastLib.Book03RamificationTheory.Chapter05
