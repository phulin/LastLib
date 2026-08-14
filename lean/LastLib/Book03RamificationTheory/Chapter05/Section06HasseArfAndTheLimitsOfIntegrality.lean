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

private theorem chapter05_nat_card_map_group_equiv
    {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (K : Subgroup G) (e : G ≃* G') :
    Nat.card (K.map e.toMonoidHom) = Nat.card K := by
  classical
  let f : K → K.map e.toMonoidHom := fun x =>
    ⟨e x, ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy
    · intro y
      rcases y.property with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

private theorem chapter05_upper_group_transport_of_profile
    {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (D : Chapter05RamificationFiltration G)
    (E : Chapter05RamificationFiltration G')
    (e : G ≃* G')
    (hprofile : ∀ u : ℝ,
      E.lowerGroup u = (D.lowerGroup u).map e.toMonoidHom)
    (hD : Function.Bijective (chapter05HerbrandFunction D))
    (hE : Function.Bijective (chapter05HerbrandFunction E))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup E v =
      (chapter05UpperRamificationGroup D v).map e.toMonoidHom := by
  have hcard (u : ℝ) :
      Nat.card (E.lowerGroup u) = Nat.card (D.lowerGroup u) := by
    rw [hprofile u]
    exact chapter05_nat_card_map_group_equiv _ e
  have hslope (u : ℝ) :
      chapter05HerbrandSlope E u = chapter05HerbrandSlope D u := by
    by_cases hu : u ≤ 0
    · simp [chapter05HerbrandSlope, hu]
    · rw [chapter05HerbrandSlope, if_neg hu,
        chapter05HerbrandSlope, if_neg hu, hcard u, hcard 0]
  have hfunction (u : ℝ) :
      chapter05HerbrandFunction E u = chapter05HerbrandFunction D u := by
    by_cases hu : u ≤ 0
    · simp [chapter05HerbrandFunction, hu]
    · rw [chapter05HerbrandFunction, if_neg hu,
        chapter05HerbrandFunction, if_neg hu]
      rw [show (fun t : ℝ => chapter05HerbrandSlope E t) =
          (fun t : ℝ => chapter05HerbrandSlope D t) by
        funext t
        exact hslope t]
  have hinverse (u : ℝ) :
      chapter05HerbrandInverse E u = chapter05HerbrandInverse D u := by
    apply hD.1
    calc
      chapter05HerbrandFunction D
          (chapter05HerbrandInverse E u) =
          chapter05HerbrandFunction E
            (chapter05HerbrandInverse E u) :=
        (hfunction _).symm
      _ = u := chapter05_herbrand_inverse_spec E hE u
      _ = chapter05HerbrandFunction D
          (chapter05HerbrandInverse D u) :=
        (chapter05_herbrand_inverse_spec D hD u).symm
  rw [chapter05_upper_group_eq_lower_at_inverse E hE hv,
    chapter05_upper_group_eq_lower_at_inverse D hD hv,
    hinverse]
  exact hprofile _

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
  classical
  let q := chapter05QuotientMap (MonoidHom.ker χ)
  let c : ℝ :=
    chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b
  have hcomp :
      (T.twoBreak.a : ℝ) < c ∧ c < (T.twoBreak.b : ℝ) := by
    simpa [c] using chapter05_two_break_upper_label_is_strictly_compressed
      T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_prime
        T.twoBreak.a_lt_b
  have hformula (x : ℝ) :
      chapter05HerbrandFunction T.twoBreak.profile x =
        chapter05TwoBreakHerbrand T.twoBreak.p T.twoBreak.a T.twoBreak.b x := by
    exact chapter05_two_break_herbrand_formula H T.twoBreak (volume := 0)
      (by
        intro a' b'
        exact (intervalIntegrable_iff).2
          (_root_.MeasureTheory.IntegrableOn.of_measure_zero (by simp))) x
  have hF_le_a {x : ℝ} (hx : x ≤ (T.twoBreak.a : ℝ)) :
      chapter05HerbrandFunction T.twoBreak.profile x = x := by
    rw [hformula]
    by_cases hx0 : x ≤ 0
    · simp [chapter05TwoBreakHerbrand, hx0]
    · simp [chapter05TwoBreakHerbrand, hx0, hx]
  have hF_mid {x : ℝ} (hxa : (T.twoBreak.a : ℝ) < x)
      (hxb : x ≤ (T.twoBreak.b : ℝ)) :
      chapter05HerbrandFunction T.twoBreak.profile x =
        (T.twoBreak.a : ℝ) +
          (x - (T.twoBreak.a : ℝ)) / (T.twoBreak.p : ℝ) := by
    rw [hformula]
    have hx0 : ¬x ≤ 0 := by
      have ha_pos : (0 : ℝ) < (T.twoBreak.a : ℝ) := by
        exact_mod_cast T.twoBreak.a_pos
      linarith
    simp [chapter05TwoBreakHerbrand, hx0, not_le.mpr hxa, hxb]
  have hF_gt {x : ℝ} (hxb : (T.twoBreak.b : ℝ) < x) :
      chapter05HerbrandFunction T.twoBreak.profile x =
        (T.twoBreak.a : ℝ) +
          ((T.twoBreak.b - T.twoBreak.a : ℕ) : ℝ) /
            (T.twoBreak.p : ℝ) +
          (x - (T.twoBreak.b : ℝ)) / (T.twoBreak.p : ℝ) ^ 2 := by
    rw [hformula]
    have hab : (T.twoBreak.a : ℝ) ≤ (T.twoBreak.b : ℝ) := by
      exact_mod_cast T.twoBreak.a_lt_b.le
    have hxa : ¬x ≤ (T.twoBreak.a : ℝ) := by linarith
    have hb_pos : (0 : ℝ) < (T.twoBreak.b : ℝ) := by
      exact lt_of_lt_of_le (by exact_mod_cast T.twoBreak.a_pos) hab
    have hx0 : ¬x ≤ 0 := by linarith
    simp [chapter05TwoBreakHerbrand, hx0, hxa, hxb]
  have hFb :
      chapter05HerbrandFunction T.twoBreak.profile (T.twoBreak.b : ℝ) = c := by
    have h := hF_mid (x := (T.twoBreak.b : ℝ))
      (by exact_mod_cast T.twoBreak.a_lt_b) le_rfl
    have hcast : ((T.twoBreak.b - T.twoBreak.a : ℕ) : ℝ) =
        (T.twoBreak.b : ℝ) - (T.twoBreak.a : ℝ) := by
      exact_mod_cast Nat.cast_sub T.twoBreak.a_lt_b.le
    simpa [c, chapter05TwoBreakSecondUpper, hcast] using h
  have hF_gt_c {x : ℝ} (hxb : (T.twoBreak.b : ℝ) < x) :
      c < chapter05HerbrandFunction T.twoBreak.profile x := by
    rw [hF_gt hxb]
    simp only [c, chapter05TwoBreakSecondUpper]
    have hp0 : (0 : ℝ) < (T.twoBreak.p : ℝ) := by
      exact_mod_cast T.twoBreak.p_prime.pos
    have hpos : 0 < (x - (T.twoBreak.b : ℝ)) /
        (T.twoBreak.p : ℝ) ^ 2 := by
      exact div_pos (sub_pos.mpr hxb) (sq_pos_of_pos hp0)
    linarith
  have hmono : StrictMonoOn
      (chapter05HerbrandFunction T.twoBreak.profile)
      (Set.Ici (-1 : ℝ)) :=
    (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
      T.twoBreak.profile).2.1
  have htop_bij :
      Function.Bijective (chapter05HerbrandFunction T.twoBreak.profile) :=
    chapter05_herbrand_bijective_of_filtration T.twoBreak.profile
  have hinv_domain {x : ℝ} (hx : (-1 : ℝ) ≤ x) :
      (-1 : ℝ) ≤ chapter05HerbrandInverse T.twoBreak.profile x := by
    by_contra hnot
    have hlt : chapter05HerbrandInverse T.twoBreak.profile x < (-1 : ℝ) :=
      lt_of_not_ge hnot
    have hidentity :=
      chapter05_herbrand_function_of_nonpositive T.twoBreak.profile (by linarith)
    have hspec := chapter05_herbrand_inverse_spec
      T.twoBreak.profile htop_bij x
    have hxeq : chapter05HerbrandInverse T.twoBreak.profile x = x :=
      hidentity.symm.trans hspec
    linarith
  have htop_upper_c :
      chapter05UpperRamificationGroup T.twoBreak.profile c = H := by
    have hc_dom : (-1 : ℝ) ≤ c := by linarith [hcomp.1]
    have hspec := chapter05_herbrand_inverse_spec
      T.twoBreak.profile htop_bij c
    have hψ_dom := hinv_domain hc_dom
    have hψ_gt_a : (T.twoBreak.a : ℝ) <
        chapter05HerbrandInverse T.twoBreak.profile c := by
      by_contra hnot
      have hψ_le := le_of_not_gt hnot
      have hfx := hF_le_a hψ_le
      linarith [hcomp.1]
    have hψ_le_b : chapter05HerbrandInverse T.twoBreak.profile c ≤
        (T.twoBreak.b : ℝ) := by
      by_contra hnot
      have hψ_gt := lt_of_not_ge hnot
      have hgtc := hF_gt_c hψ_gt
      linarith
    rw [chapter05UpperRamificationGroup, if_pos hc_dom,
      T.twoBreak.lower_second_layer _ hψ_gt_a hψ_le_b]
  have htop_upper_gt {w : ℝ} (hw : c < w) :
      chapter05UpperRamificationGroup T.twoBreak.profile w = ⊥ := by
    have hw_dom : (-1 : ℝ) ≤ w := by linarith [hcomp.1]
    have hspec := chapter05_herbrand_inverse_spec
      T.twoBreak.profile htop_bij w
    have hψ_dom := hinv_domain hw_dom
    have hF_le_b {x : ℝ} (hx : (-1 : ℝ) ≤ x)
        (hxb : x ≤ (T.twoBreak.b : ℝ)) :
        chapter05HerbrandFunction T.twoBreak.profile x ≤ c := by
      have hb_dom : (-1 : ℝ) ≤ (T.twoBreak.b : ℝ) := by
        have hb_nonneg : (0 : ℝ) ≤ (T.twoBreak.b : ℝ) := by
          exact_mod_cast T.twoBreak.a_pos.le.trans T.twoBreak.a_lt_b.le
        linarith
      have hle := hmono.monotoneOn hx hb_dom hxb
      rw [hFb] at hle
      exact hle
    have hψ_gt_b : (T.twoBreak.b : ℝ) <
        chapter05HerbrandInverse T.twoBreak.profile w := by
      by_contra hnot
      have hψ_le := le_of_not_gt hnot
      have hle := hF_le_b hψ_dom hψ_le
      linarith
    rw [chapter05UpperRamificationGroup, if_pos hw_dom,
      T.twoBreak.lower_after_second_layer _ hψ_gt_b]
  letI : Fintype (Gal(L / K)) := AlgEquiv.fintype K L
  let Q := R.quotient_setup
  have hQ_profile : Q.upstairs = R.local_data.profile := by
    exact R.quotient_setup_upstairs_eq
  have hup_R :
      Function.Bijective
        (chapter05HerbrandFunction Q.upstairs) := by
    exact chapter05_herbrand_bijective_of_filtration Q.upstairs
  have hdown_R :
      Function.Bijective
        (chapter05HerbrandFunction Q.downstairs) := by
    exact chapter05_herbrand_bijective_of_filtration Q.downstairs
  have hquotient_upper {w : ℝ} (hw : (-1 : ℝ) ≤ w) :
      chapter05UpperRamificationGroup Q.downstairs w =
        (chapter05UpperRamificationGroup R.local_data.profile w).map q := by
    simpa [chapter05UpperQuotientImage, q, hQ_profile] using
      (chapter05_herbrand_quotient_theorem (MonoidHom.ker χ)
        Q hup_R hdown_R hw)
  have hdown_upper_c :
      chapter05UpperRamificationGroup Q.downstairs c =
        H.map q := by
    have htop_upper_c_R :
        chapter05UpperRamificationGroup R.local_data.profile c = H := by
      rw [hprofile]
      exact htop_upper_c
    rw [hquotient_upper (by linarith [hcomp.1]), htop_upper_c_R]
  have hdown_upper_gt {w : ℝ} (hw : c < w) :
      chapter05UpperRamificationGroup Q.downstairs w = ⊥ := by
    have htop_upper_gt_R :
        chapter05UpperRamificationGroup R.local_data.profile w = ⊥ := by
      rw [hprofile]
      exact htop_upper_gt hw
    rw [hquotient_upper (by linarith [hcomp.1]), htop_upper_gt_R]
    simp
  have hdown_right :
      chapter05UpperRightLimit Q.downstairs c = ⊥ := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K' hK'
      rcases hK' with ⟨w, hw, rfl⟩
      exact le_of_eq (hdown_upper_gt hw)
    · exact bot_le
  have hnotker : ∃ h : Gal(L / K), h ∈ H ∧ h ∉ MonoidHom.ker χ := by
    by_contra hnone
    apply hsubgroup_not_le_kernel
    intro h hh
    by_contra hhk
    apply hnone
    exact ⟨h, hh, hhk⟩
  have hqker_eq : MonoidHom.ker q = MonoidHom.ker χ := by
    dsimp [q]
    exact Chapter05QuotientRamificationSetup.quotient_map_kernel _
  have hmapH_ne_bot : H.map q ≠ (⊥ : Subgroup _ ) := by
    intro hbot
    rcases hnotker with ⟨h, hh, hhk⟩
    have hmem : q h ∈ H.map q := ⟨h, hh, rfl⟩
    rw [hbot] at hmem
    have hqone : q h = 1 := by simpa using hmem
    apply hhk
    have hkerq : h ∈ MonoidHom.ker q := MonoidHom.mem_ker.mpr hqone
    rw [hqker_eq] at hkerq
    exact hkerq
  have hdown_break : chapter05UpperBreak
      R.quotient_setup.downstairs c := by
    rw [chapter05UpperBreak]
    refine ⟨by linarith [hcomp.1], ?_⟩
    have hc_ne : c ≠ (-1 : ℝ) := by linarith [hcomp.1]
    rw [if_neg hc_ne, hdown_upper_c, hdown_right]
    exact hmapH_ne_bot
  have hquotient_profile_bij :
      Function.Bijective
        (chapter05HerbrandFunction R.quotient_local.profile) := by
    exact chapter05_herbrand_bijective_of_filtration R.quotient_local.profile
  have htransport_c := chapter05_upper_group_transport_of_profile
    R.quotient_setup.downstairs R.quotient_local.profile
      R.quotient_galois_equiv R.quotient_profile_transport hdown_R
        hquotient_profile_bij (by linarith [hcomp.1] : (-1 : ℝ) ≤ c)
  have htransport_gt {w : ℝ} (hw : c < w) :
      chapter05UpperRamificationGroup R.quotient_local.profile w = ⊥ := by
    have hw_dom : (-1 : ℝ) ≤ w := by linarith [hcomp.1]
    rw [chapter05_upper_group_transport_of_profile
      R.quotient_setup.downstairs R.quotient_local.profile
        R.quotient_galois_equiv R.quotient_profile_transport hdown_R
          hquotient_profile_bij hw_dom, hdown_upper_gt hw]
    simp
  have hupper_c_ne_bot :
      chapter05UpperRamificationGroup R.quotient_local.profile c ≠ ⊥ := by
    intro hzero
    have hmapzero :
        (chapter05UpperRamificationGroup Q.downstairs c).map
            R.quotient_galois_equiv.toMonoidHom = ⊥ := by
      rw [← htransport_c, hzero]
    rw [hdown_upper_c] at hmapzero
    rcases hnotker with ⟨h, hh, hhk⟩
    have hmem :
        R.quotient_galois_equiv (q h) ∈
          (H.map q).map R.quotient_galois_equiv.toMonoidHom := by
      exact ⟨q h, ⟨h, hh, rfl⟩, rfl⟩
    rw [hmapzero] at hmem
    have heq : R.quotient_galois_equiv (q h) = 1 := by simpa using hmem
    apply hhk
    have hqone : q h = 1 := by
      apply R.quotient_galois_equiv.injective
      simpa using heq
    have hkerq : h ∈ MonoidHom.ker q := MonoidHom.mem_ker.mpr hqone
    rw [hqker_eq] at hkerq
    exact hkerq
  have hright :
      chapter05UpperRightLimit R.quotient_local.profile c = ⊥ := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K' hK'
      rcases hK' with ⟨w, hw, rfl⟩
      exact le_of_eq (htransport_gt hw)
    · exact bot_le
  rw [chapter05UpperBreak]
  refine ⟨by linarith [hcomp.1], ?_⟩
  have hc_ne : c ≠ (-1 : ℝ) := by linarith [hcomp.1]
  rw [if_neg hc_ne, hright]
  exact hupper_c_ne_bot

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
  have hbreak := chapter05_character_kernel_detects_two_break_second_upper
    χ R T hprofile hsubgroup_not_le_kernel
  have hintegral := chapter05_character_kernel_upper_break_integer χ R hbreak
  refine ⟨hintegral, ?_⟩
  exact chapter05_two_break_integral_second_label_implies_dvd
    T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_prime.pos
    T.twoBreak.a_lt_b hintegral

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
  exact @chapter05_cyclic_hasse_arf_lemma _ _ _ _ _ _ _ _
    R.quotient_local R.quotient_cyclic R.quotient_residue_perfect
    b hlast hbreak htotally_ramified

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
  have hbreaks := chapter05_two_break_upper_breaks H T.twoBreak
    (chapter05_herbrand_bijective_of_filtration T.twoBreak.profile)
  have hsecond : chapter05UpperBreak D.profile
      (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) := by
    rw [hprofile]
    exact hbreaks.2.1
  have hintegral := (chapter05_hasse_arf D habelian) _ hsecond
  refine ⟨hintegral, ?_⟩
  exact chapter05_two_break_integral_second_label_implies_dvd
    T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_prime.pos
    T.twoBreak.a_lt_b hintegral

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
