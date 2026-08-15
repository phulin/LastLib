import LastLib.Book03RamificationTheory.Chapter06.Dependencies
import LastLib.Book03RamificationTheory.Chapter05.Section06HasseArfAndTheLimitsOfIntegrality
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.ClopenNhdofOne

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05

/-! ## 6.1. Why only upper numbering survives inverse limits -/

universe u v w

/-- The residue characteristic exponent, with `1` in characteristic zero. -/
def chapter06ResidueCharacteristicExponent (k : Type*) [Ring k] : ℕ :=
  ringExpChar k

/-- The perfect-residue-field hypothesis used for the strongest form. -/
def chapter06PerfectResidueField (k : Type*) [Field k] : Prop :=
  PerfectField k

/-- Separability of one finite residue extension. -/
def chapter06SeparableResidueExtension
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  Algebra.IsSeparable k l

/-!
An open normal level has a closed normal carrier, so Mathlib's infinite
Galois correspondence identifies its quotient with the Galois group of the
fixed field.  These declarations retain that identification at the chapter
API boundary.
-/

def chapter06ClosedLevel
    {P : ProfiniteGrp} (N : OpenNormalSubgroup P) : ClosedSubgroup P :=
  { toSubgroup := N.toSubgroup
    isClosed' := N.toOpenSubgroup.isClosed }

theorem chapter06ClosedLevel_normal
    {P : ProfiniteGrp} (N : OpenNormalSubgroup P) :
  (chapter06ClosedLevel N).toSubgroup.Normal := by
  change N.toSubgroup.Normal
  exact N.isNormal'

def chapter06GaloisLevelFixedField
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E)) :
    IntermediateField K E :=
  IntermediateField.fixedField N.toSubgroup

theorem chapter06GaloisLevelFixedField_finite
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E)) :
    FiniteDimensional K (chapter06GaloisLevelFixedField N) := by
  rw [← InfiniteGalois.isOpen_iff_finite]
  have hfix :
      (chapter06GaloisLevelFixedField N).fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField (chapter06ClosedLevel N)
  rw [hfix]
  change IsOpen (N.toOpenSubgroup : Set (chapter06ProfiniteGaloisGroup K E))
  exact N.toOpenSubgroup.isOpen

noncomputable def chapter06GaloisLevelQuotientEquiv
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E)) :
    (chapter06ProfiniteGaloisGroup K E ⧸ N.toSubgroup) ≃*
      Gal(chapter06GaloisLevelFixedField N / K) := by
  exact @InfiniteGalois.normalAutEquivQuotient K E _ _ _ _
    (chapter06ClosedLevel N) (chapter06ClosedLevel_normal N)

/-!
The upper system is now required to come from the complete discretely valued
finite Galois levels supplied by Chapter 5.  The profile transport is stated
after the canonical quotient equivalence, so the finite profiles cannot be
unrelated witnesses on an abstract quotient.
-/
structure Chapter06InfiniteGaloisRamificationRealization
    (K : Type v) (E : Type w) [Field K] [Field E] [Algebra K E] [IsGalois K E] where
  upper : Chapter06InfiniteUpperSystem (chapter06ProfiniteGaloisGroup K E)
  levelData :
    ∀ N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E),
      letI : FiniteDimensional K (chapter06GaloisLevelFixedField N) :=
        chapter06GaloisLevelFixedField_finite N
      letI : (chapter06ClosedLevel N).toSubgroup.Normal :=
        chapter06ClosedLevel_normal N
      letI : IsGalois K (chapter06GaloisLevelFixedField N) :=
        @IsGalois.of_fixedField_normal_subgroup K E _ _ _ _
          (chapter06ClosedLevel N).toSubgroup (chapter06ClosedLevel_normal N)
      letI : Finite (Gal(chapter06GaloisLevelFixedField N / K)) :=
        Finite.of_equiv _ (chapter06GaloisLevelQuotientEquiv N).toEquiv
      Chapter05LocalGaloisUpperData K (chapter06GaloisLevelFixedField N)
  upper_profile_is_realized :
    ∀ (N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E)) (v : ℝ),
      letI : FiniteDimensional K (chapter06GaloisLevelFixedField N) :=
        chapter06GaloisLevelFixedField_finite N
      letI : (chapter06ClosedLevel N).toSubgroup.Normal :=
        chapter06ClosedLevel_normal N
      letI : IsGalois K (chapter06GaloisLevelFixedField N) :=
        @IsGalois.of_fixedField_normal_subgroup K E _ _ _ _
          (chapter06ClosedLevel N).toSubgroup (chapter06ClosedLevel_normal N)
      letI : Finite (Gal(chapter06GaloisLevelFixedField N / K)) :=
        Finite.of_equiv _ (chapter06GaloisLevelQuotientEquiv N).toEquiv
      (chapter05UpperRamificationGroup (levelData N).profile v).map
          (chapter06GaloisLevelQuotientEquiv N).symm.toMonoidHom =
        chapter05UpperRamificationGroup (upper.upperProfile N) v
  residueField : Type v
  [residueField_field : Field residueField]
  residueField_identification :
    ∀ N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E),
      letI : FiniteDimensional K (chapter06GaloisLevelFixedField N) :=
        chapter06GaloisLevelFixedField_finite N
      letI : (chapter06ClosedLevel N).toSubgroup.Normal :=
        chapter06ClosedLevel_normal N
      letI : IsGalois K (chapter06GaloisLevelFixedField N) :=
        @IsGalois.of_fixedField_normal_subgroup K E _ _ _ _
          (chapter06ClosedLevel N).toSubgroup (chapter06ClosedLevel_normal N)
      letI : Finite (Gal(chapter06GaloisLevelFixedField N / K)) :=
        Finite.of_equiv _ (chapter06GaloisLevelQuotientEquiv N).toEquiv
      Nonempty (residueField ≃+*
        IsLocalRing.ResidueField
          (levelData N).vK.toValuation.valuationSubring)

/-- The actual finite residue extension at a realized local Galois level. -/
def chapter06ResidueLevelCondition
    {K : Type v} {E : Type w} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (R : Chapter06InfiniteGaloisRamificationRealization K E)
    (N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E)) : Prop :=
  letI : FiniteDimensional K (chapter06GaloisLevelFixedField N) :=
    chapter06GaloisLevelFixedField_finite N
  letI : (chapter06ClosedLevel N).toSubgroup.Normal :=
    chapter06ClosedLevel_normal N
  letI : IsGalois K (chapter06GaloisLevelFixedField N) :=
    @IsGalois.of_fixedField_normal_subgroup K E _ _ _ _
      (chapter06ClosedLevel N).toSubgroup (chapter06ClosedLevel_normal N)
  letI : Finite (Gal(chapter06GaloisLevelFixedField N / K)) :=
    Finite.of_equiv _ (chapter06GaloisLevelQuotientEquiv N).toEquiv
  let L := R.levelData N
  letI : L.vK.toValuation.HasExtension L.vL.toValuation :=
    ⟨L.restriction⟩
  FiniteDimensional
      (IsLocalRing.ResidueField L.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField L.vL.toValuation.valuationSubring) ∧
    Algebra.IsSeparable
      (IsLocalRing.ResidueField L.vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField L.vL.toValuation.valuationSubring)

structure Chapter06ResidueData
    {K : Type v} {E : Type w} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (R : Chapter06InfiniteGaloisRamificationRealization K E) where
  residueField : Type v
  [residueField_field : Field residueField]
  residueField_equiv :
    letI : Field R.residueField := R.residueField_field
    residueField ≃+* R.residueField
  residueCharacteristicExponent : ℕ
  characteristic_exponent_eq :
    residueCharacteristicExponent = ringExpChar residueField
  residue_condition :
    chapter06PerfectResidueField residueField ∨
      ∀ N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E),
        chapter06ResidueLevelCondition R N

structure Chapter06InfiniteGaloisRamificationData
    (K : Type v) (E : Type w) [Field K] [Field E] [Algebra K E] [IsGalois K E] where
  realization : Chapter06InfiniteGaloisRamificationRealization K E
  residue : Chapter06ResidueData realization

namespace Chapter06InfiniteGaloisRamificationData

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]

abbrev galoisGroup
    (_D : Chapter06InfiniteGaloisRamificationData K E) : ProfiniteGrp :=
  chapter06ProfiniteGaloisGroup K E

abbrev upper
    (D : Chapter06InfiniteGaloisRamificationData K E) :
    Chapter06InfiniteUpperSystem D.galoisGroup :=
  D.realization.upper

abbrev inertia
    (D : Chapter06InfiniteGaloisRamificationData K E) : Subgroup D.galoisGroup :=
  chapter06InertiaGroup D.upper

abbrev wildInertia
    (D : Chapter06InfiniteGaloisRamificationData K E) : Subgroup D.galoisGroup :=
  chapter06WildInertiaGroup D.upper

end Chapter06InfiniteGaloisRamificationData

/-- The following statements are consequences of the finite local-Galois
realization carried by `D`; the pro-group conclusions are not hypotheses of
the data structure. -/
theorem chapter06_tame_quotient_pro_prime_to
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (p : ℕ) (hp : 1 < p)
    (hlevels : Chapter06FiniteLevelLocalRamificationInterface D.upper p)
    (hp_characteristic : p = D.residue.residueCharacteristicExponent) :
    chapter06ProPrimeTo p (chapter06TameQuotient D.upper) := by
  intro H
  rcases hlevels.tame_kernel_cofinal H with ⟨N, hN⟩
  let f := hlevels.tame_level_map N
  have hf : Function.Surjective f := hlevels.tame_level_map_surjective N
  letI : Finite (chapter06FiniteLevelTameQuotient D.upper N) :=
    hlevels.tame_level_finite N
  letI : Finite (chapter06TameQuotient D.upper ⧸ f.ker) :=
    Finite.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
      (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  let qmap : (chapter06TameQuotient D.upper ⧸ f.ker) →*
      (chapter06TameQuotient D.upper ⧸ H.toSubgroup) :=
    QuotientGroup.map f.ker H.toSubgroup (MonoidHom.id _) (by
      intro x hx
      exact hN hx)
  have hqmap : Function.Surjective qmap := by
    intro y
    rcases QuotientGroup.mk'_surjective H.toSubgroup y with ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk' f.ker x, ?_⟩
    rfl
  have hdiv :
      Nat.card (chapter06TameQuotient D.upper ⧸ H.toSubgroup) ∣
    Nat.card (chapter06TameQuotient D.upper ⧸ f.ker) := by
    rw [← Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective qmap hqmap).toEquiv]
    exact Subgroup.card_quotient_dvd_card qmap.ker
  have hcop :
      Nat.Coprime p (Nat.card (chapter06TameQuotient D.upper ⧸ f.ker)) := by
    rw [Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    exact hlevels.tame_level_prime_to N
  exact ⟨Finite.of_surjective qmap hqmap,
    Nat.Coprime.of_dvd_right hdiv hcop⟩

theorem chapter06_wild_inertia_pro_p
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (p : ℕ) (hp : 1 < p)
    (hlevels : Chapter06FiniteLevelLocalRamificationInterface D.upper p)
    (hp_characteristic : p = D.residue.residueCharacteristicExponent) :
    chapter06ProPGroup p (chapter06WildInertiaGroup D.upper) := by
  intro H
  rcases hlevels.wild_kernel_cofinal H with ⟨N, hN⟩
  let f := hlevels.wild_level_map N
  have hf : Function.Surjective f := hlevels.wild_level_map_surjective N
  letI : Finite (chapter06FiniteLevelWildInertiaGroup D.upper N) :=
    hlevels.wild_level_finite N
  letI : Finite (chapter06WildInertiaGroup D.upper ⧸ f.ker) :=
    Finite.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
      (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  let qmap : (chapter06WildInertiaGroup D.upper ⧸ f.ker) →*
      (chapter06WildInertiaGroup D.upper ⧸ H.toSubgroup) :=
    QuotientGroup.map f.ker H.toSubgroup (MonoidHom.id _) (by
      intro x hx
      exact hN hx)
  have hqmap : Function.Surjective qmap := by
    intro y
    rcases QuotientGroup.mk'_surjective H.toSubgroup y with ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk' f.ker x, ?_⟩
    rfl
  have hp_prime : Nat.Prime p := by
    letI : Field D.residue.residueField := D.residue.residueField_field
    have hchar : p = ringExpChar D.residue.residueField :=
      hp_characteristic.trans D.residue.characteristic_exponent_eq
    rw [hchar]
    exact (expChar_is_prime_or_one D.residue.residueField _).resolve_right
      (by
        intro h
        apply (Nat.ne_of_gt hp)
        exact hchar.trans h)
  letI : Fact p.Prime := ⟨hp_prime⟩
  have hQp : IsPGroup p (chapter06FiniteLevelWildInertiaGroup D.upper N) := by
    obtain ⟨r, hr⟩ := hlevels.wild_level_p_power N
    exact IsPGroup.of_card hr
  let qmap' : (chapter06FiniteLevelWildInertiaGroup D.upper N) →*
      (chapter06WildInertiaGroup D.upper ⧸ H.toSubgroup) :=
    qmap.comp (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
  have hqmap' : Function.Surjective qmap' := by
    intro y
    rcases hqmap y with ⟨x, hx⟩
    refine ⟨QuotientGroup.quotientKerEquivOfSurjective f hf x, ?_⟩
    simpa [qmap'] using hx
  have htarget :
      IsPGroup p (chapter06WildInertiaGroup D.upper ⧸ H.toSubgroup) :=
    hQp.of_surjective qmap' hqmap'
  letI : Finite (chapter06WildInertiaGroup D.upper ⧸ H.toSubgroup) :=
    Finite.of_surjective qmap' hqmap'
  rcases IsPGroup.iff_card.mp htarget with ⟨r, hr⟩
  exact ⟨r, inferInstance, hr⟩

theorem chapter06_tame_quotient_procyclic_of_separably_closed_residue
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (p : ℕ) (hp : 1 < p)
    (hlevels : Chapter06FiniteLevelLocalRamificationInterface D.upper p)
    (hp_characteristic : p = D.residue.residueCharacteristicExponent)
    (hsep : letI : Field D.residue.residueField := D.residue.residueField_field;
      IsSepClosed D.residue.residueField) :
    chapter06Procyclic (chapter06TameQuotient D.upper) := by
  intro H
  rcases hlevels.tame_kernel_cofinal H with ⟨N, hN⟩
  let f := hlevels.tame_level_map N
  have hf : Function.Surjective f := hlevels.tame_level_map_surjective N
  letI : Finite (chapter06FiniteLevelTameQuotient D.upper N) :=
    hlevels.tame_level_finite N
  letI : Finite (chapter06TameQuotient D.upper ⧸ f.ker) :=
    Finite.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
      (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  let qmap : (chapter06TameQuotient D.upper ⧸ f.ker) →*
      (chapter06TameQuotient D.upper ⧸ H.toSubgroup) :=
    QuotientGroup.map f.ker H.toSubgroup (MonoidHom.id _) (by
      intro x hx
      exact hN hx)
  have hqmap : Function.Surjective qmap := by
    intro y
    rcases QuotientGroup.mk'_surjective H.toSubgroup y with ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk' f.ker x, ?_⟩
    rfl
  let qmap' : (chapter06FiniteLevelTameQuotient D.upper N) →*
      (chapter06TameQuotient D.upper ⧸ H.toSubgroup) :=
    qmap.comp (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
  have hqmap' : Function.Surjective qmap' := by
    intro y
    rcases hqmap y with ⟨x, hx⟩
    refine ⟨QuotientGroup.quotientKerEquivOfSurjective f hf x, ?_⟩
    simpa [qmap'] using hx
  letI : IsCyclic (chapter06FiniteLevelTameQuotient D.upper N) :=
    hlevels.tame_level_cyclic N
  letI : Finite (chapter06TameQuotient D.upper ⧸ H.toSubgroup) :=
    Finite.of_surjective qmap' hqmap'
  exact ⟨inferInstance, isCyclic_of_surjective qmap' hqmap'⟩

theorem chapter06_residue_characteristic_exponent_eq_one_of_charZero
    {k : Type*} [Field k] [CharZero k] :
    chapter06ResidueCharacteristicExponent k = 1 := by
  simp [chapter06ResidueCharacteristicExponent]

theorem chapter06_wild_inertia_trivial_of_characteristic_zero
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (hlevels : Chapter06FiniteLevelLocalRamificationInterface D.upper 1)
    (hcharacteristic_zero :
      D.residue.residueCharacteristicExponent = 1) :
    chapter06WildInertiaGroup D.upper = ⊥ := by
  letI : CompactSpace (chapter06WildInertiaGroup D.upper) :=
    isCompact_iff_compactSpace.mp
      (chapter06InfiniteUpperRightLimit_closed D.upper 0).isCompact
  apply le_antisymm
  · intro g hg
    change g = 1
    by_contra hne
    let g' : chapter06WildInertiaGroup D.upper := ⟨g, hg⟩
    have hgne : g' ≠ 1 := by
      intro h
      apply hne
      change g = 1
      simpa [g'] using congrArg Subtype.val h
    let U : Set (chapter06WildInertiaGroup D.upper) := ({g'} : Set _)ᶜ
    have hUopen : IsOpen U := by
      dsimp [U]
      exact isClosed_singleton.isOpen_compl
    have hone : (1 : chapter06WildInertiaGroup D.upper) ∈ U := by
      change (1 : chapter06WildInertiaGroup D.upper) ∉ ({g'} : Set _)
      simpa using Ne.symm hgne
    obtain ⟨H, hH⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUopen hone
    rcases hlevels.wild_kernel_cofinal H with ⟨N, hN⟩
    let f := hlevels.wild_level_map N
    have hfker : f.ker = ⊤ := by
      apply top_unique
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      have htriv :
          chapter06FiniteLevelWildInertiaGroup D.upper N = ⊥ :=
        hlevels.wild_level_trivial_of_characteristic_zero rfl N
      have hxmem :
          (f x : chapter06ProfiniteGaloisGroup K E ⧸ N.toSubgroup) ∈
            (⊥ : Subgroup (chapter06ProfiniteGaloisGroup K E ⧸ N.toSubgroup)) := by
        rw [← htriv]
        exact (f x).property
      simpa using Subgroup.mem_bot.mp hxmem
    have htop : (⊤ : Subgroup (chapter06WildInertiaGroup D.upper)) ≤ H.toSubgroup := by
      rw [← hfker]
      exact hN
    have hgH : g' ∈ H := htop (by simp)
    exact (hH hgH) rfl
  · exact bot_le

theorem chapter06_all_inertia_tame_of_characteristic_zero
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (hlevels : Chapter06FiniteLevelLocalRamificationInterface D.upper 1)
    (hcharacteristic_zero :
      D.residue.residueCharacteristicExponent = 1) :
    chapter06WildInertiaGroup D.upper = ⊥ := by
  exact chapter06_wild_inertia_trivial_of_characteristic_zero D
    hlevels
    hcharacteristic_zero

end

end LastLib.Book03RamificationTheory.Chapter06
