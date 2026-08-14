import LastLib.Book03RamificationTheory.Chapter06.Dependencies
import LastLib.Book03RamificationTheory.Chapter05.Section06HasseArfAndTheLimitsOfIntegrality
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Valuation.Extension

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

/-!
The tame quotient is a genuine group quotient of inertia by wild inertia.  The
finite-index formulation of the three profinite properties avoids choosing a
presentation of the profinite group.
-/

def chapter06TameQuotient
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) : Type u :=
  chapter06InertiaGroup S ⧸
    (chapter06WildInertiaGroup S).subgroupOf (chapter06InertiaGroup S)

instance chapter06TameQuotient_group
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) :
    Group (chapter06TameQuotient S) := by
  letI : (chapter06WildInertiaGroup S).Normal :=
    chapter06WildInertiaGroup_normal S
  change Group
    (chapter06InertiaGroup S ⧸
      (chapter06WildInertiaGroup S).subgroupOf (chapter06InertiaGroup S))
  infer_instance

noncomputable instance chapter06TameQuotient_topologicalSpace
    {P : ProfiniteGrp.{u}} (S : Chapter06InfiniteUpperSystem P) :
    TopologicalSpace (chapter06TameQuotient S) := by
  exact QuotientGroup.instTopologicalSpace _

def chapter06ProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G,
    ∃ r : ℕ, Finite (G ⧸ N.toSubgroup) ∧
      Nat.card (G ⧸ N.toSubgroup) = p ^ r

def chapter06ProPrimeTo (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G,
    Finite (G ⧸ N.toSubgroup) ∧
      Nat.Coprime p (Nat.card (G ⧸ N.toSubgroup))

def chapter06Procyclic (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G,
    Finite (G ⧸ N.toSubgroup) ∧ IsCyclic (G ⧸ N.toSubgroup)

/-- The following statements are consequences of the finite local-Galois
realization carried by `D`; the pro-group conclusions are not hypotheses of
the data structure. -/
theorem chapter06_tame_quotient_pro_prime_to
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (p : ℕ) (hp : 1 < p)
    (hp_characteristic : p = D.residue.residueCharacteristicExponent) :
    chapter06ProPrimeTo p (chapter06TameQuotient D.upper) := by
  sorry

theorem chapter06_wild_inertia_pro_p
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (p : ℕ) (hp : 1 < p)
    (hp_characteristic : p = D.residue.residueCharacteristicExponent) :
    chapter06ProPGroup p (chapter06WildInertiaGroup D.upper) := by
  sorry

theorem chapter06_tame_quotient_procyclic_of_separably_closed_residue
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (p : ℕ) (hp : 1 < p)
    (hp_characteristic : p = D.residue.residueCharacteristicExponent)
    (hsep : letI : Field D.residue.residueField := D.residue.residueField_field
      IsSepClosed D.residue.residueField) :
    chapter06Procyclic (chapter06TameQuotient D.upper) := by
  sorry

theorem chapter06_residue_characteristic_exponent_eq_one_of_charZero
    {k : Type*} [Field k] [CharZero k] :
    chapter06ResidueCharacteristicExponent k = 1 := by
  simp [chapter06ResidueCharacteristicExponent]

theorem chapter06_wild_inertia_trivial_of_characteristic_zero
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (hcharacteristic_zero :
      D.residue.residueCharacteristicExponent = 1) :
    chapter06WildInertiaGroup D.upper = ⊥ := by
  sorry

theorem chapter06_all_inertia_tame_of_characteristic_zero
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    [IsSepClosed E]
    (D : Chapter06InfiniteGaloisRamificationData K E)
    (hcharacteristic_zero :
      D.residue.residueCharacteristicExponent = 1) :
    chapter06WildInertiaGroup D.upper = ⊥ := by
  exact chapter06_wild_inertia_trivial_of_characteristic_zero D
    hcharacteristic_zero

end

end LastLib.Book03RamificationTheory.Chapter06
