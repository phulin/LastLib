import LastLib.Book03RamificationTheory.Chapter06.Dependencies
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.LinearAlgebra.Dimension.Finite

namespace LastLib.Book03RamificationTheory.Chapter06

noncomputable section

/-! ## 6.1. Why only upper numbering survives inverse limits -/

universe u

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
The source permits either a perfect residue field or a directed collection of
finite levels with separable residue extensions.  The latter is kept as an
explicit local interface because the current earlier chapters do not attach a
canonical residue-field object to every open normal subgroup.
-/
structure Chapter06SeparableResidueLevel (k : Type u) [Field k] where
  extension : Type u
  [extension_field : Field extension]
  [extension_algebra : Algebra k extension]
  [extension_finite : FiniteDimensional k extension]
  separable : Algebra.IsSeparable k extension

structure Chapter06ResidueData (P : ProfiniteGrp.{u}) where
  residueField : Type u
  [residueField_field : Field residueField]
  residueCharacteristicExponent : ℕ
  characteristic_exponent_eq :
    residueCharacteristicExponent = ringExpChar residueField
  residue_condition :
    chapter06PerfectResidueField residueField ∨
      ∀ _N : OpenNormalSubgroup P,
        Nonempty (Chapter06SeparableResidueLevel residueField)

structure Chapter06InfiniteGaloisRamificationData
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsGalois K E] where
  upper : Chapter06InfiniteUpperSystem (chapter06ProfiniteGaloisGroup K E)
  residue : Chapter06ResidueData (chapter06ProfiniteGaloisGroup K E)

namespace Chapter06InfiniteGaloisRamificationData

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]

abbrev galoisGroup
    (_D : Chapter06InfiniteGaloisRamificationData K E) : ProfiniteGrp :=
  chapter06ProfiniteGaloisGroup K E

abbrev inertia
    (D : Chapter06InfiniteGaloisRamificationData K E) : Subgroup D.galoisGroup :=
  chapter06InertiaGroup D.upper

abbrev wildInertia
    (D : Chapter06InfiniteGaloisRamificationData K E) : Subgroup D.galoisGroup :=
  chapter06WildInertiaGroup D.upper

end Chapter06InfiniteGaloisRamificationData

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
  sorry

noncomputable def chapter06GaloisLevelQuotientEquiv
    {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]
    (N : OpenNormalSubgroup (chapter06ProfiniteGaloisGroup K E)) :
    (chapter06ProfiniteGaloisGroup K E ⧸ N.toSubgroup) ≃*
      Gal(chapter06GaloisLevelFixedField N / K) := by
  exact @InfiniteGalois.normalAutEquivQuotient K E _ _ _ _
    (chapter06ClosedLevel N) (chapter06ClosedLevel_normal N)

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

def chapter06ProPGroup (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ N : FiniteIndexNormalSubgroup G,
    ∃ r : ℕ, Nat.card (G ⧸ N.toSubgroup) = p ^ r

def chapter06ProPrimeTo (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ N : FiniteIndexNormalSubgroup G,
    Nat.Coprime p (Nat.card (G ⧸ N.toSubgroup))

def chapter06Procyclic (G : Type*) [Group G] : Prop :=
  ∀ N : FiniteIndexNormalSubgroup G, IsCyclic (G ⧸ N.toSubgroup)

/- LOCAL_DEPENDENCY_GUESS: the current checkout has the finite upper profiles
and the infinite Galois correspondence but no earlier theorem packaging the
local residue-characteristic calculation for every finite quotient.  The
following statements are the book-facing consequences for the residue data
recorded above; they do not put those consequences into the data structure as
hypotheses. -/
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
  sorry

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
