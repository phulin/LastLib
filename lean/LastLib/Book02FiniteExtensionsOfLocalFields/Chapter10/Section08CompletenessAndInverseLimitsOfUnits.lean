import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields
import Mathlib.GroupTheory.CosetCover
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

set_option maxHeartbeats 800000

open Ideal IsLocalRing
open Filter
open scoped Topology Pointwise

/-! ## 10.8. Completeness and inverse limits of units -/

/-- Reduction from precision `n+1` to precision `n`. -/
noncomputable def chapter10PrecisionRingTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrecisionQuotient A (n + 1) →+*
      Chapter10PrecisionQuotient A n := by
  exact Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The induced transition map on finite-precision unit groups. -/
def chapter10PrecisionUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    (Chapter10PrecisionQuotient A (n + 1))ˣ →*
      (Chapter10PrecisionQuotient A n)ˣ :=
  Units.map (chapter10PrecisionRingTransition A n).toMonoidHom

/-- An opaque name for a finite-precision unit group, avoiding quotient unfolding in families. -/
def Chapter10PrecisionUnitGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  (Chapter10PrecisionQuotient A (n + 1))ˣ

instance chapter10PrecisionUnitGroupGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Group (Chapter10PrecisionUnitGroup A n) := by
  change Group ((Chapter10PrecisionQuotient A (n + 1))ˣ)
  infer_instance

/-- The abstract transition used by the inverse-limit interface. -/
noncomputable def chapter10AbstractPrecisionUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrecisionUnitGroup A (n + 1) →*
      Chapter10PrecisionUnitGroup A n := by
  change (Chapter10PrecisionQuotient A (n + 2))ˣ →*
    (Chapter10PrecisionQuotient A (n + 1))ˣ
  exact chapter10PrecisionUnitTransition A (n + 1)

/-- A compatible family of units in all finite congruence quotients. -/
def Chapter10CompatibleUnitFamily
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Subgroup (∀ n : ℕ, Chapter10PrecisionUnitGroup A n) where
  carrier := {x | ∀ n,
    chapter10AbstractPrecisionUnitTransition A n (x (n + 1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hxy hy n
    change chapter10AbstractPrecisionUnitTransition A n
        (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hxy n, hy n]
  inv_mem' := by
    intro x hxy n
    change chapter10AbstractPrecisionUnitTransition A n
        ((x (n + 1))⁻¹) = (x n)⁻¹
    rw [map_inv, hxy n]

/-- The inverse-limit group of finite-precision units. -/
abbrev Chapter10AdicUnitInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] : Type _ :=
  Chapter10CompatibleUnitFamily A

/-- The canonical compatible family attached to a ring unit. -/
noncomputable def chapter10UnitToAdicInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Aˣ →* Chapter10AdicUnitInverseLimit A := by
  let q : ∀ n : ℕ, Aˣ →* Chapter10PrecisionUnitGroup A n :=
    fun n => Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom
  have hcompat : ∀ (u : Aˣ) (n : ℕ),
      chapter10AbstractPrecisionUnitTransition A n (q (n + 1) u) = q n u := by
    intro u n
    apply Units.ext
    change (chapter10PrecisionRingTransition A (n + 1))
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1 + 1))
          (u : A)) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1)) (u : A)
    rw [chapter10PrecisionRingTransition, Ideal.Quotient.factor_mk]
  refine
    { toFun := fun u => ⟨fun n => q n u, fun n => hcompat u n⟩
      map_one' := by
        ext n
        exact (q n).map_one
      map_mul' := by
        intro u v
        ext n
        exact (q n).map_mul u v }

private noncomputable def chapter10CompatibleRingUnitMap
    {L : Type*} [Field L] (A : ValuationSubring L) :
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
      (IsLocalRing.maximalIdeal A))ˣ →*
      Chapter10AdicUnitInverseLimit A := by
  let C :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
      (IsLocalRing.maximalIdeal A)
  let coordinate (n : ℕ) : C →+* Chapter10PrecisionQuotient A (n + 1) :=
    { toFun := fun x => x.1 n
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  let q : ∀ n : ℕ, Cˣ →* Chapter10PrecisionUnitGroup A n :=
    fun n => Units.map (coordinate n).toMonoidHom
  have hcompat : ∀ (u : Cˣ) (n : ℕ),
      chapter10AbstractPrecisionUnitTransition A n (q (n + 1) u) = q n u := by
    intro u n
    apply Units.ext
    change chapter10PrecisionRingTransition A (n + 1)
        (coordinate (n + 1) (u : C)) = coordinate n (u : C)
    change (chapter10PrecisionRingTransition A (n + 1))
        ((u : C).1 (n + 1)) = (u : C).1 n
    rw [chapter10PrecisionRingTransition]
    exact (LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily.compatible
      (u : C) n)
  refine
    { toFun := fun u => ⟨fun n => q n u, hcompat u⟩
      map_one' := by
        ext n
        exact (q n).map_one
      map_mul' := by
        intro u v
        ext n
        exact (q n).map_mul u v }

private noncomputable def chapter10CompatibleRingUnitUnmap
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Chapter10AdicUnitInverseLimit A →*
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
        (IsLocalRing.maximalIdeal A))ˣ := by
  let C :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
      (IsLocalRing.maximalIdeal A)
  let X := Chapter10AdicUnitInverseLimit A
  let toFamily : X → C := fun x =>
    ⟨fun n =>
        ((show (Chapter10PrecisionQuotient A (n + 1))ˣ from x.1 n) :
          Chapter10PrecisionQuotient A (n + 1)), by
      intro n
      have hx := congrArg Units.val (x.2 n)
      change (chapter10PrecisionRingTransition A (n + 1))
          ((show (Chapter10PrecisionQuotient A (n + 2))ˣ from x.1 (n + 1)) :
            Chapter10PrecisionQuotient A (n + 2)) =
        ((show (Chapter10PrecisionQuotient A (n + 1))ˣ from x.1 n) :
          Chapter10PrecisionQuotient A (n + 1)) at hx
      simpa [chapter10PrecisionRingTransition] using hx⟩
  refine
    { toFun := fun x =>
        { val := toFamily x
          inv := toFamily x⁻¹
          val_inv := by
            apply Subtype.ext
            funext n
            change ((show (Chapter10PrecisionQuotient A (n + 1))ˣ from x.1 n) :
                Chapter10PrecisionQuotient A (n + 1)) *
                ((show (Chapter10PrecisionQuotient A (n + 1))ˣ from (x⁻¹).1 n) :
                  Chapter10PrecisionQuotient A (n + 1)) = 1
            exact Units.mul_inv (show (Chapter10PrecisionQuotient A (n + 1))ˣ from x.1 n)
          inv_val := by
            apply Subtype.ext
            funext n
            change ((show (Chapter10PrecisionQuotient A (n + 1))ˣ from (x⁻¹).1 n) :
                Chapter10PrecisionQuotient A (n + 1)) *
                ((show (Chapter10PrecisionQuotient A (n + 1))ˣ from x.1 n) :
                  Chapter10PrecisionQuotient A (n + 1)) = 1
            exact Units.inv_mul (show (Chapter10PrecisionQuotient A (n + 1))ˣ from x.1 n) }
      map_one' := by
        apply Units.ext
        apply Subtype.ext
        funext n
        rfl
      map_mul' := by
        intro x y
        apply Units.ext
        apply Subtype.ext
        funext n
        rfl }

/-- Completeness identifies ring units with the inverse limit of their reductions. -/
theorem chapter10_complete_units_inverse_limit
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : Aˣ ≃* Chapter10AdicUnitInverseLimit A,
      ∀ u, e u = chapter10UnitToAdicInverseLimit A u := by
  classical
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hcomplete
  let C :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily A
      (IsLocalRing.maximalIdeal A)
  let I := IsLocalRing.maximalIdeal A
  let coordinate (n : ℕ) : C →+* A ⧸ I ^ (n + 1) :=
    { toFun := fun x => x.1 n
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  let F : ∀ n : ℕ, C →+* A ⧸ I ^ n :=
    fun n => (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (coordinate n)
  have hF : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (F n) = F m := by
    intro m n hmn
    ext z
    change Ideal.Quotient.factorPow I hmn
        (Ideal.Quotient.factorPow I (Nat.le_succ n) (z.1 n)) =
      Ideal.Quotient.factorPow I (Nat.le_succ m) (z.1 m)
    have hlong : z.1 m =
        Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n) := by
      have hlong' :=
        Ideal.Quotient.eq_factor_of_eq_factor_succ
          (I := fun i : ℕ => I ^ (i + 1))
          (fun i j hij => Ideal.pow_le_pow_right (Nat.succ_le_succ hij))
          (fun i => z.1 i)
          (fun i => by simp)
          hmn
      simpa [Ideal.Quotient.factorPow] using hlong'
    calc
      Ideal.Quotient.factorPow I hmn
          (Ideal.Quotient.factorPow I (Nat.le_succ n) (z.1 n)) =
          Ideal.Quotient.factorPow I (Nat.le_trans hmn (Nat.le_succ n))
            (z.1 n) := by
        simp [Ideal.Quotient.factorPow]
      _ = Ideal.Quotient.factorPow I (Nat.le_succ m)
          (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn) (z.1 n)) := by
        simp [Ideal.Quotient.factorPow]
      _ = Ideal.Quotient.factorPow I (Nat.le_succ m) (z.1 m) := by
        exact congrArg (Ideal.Quotient.factorPow I (Nat.le_succ m)) hlong.symm
  let g : C →+* A := IsAdicComplete.liftRingHom I F hF
  let eRing : A →+* C :=
    { toFun := fun a =>
        ⟨fun n => Ideal.Quotient.mk (I ^ (n + 1)) a, by
          intro n
          exact DFunLike.congr_fun
            (Ideal.Quotient.factor_comp_mk
              (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) a⟩
      map_one' := by
        ext n
        rfl
      map_mul' := by
        intro a b
        ext n
        rfl
      map_zero' := by
        ext n
        rfl
      map_add' := by
        intro a b
        ext n
        rfl }
  have hg_coord (n : ℕ) (x : C) :
      Ideal.Quotient.mk (I ^ n) (g x) = F n x := by
    exact IsAdicComplete.mk_liftRingHom I F hF n x
  have hRing_right : eRing.comp g = RingHom.id C := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    funext n
    change Ideal.Quotient.mk (I ^ (n + 1)) (g x) = x.1 n
    rw [hg_coord (n + 1) x]
    change Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
        (x.1 (n + 1)) = x.1 n
    exact (LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Chapter08CompatibleFamily.compatible
      x n)
  have hRing_left : g.comp eRing = RingHom.id A := by
    apply RingHom.ext
    intro a
    apply (IsHausdorff.eq_iff_smodEq (I := I)).2
    intro n
    have hq : Ideal.Quotient.mk (I ^ n) (g (eRing a)) =
        Ideal.Quotient.mk (I ^ n) a := by
      rw [hg_coord n (eRing a)]
      change Ideal.Quotient.factorPow I (Nat.le_succ n)
          (Ideal.Quotient.mk (I ^ (n + 1)) a) = _
      exact DFunLike.congr_fun
        (Ideal.Quotient.factor_comp_mk
          (Ideal.pow_le_pow_right (Nat.le_succ n))) a
    simpa [SModEq.idealQuotientMk, smul_eq_mul, Ideal.mul_top] using hq
  let ringEquiv : A ≃+* C := RingEquiv.ofBijective eRing (by
    constructor
    · intro a b hab
      have h := congrArg g hab
      have ha := DFunLike.congr_fun hRing_left a
      have hb := DFunLike.congr_fun hRing_left b
      have ha' : g (eRing a) = a := by
        simpa [RingHom.comp_apply] using ha
      have hb' : g (eRing b) = b := by
        simpa [RingHom.comp_apply] using hb
      exact ha'.symm.trans (h.trans hb')
    · intro x
      exact ⟨g x, by
        simpa [RingHom.comp_apply] using DFunLike.congr_fun hRing_right x⟩)
  let unitEquiv : Aˣ ≃* Cˣ := Units.mapEquiv ringEquiv.toMulEquiv
  let unitMap : Aˣ →* Chapter10AdicUnitInverseLimit A :=
    (chapter10CompatibleRingUnitMap A).comp unitEquiv.toMonoidHom
  have hunit_left (y : Cˣ) :
      chapter10CompatibleRingUnitUnmap A
          (chapter10CompatibleRingUnitMap A y) = y := by
    apply Units.ext
    apply Subtype.ext
    funext n
    rfl
  have hunit_right (x : Chapter10AdicUnitInverseLimit A) :
      chapter10CompatibleRingUnitMap A
          (chapter10CompatibleRingUnitUnmap A x) = x := by
    apply Subtype.ext
    funext n
    apply Units.ext
    rfl
  let unitMapInv : Chapter10AdicUnitInverseLimit A →* Aˣ :=
    unitEquiv.symm.toMonoidHom.comp (chapter10CompatibleRingUnitUnmap A)
  have hunitMap_left (u : Aˣ) : unitMapInv (unitMap u) = u := by
    change unitEquiv.symm
        (chapter10CompatibleRingUnitUnmap A
          (chapter10CompatibleRingUnitMap A (unitEquiv u))) = u
    rw [hunit_left]
    exact unitEquiv.symm_apply_apply u
  have hunitMap_right (x : Chapter10AdicUnitInverseLimit A) :
      unitMap (unitMapInv x) = x := by
    change chapter10CompatibleRingUnitMap A
        (unitEquiv (unitEquiv.symm
          (chapter10CompatibleRingUnitUnmap A x))) = x
    rw [unitEquiv.apply_symm_apply]
    exact hunit_right x
  have hunitMap_injective : Function.Injective unitMap := by
    intro u v huv
    have h := congrArg unitMapInv huv
    rw [hunitMap_left, hunitMap_left] at h
    exact h
  have hunitMap_surjective : Function.Surjective unitMap := by
    intro x
    exact ⟨unitMapInv x, hunitMap_right x⟩
  let e : Aˣ ≃* Chapter10AdicUnitInverseLimit A :=
    MulEquiv.ofBijective unitMap ⟨hunitMap_injective, hunitMap_surjective⟩
  refine ⟨e, ?_⟩
  intro u
  apply Subtype.ext
  funext n
  change (unitMap u).1 n =
    (chapter10UnitToAdicInverseLimit A u).1 n
  rfl

/-- The finite-precision quotients of the principal-unit group. -/
abbrev Chapter10PrincipalUnitPrecisionQuotient
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  chapter10UnitFiltration A 1 ⧸
    (chapter10UnitFiltration A (n + 1)).subgroupOf (chapter10UnitFiltration A 1)

/-- Reduction between successive principal-unit precision quotients. -/
noncomputable def chapter10PrincipalUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrincipalUnitPrecisionQuotient A (n + 1) →*
      Chapter10PrincipalUnitPrecisionQuotient A n := by
  exact QuotientGroup.map
    ((chapter10UnitFiltration A (n + 2)).subgroupOf
      (chapter10UnitFiltration A 1))
    ((chapter10UnitFiltration A (n + 1)).subgroupOf
      (chapter10UnitFiltration A 1))
    (MonoidHom.id _) (by
      intro u hu
      change (u : Aˣ) ∈ chapter10UnitFiltration A (n + 1)
      exact (chapter10_unit_filtration_descending A (n + 1)) hu)

/-- An opaque name for a principal-unit precision quotient. -/
def Chapter10PrincipalUnitPrecisionGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  Chapter10PrincipalUnitPrecisionQuotient A n

instance chapter10PrincipalUnitPrecisionGroupGroup
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Group (Chapter10PrincipalUnitPrecisionGroup A n) := by
  change Group (Chapter10PrincipalUnitPrecisionQuotient A n)
  infer_instance

/-- The abstract transition used by the principal-unit inverse-limit interface. -/
noncomputable def chapter10AbstractPrincipalUnitTransition
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Chapter10PrincipalUnitPrecisionGroup A (n + 1) →*
      Chapter10PrincipalUnitPrecisionGroup A n := by
  change Chapter10PrincipalUnitPrecisionQuotient A (n + 1) →*
    Chapter10PrincipalUnitPrecisionQuotient A n
  exact chapter10PrincipalUnitTransition A n

/-- A compatible family of principal units modulo every deeper subgroup. -/
def Chapter10CompatiblePrincipalUnitFamily
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Subgroup (∀ n : ℕ, Chapter10PrincipalUnitPrecisionGroup A n) where
  carrier := {x | ∀ n,
    chapter10AbstractPrincipalUnitTransition A n (x (n + 1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hxy hy n
    change chapter10AbstractPrincipalUnitTransition A n
        (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hxy n, hy n]
  inv_mem' := by
    intro x hxy n
    change chapter10AbstractPrincipalUnitTransition A n
        ((x (n + 1))⁻¹) = (x n)⁻¹
    rw [map_inv, hxy n]

/-- The inverse-limit type for principal units. -/
abbrev Chapter10PrincipalUnitInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] : Type _ :=
  Chapter10CompatiblePrincipalUnitFamily A

/- The canonical family of principal-unit reductions. -/
noncomputable def chapter10PrincipalUnitToAdicInverseLimit
    (A : Type*) [CommRing A] [IsLocalRing A] :
    chapter10UnitFiltration A 1 →*
      Chapter10PrincipalUnitInverseLimit A := by
  let q : ∀ n : ℕ,
      chapter10UnitFiltration A 1 →*
        Chapter10PrincipalUnitPrecisionGroup A n :=
    fun n => QuotientGroup.mk'
      ((chapter10UnitFiltration A (n + 1)).subgroupOf
        (chapter10UnitFiltration A 1))
  have hcompat : ∀ (u : chapter10UnitFiltration A 1) (n : ℕ),
      chapter10AbstractPrincipalUnitTransition A n (q (n + 1) u) =
        q n u := by
    intro u n
    rfl
  refine
    { toFun := fun u => ⟨fun n => q n u, hcompat u⟩
      map_one' := by
        ext n
        exact (q n).map_one
      map_mul' := by
        intro u v
        ext n
        exact (q n).map_mul u v }

/-- Completeness identifies principal units with their compatible finite layers. -/
theorem chapter10_complete_principal_units_inverse_limit
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    ∃ e : chapter10UnitFiltration A 1 ≃*
        Chapter10PrincipalUnitInverseLimit A,
      ∀ u, e u = chapter10PrincipalUnitToAdicInverseLimit A u := by
  classical
  let U : Subgroup Aˣ := chapter10UnitFiltration A 1
  let V : ∀ n : ℕ, Subgroup U := fun n =>
    (chapter10UnitFiltration A (n + 1)).subgroupOf U
  let r : ∀ n : ℕ, U →* Chapter10PrecisionUnitGroup A n := fun n =>
    (Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom).comp
      U.subtype
  have hrker (n : ℕ) : (r n).ker = V n := by
    ext u
    constructor
    · intro hu
      change r n u = 1 at hu
      have hv := congrArg Units.val hu
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
          ((u : Aˣ) : A) = 1 at hv
      change (u : Aˣ) ∈ chapter10UnitFiltration A (n + 1)
      change ((u : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr hv
    · intro hu
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
          ((u : Aˣ) : A) = 1
      rw [← sub_eq_zero]
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
          (((u : Aˣ) : A) - 1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
        change ((u : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
        exact hu)
  have hV (n : ℕ) : V n ≤ (r n).ker := by
    rw [hrker]
  let rbar : ∀ n : ℕ,
      Chapter10PrincipalUnitPrecisionGroup A n →*
        Chapter10PrecisionUnitGroup A n := fun n => by
    change (U ⧸ V n) →* (Chapter10PrecisionQuotient A (n + 1))ˣ
    exact QuotientGroup.lift (V n) (r n) (hV n)
  have hred (n : ℕ) :
      (chapter10AbstractPrecisionUnitTransition A n).comp (rbar (n + 1)) =
        (rbar n).comp (chapter10AbstractPrincipalUnitTransition A n) := by
    change (chapter10PrecisionUnitTransition A (n + 1)).comp (rbar (n + 1)) =
      (rbar n).comp (chapter10PrincipalUnitTransition A n)
    apply QuotientGroup.monoidHom_ext
    ext u
    rfl
  let toFull : Chapter10PrincipalUnitInverseLimit A →*
      Chapter10AdicUnitInverseLimit A :=
    { toFun := fun x =>
        ⟨fun n => rbar n (x.1 n), by
          intro n
          change chapter10AbstractPrecisionUnitTransition A n
              (rbar (n + 1) (x.1 (n + 1))) = rbar n (x.1 n)
          have hh := DFunLike.congr_fun (hred n) (x.1 (n + 1))
          change chapter10AbstractPrecisionUnitTransition A n
              (rbar (n + 1) (x.1 (n + 1))) =
            rbar n (chapter10AbstractPrincipalUnitTransition A n
              (x.1 (n + 1))) at hh
          calc
            chapter10AbstractPrecisionUnitTransition A n
                (rbar (n + 1) (x.1 (n + 1))) =
                rbar n (chapter10AbstractPrincipalUnitTransition A n
                  (x.1 (n + 1))) := hh
            _ = rbar n (x.1 n) := by rw [x.2 n]⟩
      map_one' := by
        apply Subtype.ext
        funext n
        exact (rbar n).map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext n
        exact (rbar n).map_mul _ _ }
  obtain ⟨efull, hef⟩ :=
    chapter10_complete_units_inverse_limit A hcomplete hDVR
  let y : Chapter10PrincipalUnitInverseLimit A → Aˣ := fun x =>
    efull.symm (toFull x)
  have hx0 (x : Chapter10PrincipalUnitInverseLimit A) : x.1 0 = 1 := by
    change x.1 0 = (1 : U ⧸ V 0)
    refine QuotientGroup.induction_on (x.1 0) ?_
    intro u
    change QuotientGroup.mk' (V 0) u = 1
    apply (QuotientGroup.eq_one_iff (N := V 0) u).2
    change (u : Aˣ) ∈ chapter10UnitFiltration A 1
    exact u.property
  have hy1 (x : Chapter10PrincipalUnitInverseLimit A) : y x ∈ U := by
    have hcan : chapter10UnitToAdicInverseLimit A (y x) = toFull x := by
      calc
        chapter10UnitToAdicInverseLimit A (y x) = efull (y x) := (hef (y x)).symm
        _ = toFull x := by simp [y]
    have hcoord := congrArg (fun z : Chapter10AdicUnitInverseLimit A => z.1 0) hcan
    have hcoord' :
        (chapter10UnitToAdicInverseLimit A (y x)).1 0 = rbar 0 (x.1 0) := by
      simpa [toFull] using hcoord
    have hx0' : rbar 0 (x.1 0) = 1 := by
      exact congrArg (rbar 0) (hx0 x) |>.trans ((rbar 0).map_one)
    have hv := congrArg Units.val (hcoord'.trans hx0')
    change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (0 + 1))
        (y x : A) = 1 at hv
    change (y x : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hv
  let lift : Chapter10PrincipalUnitInverseLimit A →* U :=
    { toFun := fun x => ⟨y x, hy1 x⟩
      map_one' := by
        apply Subtype.ext
        change efull.symm (toFull 1) = 1
        rw [toFull.map_one]
        exact efull.symm.map_one
      map_mul' := by
        intro x z
        apply Subtype.ext
        change efull.symm (toFull (x * z)) = efull.symm (toFull x) * efull.symm (toFull z)
        rw [toFull.map_mul, map_mul] }
  have htoFull (u : U) :
      toFull (chapter10PrincipalUnitToAdicInverseLimit A u) =
        chapter10UnitToAdicInverseLimit A (u : Aˣ) := by
    apply Subtype.ext
    funext n
    rfl
  have hleft (u : U) : lift (chapter10PrincipalUnitToAdicInverseLimit A u) = u := by
    apply Subtype.ext
    change y (chapter10PrincipalUnitToAdicInverseLimit A u) = (u : Aˣ)
    dsimp [y]
    rw [htoFull]
    rw [← hef (u : Aˣ)]
    exact efull.symm_apply_apply (u : Aˣ)
  have hrbar_injective (n : ℕ) : Function.Injective (rbar n) := by
    change Function.Injective (QuotientGroup.lift (V n) (r n) (hV n))
    exact (QuotientGroup.injective_lift_iff (V n) (r n) (hV n)).2 (hrker n).symm
  have hright (x : Chapter10PrincipalUnitInverseLimit A) :
      chapter10PrincipalUnitToAdicInverseLimit A (lift x) = x := by
    apply Subtype.ext
    funext n
    apply hrbar_injective n
    have hcan : chapter10UnitToAdicInverseLimit A (y x) = toFull x := by
      calc
        chapter10UnitToAdicInverseLimit A (y x) = efull (y x) := (hef (y x)).symm
        _ = toFull x := by simp [y]
    have hcoord := congrArg (fun z : Chapter10AdicUnitInverseLimit A => z.1 n) hcan
    change rbar n (QuotientGroup.mk' (V n) (lift x)) = rbar n (x.1 n)
    calc
      rbar n (QuotientGroup.mk' (V n) (lift x)) = r n (lift x) := by rfl
      _ = (chapter10UnitToAdicInverseLimit A (y x)).1 n := by rfl
      _ = (toFull x).1 n := hcoord
      _ = rbar n (x.1 n) := by rfl
  let e : U ≃* Chapter10PrincipalUnitInverseLimit A :=
    { toFun := chapter10PrincipalUnitToAdicInverseLimit A
      invFun := lift
      left_inv := hleft
      right_inv := hright
      map_mul' := by
        intro u v
        exact (chapter10PrincipalUnitToAdicInverseLimit A).map_mul u v }
  refine ⟨e, ?_⟩
  intro u
  rfl

/-- Finite residue fields make every finite-precision quotient finite. -/
theorem chapter10_finite_residue_finite_precision_quotients
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Finite (Chapter10ResidueField A)] (n : ℕ)
    (hDVR : IsDiscreteValuationRing A) :
    Finite (Chapter10PrecisionQuotient A (n + 1)) := by
  let _ : IsDiscreteValuationRing A := hDVR
  let _ : Finite (A ⧸ IsLocalRing.maximalIdeal A) := by
    change Finite (Chapter10ResidueField A)
    infer_instance
  exact Ideal.finite_quotient_pow
    (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal A)).fg (n + 1)

private theorem chapter10_unit_filtration_finite_index
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Finite (Chapter10ResidueField A)] (n : ℕ)
    (hDVR : IsDiscreteValuationRing A) :
    (chapter10UnitFiltration A n).FiniteIndex := by
  cases n with
  | zero =>
      rw [chapter10_unit_filtration_zero A]
      infer_instance
  | succ n =>
      let _ : Finite (Chapter10PrecisionQuotient A (n + 1)) :=
        chapter10_finite_residue_finite_precision_quotients A n hDVR
      let f : Aˣ →* (Chapter10PrecisionQuotient A (n + 1))ˣ :=
        Units.map
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom
      have hker : f.ker = chapter10UnitFiltration A (n + 1) := by
        ext u
        constructor
        · intro hu
          change f u = 1 at hu
          have hv := congrArg Units.val hu
          change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
              (u : A) = 1 at hv
          change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          rw [map_sub]
          exact sub_eq_zero.mpr hv
        · intro hu
          apply MonoidHom.mem_ker.mpr
          apply Units.ext
          change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
              (u : A) = 1
          rw [← sub_eq_zero]
          change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
              ((u : A) - 1) = 0
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
            change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
            exact hu)
      rw [← hker]
      infer_instance

/-- Under the adic topology, finite residue fields make the unit group compact. -/
theorem chapter10_finite_residue_unit_group_compact
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Aˣ] [IsTopologicalGroup Aˣ] [CompleteSpace Aˣ]
    [T2Space Aˣ] [Finite (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    Chapter10CompactUnitGroup (G := Aˣ) := by
  classical
  let U : ℕ → Subgroup Aˣ := chapter10UnitFiltration A
  let q : ∀ n : ℕ, Aˣ →* (Aˣ ⧸ U (n + 1)) := fun n =>
    QuotientGroup.mk' (U (n + 1))
  let red : ∀ n : ℕ, Aˣ →* Chapter10PrecisionUnitGroup A n := fun n =>
    Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom
  have hredker (n : ℕ) : (red n).ker = U (n + 1) := by
    ext u
    constructor
    · intro hu
      change red n u = 1 at hu
      have hv := congrArg Units.val hu
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
          (u : A) = 1 at hv
      change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr hv
    · intro hu
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
          (u : A) = 1
      rw [← sub_eq_zero]
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
          ((u : A) - 1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hred_mem (n : ℕ) {a b : Aˣ}
      (hab : a / b ∈ U (n + 1)) : red n a = red n b := by
    have hker : a / b ∈ (red n).ker := by
      rw [hredker]
      exact hab
    have hm : red n (a / b) = 1 := MonoidHom.mem_ker.mp hker
    have hm' : red n a / red n b = 1 := by simpa using hm
    exact div_eq_one.mp hm'
  have hquot_red (n : ℕ) {a b : Aˣ}
      (hab : red n a = red n b) : q n a = q n b := by
    apply (QuotientGroup.eq_iff_div_mem).2
    rw [← hredker]
    apply MonoidHom.mem_ker.mpr
    change red n (a / b) = 1
    simp [map_div, hab]
  apply (isCompact_iff_ultrafilter_le_nhds (s := (Set.univ : Set Aˣ))).2
  intro f hf
  have hfinite (n : ℕ) : Finite (Aˣ ⧸ U (n + 1)) := by
    let _ : (U (n + 1)).FiniteIndex :=
      chapter10_unit_filtration_finite_index A (n + 1) hDVR
    infer_instance
  have hcoset (n : ℕ) :
      ∃ c : Aˣ ⧸ U (n + 1), q n ⁻¹' {c} ∈ (f : Filter Aˣ) := by
    let _ : Finite (Aˣ ⧸ U (n + 1)) := hfinite n
    have hcover :
        (⋃ c : Aˣ ⧸ U (n + 1), q n ⁻¹' ({c} : Set (Aˣ ⧸ U (n + 1)))) =
          Set.univ := by
      ext x
      simp
    have hmem :
        (⋃ c : Aˣ ⧸ U (n + 1), q n ⁻¹' ({c} : Set (Aˣ ⧸ U (n + 1)))) ∈
          (f : Filter Aˣ) := by
      rw [hcover]
      exact Filter.univ_mem
    have hmem' :
        (⋃ c ∈ (Set.univ : Set (Aˣ ⧸ U (n + 1))),
          q n ⁻¹' ({c} : Set (Aˣ ⧸ U (n + 1)))) ∈ (f : Filter Aˣ) := by
      simpa using hmem
    rcases (f.finite_biUnion_mem_iff Set.finite_univ).mp hmem' with
      ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  let c : ∀ n : ℕ, Aˣ ⧸ U (n + 1) := fun n => Classical.choose (hcoset n)
  have hc (n : ℕ) : q n ⁻¹' ({c n} : Set (Aˣ ⧸ U (n + 1))) ∈ (f : Filter Aˣ) :=
    Classical.choose_spec (hcoset n)
  let a : ∀ n : ℕ, Aˣ := fun n =>
    Classical.choose ((QuotientGroup.mk'_surjective (U (n + 1))) (c n))
  have ha (n : ℕ) : q n (a n) = c n :=
    Classical.choose_spec ((QuotientGroup.mk'_surjective (U (n + 1))) (c n))
  have hfactor (n : ℕ) (u : Aˣ) :
      chapter10AbstractPrecisionUnitTransition A n (red (n + 1) u) = red n u := by
    apply Units.ext
    change chapter10PrecisionRingTransition A (n + 1)
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 2)) (u : A)) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1)) (u : A)
    rw [chapter10PrecisionRingTransition, Ideal.Quotient.factor_mk]
  have hselected (n : ℕ) : red n (a (n + 1)) = red n (a n) := by
    obtain ⟨z, hz⟩ := f.nonempty_of_mem
      (Filter.inter_mem (hc (n + 1)) (hc n))
    have hz1 := hz.1
    have hz0 := hz.2
    have hq1 : q (n + 1) (a (n + 1)) = q (n + 1) z := by
      exact (ha (n + 1)).trans (by simpa using hz1.symm)
    have hq0 : q n (a n) = q n z := by
      exact (ha n).trans (by simpa using hz0.symm)
    have hmem1 : a (n + 1) / z ∈ U (n + 2) :=
      (QuotientGroup.eq_iff_div_mem).1 hq1
    have hmem1' : a (n + 1) / z ∈ U (n + 1) :=
      (chapter10_unit_filtration_descending A (n + 1)) hmem1
    have hmem0 : a n / z ∈ U (n + 1) :=
      (QuotientGroup.eq_iff_div_mem).1 hq0
    exact (hred_mem n hmem1').trans (hred_mem n hmem0).symm
  let fam : Chapter10AdicUnitInverseLimit A :=
    ⟨fun n => red n (a n), by
      intro n
      change chapter10AbstractPrecisionUnitTransition A n
          (red (n + 1) (a (n + 1))) = red n (a n)
      exact (hfactor n (a (n + 1))).trans (hselected n)⟩
  obtain ⟨efull, hef⟩ :=
    chapter10_complete_units_inverse_limit A hcomplete hDVR
  let u : Aˣ := efull.symm fam
  have hu_red (n : ℕ) : red n u = red n (a n) := by
    have hcan : chapter10UnitToAdicInverseLimit A u = fam := by
      calc
        chapter10UnitToAdicInverseLimit A u = efull u := (hef u).symm
        _ = fam := by simp [u]
    have hcoord := congrArg (fun z : Chapter10AdicUnitInverseLimit A => z.1 n) hcan
    change red n u = red n (a n) at hcoord
    exact hcoord
  have hq_u (n : ℕ) : q n u = c n := by
    exact (hquot_red n (hu_red n)).trans (ha n)
  refine ⟨u, Set.mem_univ _, ?_⟩
  intro s hs
  have hpre : (fun z : Aˣ => u * z) ⁻¹' s ∈ 𝓝 (1 : Aˣ) :=
    by
      have hs' : s ∈ 𝓝 ((Homeomorph.mulLeft u) (1 : Aˣ)) := by
        simpa using hs
      simpa using
        ((Homeomorph.mulLeft u).continuous.continuousAt (x := (1 : Aˣ))).preimage_mem_nhds hs'
  have htranslate : u⁻¹ • s ∈ 𝓝 (1 : Aˣ) := by
    have heq : (fun z : Aˣ => u * z) ⁻¹' s = u⁻¹ • s := by
      ext z
      constructor
      · intro hz
        change u * z ∈ s at hz
        exact Set.mem_smul_set.mpr ⟨u * z, hz, by simp⟩
      · intro hz
        rcases Set.mem_smul_set.mp hz with ⟨y, hy, hyz⟩
        change u * z ∈ s
        change u⁻¹ * y = z at hyz
        rw [← hyz]
        simpa using hy
    rw [← heq]
    exact hpre
  obtain ⟨k, hk⟩ := htop.2 (u⁻¹ • s) htranslate
  cases k with
  | zero =>
      have hsub₀ : (U 1 : Set Aˣ) ⊆ (U 0 : Set Aˣ) := by
        intro x hx
        exact (chapter10_unit_filtration_descending A 0) hx
      have hsub : (U 1 : Set Aˣ) ⊆ u⁻¹ • s := hsub₀.trans hk
      refine Filter.mem_of_superset (hc 0) ?_
      intro x hx
      have hqx : q 0 x = c 0 := by simpa using hx
      have hqu : q 0 u = c 0 := hq_u 0
      have hdiv : x / u ∈ U 1 := (QuotientGroup.eq_iff_div_mem).1 (hqx.trans hqu.symm)
      have hd : u⁻¹ * x ∈ U 1 := by simpa [div_eq_mul_inv, mul_comm] using hdiv
      rcases Set.mem_smul_set.mp (hsub hd) with ⟨y, hy, hyx⟩
      change u⁻¹ * y = u⁻¹ * x at hyx
      have hxy : x = y := by
        calc
          x = u * (u⁻¹ * x) := by simp
          _ = u * (u⁻¹ * y) :=
            (congrArg (fun z : Aˣ => u * z) hyx).symm
          _ = y := by simp
      rw [hxy]
      exact hy
  | succ k =>
      refine Filter.mem_of_superset (hc k) ?_
      intro x hx
      have hqx : q k x = c k := by simpa using hx
      have hqu : q k u = c k := hq_u k
      have hdiv : x / u ∈ U (k + 1) :=
        (QuotientGroup.eq_iff_div_mem).1 (hqx.trans hqu.symm)
      have hd : u⁻¹ * x ∈ U (k + 1) := by simpa [div_eq_mul_inv, mul_comm] using hdiv
      rcases Set.mem_smul_set.mp (hk hd) with ⟨y, hy, hyx⟩
      change u⁻¹ * y = u⁻¹ * x at hyx
      have hxy : x = y := by
        calc
          x = u * (u⁻¹ * x) := by simp
          _ = u * (u⁻¹ * y) :=
            (congrArg (fun z : Aˣ => u * z) hyx).symm
          _ = y := by simp
      rw [hxy]
      exact hy

/-- Each congruence subgroup is compact and open in the finite-residue case. -/
theorem chapter10_finite_residue_unit_filtration_compact_open
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Aˣ] [IsTopologicalGroup Aˣ] [CompleteSpace Aˣ]
    [T2Space Aˣ] [Finite (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    ∀ n : ℕ,
      IsCompact (chapter10UnitFiltration A n : Set Aˣ) ∧
        IsOpen (chapter10UnitFiltration A n : Set Aˣ) := by
  have hcompact : IsCompact (Set.univ : Set Aˣ) :=
    chapter10_finite_residue_unit_group_compact A hcomplete hDVR htop
  intro n
  have hopen : IsOpen (chapter10UnitFiltration A n : Set Aˣ) := htop.1 n
  have hclosed : IsClosed (chapter10UnitFiltration A n : Set Aˣ) :=
    Subgroup.isClosed_of_isOpen _ hopen
  exact ⟨hcompact.of_isClosed_subset hclosed (Set.subset_univ _), hopen⟩

/-- The valuation direction is discrete and is the only noncompact direction. -/
def Chapter10LocallyCompactButNotCompact
    (G : Type*) [TopologicalSpace G] : Prop :=
  LocallyCompactSpace G ∧ ¬ IsCompact (Set.univ : Set G)

/-- With finite residue field, a complete valued field is locally compact but not compact. -/
theorem chapter10_finite_residue_local_compactness
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Lˣ] [IsTopologicalGroup Lˣ] [CompleteSpace Lˣ]
    [T2Space Lˣ] [Finite (Chapter10ResidueField A)]
    [Valuation.IsRankOneDiscrete A.valuation]
    (π : A) (hπ : Chapter10Uniformizer A π)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10FieldUnitFiltration A)) :
    Chapter10LocallyCompactButNotCompact Lˣ := by
  classical
  let U : ℕ → Subgroup Aˣ := chapter10UnitFiltration A
  let V : ℕ → Subgroup Lˣ := chapter10FieldUnitFiltration A
  let f₀ : Aˣ →* V 0 :=
    { toFun := fun u =>
        ⟨Units.map A.subtype.toMonoidHom u, by
          change Units.map A.subtype.toMonoidHom u ∈
            (U 0).map (Units.map A.subtype.toMonoidHom)
          refine ⟨u, ?_, rfl⟩
          simp [U, chapter10UnitFiltration, chapter10IdealUnitFiltration]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp }
  have hf₀_surjective : Function.Surjective f₀ := by
    intro x
    rcases x.property with ⟨u, hu, hux⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hux
  have hf₀_injective : Function.Injective f₀ := by
    intro u v huv
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun x : V 0 => ((x : Lˣ) : L)) huv
  let ef : Aˣ ≃* V 0 := MulEquiv.ofBijective f₀
    ⟨hf₀_injective, hf₀_surjective⟩
  let W : ∀ n : ℕ, Subgroup (V 0) := fun n =>
    (V (n + 1)).subgroupOf (V 0)
  have hWfiniteIndex (n : ℕ) : (W n).FiniteIndex := by
    let _ : (U (n + 1)).FiniteIndex :=
      chapter10_unit_filtration_finite_index A (n + 1) hDVR
    let _ : Finite (Aˣ ⧸ U (n + 1)) := inferInstance
    let F : Aˣ →* (V 0 ⧸ W n) :=
      (QuotientGroup.mk' (W n)).comp ef.toMonoidHom
    have hFsurjective : Function.Surjective F := by
      exact (QuotientGroup.mk'_surjective _).comp ef.surjective
    have hFker : F.ker = U (n + 1) := by
      ext u
      constructor
      · intro hu
        change F u = 1 at hu
        have huW : (ef u : V 0) ∈ W n :=
          (QuotientGroup.eq_one_iff _).1 hu
        change (ef u : Lˣ) ∈ V (n + 1) at huW
        rcases huW with ⟨a, ha, hEq⟩
        have heq : ef u = ef (a : Aˣ) := by
          apply Subtype.ext
          change Units.map A.subtype.toMonoidHom u =
            Units.map A.subtype.toMonoidHom (a : Aˣ)
          exact hEq.symm
        rw [ef.injective heq]
        exact ha
      · intro hu
        apply MonoidHom.mem_ker.mpr
        change QuotientGroup.mk' (W n) (ef u) = 1
        apply (QuotientGroup.eq_one_iff _).2
        change (ef u : Lˣ) ∈ V (n + 1)
        change Units.map A.subtype.toMonoidHom u ∈
          (U (n + 1)).map (Units.map A.subtype.toMonoidHom)
        exact ⟨u, hu, rfl⟩
    let eQ : (Aˣ ⧸ U (n + 1)) ≃* (V 0 ⧸ W n) :=
      (QuotientGroup.quotientMulEquivOfEq hFker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective F hFsurjective)
    let _ : Finite (V 0 ⧸ W n) := Finite.of_equiv _ eQ.toEquiv
    exact Subgroup.finiteIndex_of_finite_quotient
  have hV0compact : IsCompact (V 0 : Set Lˣ) := by
    apply (isCompact_iff_ultrafilter_le_nhds (s := (V 0 : Set Lˣ))).2
    intro f hf
    have hmemV0 : (V 0 : Set Lˣ) ∈ (f : Filter Lˣ) :=
      (le_principal_iff.1 hf)
    have hlarge : Set.range (fun x : V 0 => (x : Lˣ)) ∈ (f : Filter Lˣ) := by
      have hrange : Set.range (fun x : V 0 => (x : Lˣ)) = (V 0 : Set Lˣ) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
      rw [hrange]
      exact hmemV0
    let fV : Ultrafilter (V 0) :=
      Ultrafilter.comap f Subtype.val_injective hlarge
    have hcoset (n : ℕ) :
        ∃ g : (⊤ : Subgroup (V 0)),
          (g : V 0) • (W n : Set (V 0)) ∈ (fV : Filter (V 0)) := by
      let _ : (W n).FiniteIndex := hWfiniteIndex n
      obtain ⟨t, ht, hcover⟩ :=
        Subgroup.exists_leftTransversal_of_FiniteIndex
          (D := W n) (H := (⊤ : Subgroup (V 0))) (by
            intro x hx
            trivial)
      have hmem :
          (⋃ g ∈ t, (g : V 0) • (W n : Set (V 0))) ∈ (fV : Filter (V 0)) := by
        rw [hcover]
        exact Filter.univ_mem
      have hmem' :
          (⋃ g ∈ (t : Set (⊤ : Subgroup (V 0))),
            (g : V 0) • (W n : Set (V 0))) ∈ (fV : Filter (V 0)) := by
        simpa using hmem
      rcases (fV.finite_biUnion_mem_iff t.finite_toSet).mp hmem' with
        ⟨g, -, hg⟩
      exact ⟨g, hg⟩
    let g : ∀ n : ℕ, (⊤ : Subgroup (V 0)) := fun n =>
      Classical.choose (hcoset n)
    have hg (n : ℕ) :
        (g n : V 0) • (W n : Set (V 0)) ∈ (fV : Filter (V 0)) :=
      Classical.choose_spec (hcoset n)
    let b : ∀ n : ℕ, Aˣ := fun n => ef.symm (g n : V 0)
    have hb (n : ℕ) : ef (b n) = g n := by
      simp [b]
    let red : ∀ n : ℕ, Aˣ →* Chapter10PrecisionUnitGroup A n := fun n =>
      Units.map
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))).toMonoidHom
    have hredker (n : ℕ) : (red n).ker = U (n + 1) := by
      ext u
      constructor
      · intro hu
        change red n u = 1 at hu
        have hv := congrArg Units.val hu
        change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
            (u : A) = 1 at hv
        change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub]
        exact sub_eq_zero.mpr hv
      · intro hu
        apply MonoidHom.mem_ker.mpr
        apply Units.ext
        change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
            (u : A) = 1
        rw [← sub_eq_zero]
        change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1))
            ((u : A) - 1) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
          change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
          exact hu)
    have hred_mem (n : ℕ) {a c : Aˣ}
        (hac : a / c ∈ U (n + 1)) : red n a = red n c := by
      have hker : a / c ∈ (red n).ker := by
        rw [hredker]
        exact hac
      have hm : red n (a / c) = 1 := MonoidHom.mem_ker.mp hker
      have hm' : red n a / red n c = 1 := by simpa using hm
      exact div_eq_one.mp hm'
    have hquot_red (n : ℕ) {a c : Aˣ}
        (hac : red n a = red n c) :
        QuotientGroup.mk' (U (n + 1)) a = QuotientGroup.mk' (U (n + 1)) c := by
      apply (QuotientGroup.eq_iff_div_mem).2
      rw [← hredker]
      apply MonoidHom.mem_ker.mpr
      change red n (a / c) = 1
      simp [map_div, hac]
    have hselected (n : ℕ) : red n (b (n + 1)) = red n (b n) := by
      obtain ⟨z, hz⟩ := fV.nonempty_of_mem
        (Filter.inter_mem (hg (n + 1)) (hg n))
      have hz1 := hz.1
      have hz0 := hz.2
      rcases Set.mem_smul_set.mp hz1 with ⟨w1, hw1, hrel1⟩
      rcases Set.mem_smul_set.mp hz0 with ⟨w0, hw0, hrel0⟩
      change (w1 : Lˣ) ∈ V (n + 2) at hw1
      change (w0 : Lˣ) ∈ V (n + 1) at hw0
      rcases hw1 with ⟨d1, hd1, hwd1⟩
      rcases hw0 with ⟨d0, hd0, hwd0⟩
      obtain ⟨bz, hbz⟩ := ef.surjective z
      have hEd1 : ef d1 = w1 := by
        apply Subtype.ext
        change Units.map A.subtype.toMonoidHom d1 = (w1 : Lˣ)
        exact hwd1
      have hEd0 : ef d0 = w0 := by
        apply Subtype.ext
        change Units.map A.subtype.toMonoidHom d0 = (w0 : Lˣ)
        exact hwd0
      have hrel1' : (g (n + 1) : Lˣ) * (w1 : Lˣ) = (z : Lˣ) := by
        change (g (n + 1) : V 0) • w1 = z at hrel1
        exact congrArg (fun x : V 0 => (x : Lˣ)) hrel1
      have hrel0' : (g n : Lˣ) * (w0 : Lˣ) = (z : Lˣ) := by
        change (g n : V 0) • w0 = z at hrel0
        exact congrArg (fun x : V 0 => (x : Lˣ)) hrel0
      have heq1 : b (n + 1) * d1 = bz := by
        apply ef.injective
        calc
          ef (b (n + 1) * d1) = ef (b (n + 1)) * ef d1 := by rw [map_mul]
          _ = (g (n + 1) : V 0) * w1 := by rw [hb, hEd1]
          _ = z := hrel1
          _ = ef bz := hbz.symm
      have heq0 : b n * d0 = bz := by
        apply ef.injective
        calc
          ef (b n * d0) = ef (b n) * ef d0 := by rw [map_mul]
          _ = (g n : V 0) * w0 := by rw [hb, hEd0]
          _ = z := hrel0
          _ = ef bz := hbz.symm
      have hmem1 : b (n + 1) / bz ∈ U (n + 2) := by
        have hratio : b (n + 1) / bz = d1⁻¹ := by
          rw [← heq1]
          simp [div_eq_mul_inv]
        rw [hratio]
        exact (U (n + 2)).inv_mem hd1
      have hmem1' : b (n + 1) / bz ∈ U (n + 1) :=
        (chapter10_unit_filtration_descending A (n + 1)) hmem1
      have hmem0 : b n / bz ∈ U (n + 1) := by
        have hratio : b n / bz = d0⁻¹ := by
          rw [← heq0]
          simp [div_eq_mul_inv]
        rw [hratio]
        exact (U (n + 1)).inv_mem hd0
      exact (hred_mem n hmem1').trans (hred_mem n hmem0).symm
    let fam : Chapter10AdicUnitInverseLimit A :=
      ⟨fun n => red n (b n), by
        intro n
        change chapter10AbstractPrecisionUnitTransition A n
            (red (n + 1) (b (n + 1))) = red n (b n)
        have hfactor (n : ℕ) (u : Aˣ) :
            chapter10AbstractPrecisionUnitTransition A n (red (n + 1) u) = red n u := by
          apply Units.ext
          change chapter10PrecisionRingTransition A (n + 1)
              (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 2)) (u : A)) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n + 1)) (u : A)
          rw [chapter10PrecisionRingTransition, Ideal.Quotient.factor_mk]
        exact (hfactor n (b (n + 1))).trans (hselected n)⟩
    obtain ⟨efull, hef⟩ :=
      chapter10_complete_units_inverse_limit A hcomplete hDVR
    let u : Aˣ := efull.symm fam
    have hu_red (n : ℕ) : red n u = red n (b n) := by
      have hcan : chapter10UnitToAdicInverseLimit A u = fam := by
        calc
          chapter10UnitToAdicInverseLimit A u = efull u := (hef u).symm
          _ = fam := by simp [u]
      have hcoord := congrArg (fun z : Chapter10AdicUnitInverseLimit A => z.1 n) hcan
      change red n u = red n (b n) at hcoord
      exact hcoord
    have hfield_rel (n : ℕ) :
        ((ef u : V 0) : Lˣ) / (g n : Lˣ) ∈ V (n + 1) := by
      have hq : QuotientGroup.mk' (U (n + 1)) u =
          QuotientGroup.mk' (U (n + 1)) (b n) :=
        hquot_red n (hu_red n)
      have hring : u / b n ∈ U (n + 1) :=
        (QuotientGroup.eq_iff_div_mem).1 hq
      have hmap : Units.map A.subtype.toMonoidHom (u / b n) ∈
          (U (n + 1)).map (Units.map A.subtype.toMonoidHom) :=
        ⟨u / b n, hring, rfl⟩
      have hgb : (g n : Lˣ) =
          Units.map A.subtype.toMonoidHom (b n) := by
        exact congrArg (fun x : V 0 => (x : Lˣ)) (hb n).symm
      change ((ef u : V 0) : Lˣ) / (g n : Lˣ) ∈
        (U (n + 1)).map (Units.map A.subtype.toMonoidHom)
      rw [hgb]
      change Units.map A.subtype.toMonoidHom u /
          Units.map A.subtype.toMonoidHom (b n) ∈
        (U (n + 1)).map (Units.map A.subtype.toMonoidHom)
      simpa [map_div] using hmap
    have hconv : (f : Filter Lˣ) ≤ 𝓝 ((ef u : V 0) : Lˣ) := by
      intro s hs
      let x₀ : Lˣ := (ef u : V 0)
      have hs' : s ∈ 𝓝 x₀ := by
        simpa [x₀] using hs
      have hpre : (fun z : Lˣ => x₀ * z) ⁻¹' s ∈ 𝓝 (1 : Lˣ) := by
        have hs'' : s ∈ 𝓝 ((Homeomorph.mulLeft x₀) (1 : Lˣ)) := by
          simpa using hs'
        simpa using
          ((Homeomorph.mulLeft x₀).continuous.continuousAt (x := (1 : Lˣ))).preimage_mem_nhds hs''
      have htranslate : x₀⁻¹ • s ∈ 𝓝 (1 : Lˣ) := by
        have heq : (fun z : Lˣ => x₀ * z) ⁻¹' s = x₀⁻¹ • s := by
          ext z
          constructor
          · intro hz
            change x₀ * z ∈ s at hz
            exact Set.mem_smul_set.mpr ⟨x₀ * z, hz, by simp⟩
          · intro hz
            rcases Set.mem_smul_set.mp hz with ⟨y, hy, hyz⟩
            change x₀ * z ∈ s
            change x₀⁻¹ * y = z at hyz
            rw [← hyz]
            simpa using hy
        rw [← heq]
        exact hpre
      obtain ⟨k, hk⟩ := htop.2 (x₀⁻¹ • s) htranslate
      change (V k : Set Lˣ) ⊆ x₀⁻¹ • s at hk
      have hgfield (k : ℕ) :
          (fun z : V 0 => (z : Lˣ)) ''
              ((g k : V 0) • (W k : Set (V 0))) ∈ (f : Filter Lˣ) := by
        apply (Ultrafilter.mem_comap f Subtype.val_injective hlarge).1
        change (g k : V 0) • (W k : Set (V 0)) ∈ (fV : Filter (V 0))
        exact hg k
      have hcoset_subset (k : ℕ)
          (hsubk : (V (k + 1) : Set Lˣ) ⊆ x₀⁻¹ • s) :
          (fun z : V 0 => (z : Lˣ)) ''
              ((g k : V 0) • (W k : Set (V 0))) ⊆ s := by
        rintro y ⟨z, hz, rfl⟩
        rcases Set.mem_smul_set.mp hz with ⟨w, hw, hzw⟩
        change (w : Lˣ) ∈ V (k + 1) at hw
        have hxg : x₀⁻¹ * (g k : Lˣ) ∈ V (k + 1) := by
          have hi :
              (((ef u : V 0) : Lˣ) / (g k : Lˣ))⁻¹ ∈ V (k + 1) :=
            (V (k + 1)).inv_mem (hfield_rel k)
          have hi' : (g k : Lˣ) / ((ef u : V 0) : Lˣ) ∈ V (k + 1) := by
            simpa only [inv_div] using hi
          change ((ef u : V 0) : Lˣ)⁻¹ * (g k : Lˣ) ∈ V (k + 1)
          simpa only [div_eq_inv_mul] using hi'
        have hprod : x₀⁻¹ * (g k : Lˣ) * (w : Lˣ) ∈ V (k + 1) :=
          (V (k + 1)).mul_mem hxg hw
        have htranslated : x₀⁻¹ * (g k : Lˣ) * (w : Lˣ) ∈ x₀⁻¹ • s :=
          hsubk hprod
        rcases Set.mem_smul_set.mp htranslated with ⟨v, hv, hvrel⟩
        have hzrel : (g k : Lˣ) * (w : Lˣ) = (z : Lˣ) := by
          change (g k : V 0) * w = z at hzw
          exact congrArg (fun q : V 0 => (q : Lˣ)) hzw
        have hvrel' : x₀⁻¹ * v =
            x₀⁻¹ * (g k : Lˣ) * (w : Lˣ) := by
          change x₀⁻¹ * v = x₀⁻¹ * (g k : Lˣ) * (w : Lˣ) at hvrel
          exact hvrel
        have hvz : v = (z : Lˣ) := by
          calc
            v = x₀ * (x₀⁻¹ * v) := by simp
            _ = x₀ * (x₀⁻¹ * (g k : Lˣ) * (w : Lˣ)) := by rw [hvrel']
            _ = x₀ * (x₀⁻¹ * ((g k : Lˣ) * (w : Lˣ))) := by rw [mul_assoc]
            _ = (g k : Lˣ) * (w : Lˣ) := by
              exact mul_inv_cancel_left x₀ _
            _ = z := hzrel
        change (z : Lˣ) ∈ s
        rw [← hvz]
        exact hv
      cases k with
      | zero =>
          have hsub₀ : (V 1 : Set Lˣ) ⊆ (V 0 : Set Lˣ) := by
            intro x hx
            change x ∈ (U 0).map (Units.map A.subtype.toMonoidHom)
            change x ∈ (U 1).map (Units.map A.subtype.toMonoidHom) at hx
            rcases hx with ⟨a, ha, hax⟩
            exact ⟨a, (chapter10_unit_filtration_descending A 0) ha, hax⟩
          exact Filter.mem_of_superset (hgfield 0)
            (hcoset_subset 0 (hsub₀.trans hk))
      | succ k =>
          exact Filter.mem_of_superset (hgfield k) (hcoset_subset k hk)
    refine ⟨ef u, (ef u).property, ?_⟩
    exact hconv
  have hV0open : IsOpen (V 0 : Set Lˣ) := by
    change IsOpen (chapter10FieldUnitFiltration A 0 : Set Lˣ)
    exact htop.1 0
  have hV0nhds : (V 0 : Set Lˣ) ∈ 𝓝 (1 : Lˣ) := by
    apply hV0open.mem_nhds
    change (1 : Lˣ) ∈ chapter10FieldUnitFiltration A 0
    exact (chapter10FieldUnitFiltration A 0).one_mem
  have hlocal : LocallyCompactSpace Lˣ :=
    hV0compact.locallyCompactSpace_of_mem_nhds_of_group hV0nhds
  have hnot : ¬ IsCompact (Set.univ : Set Lˣ) := by
    intro hcompact
    let _ : CompactSpace Lˣ := ⟨hcompact⟩
    have hquot : Finite (Lˣ ⧸ V 0) :=
      Subgroup.quotient_finite_of_isOpen (V 0) hV0open
    obtain ⟨eZ⟩ := chapter10_field_unit_quotient_by_ring_units A π hπ
    let _ : Finite (Multiplicative ℤ) := Finite.of_equiv _ eZ.toEquiv
    exact not_finite (Multiplicative ℤ)
  exact ⟨hlocal, hnot⟩

/-- An infinite residue-unit quotient obstructs compactness of the unit group. -/
theorem chapter10_infinite_residue_prevents_unit_compactness
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ] [TopologicalSpace (Chapter10ResidueField A)ˣ]
    [Infinite (Chapter10ResidueField A)]
    (hquotient_discrete :
      ∀ s : Set (Chapter10ResidueField A)ˣ,
        IsOpen s)
    (hresidue_surjective : Function.Surjective (chapter10UnitReduction A))
    (hresidue_continuous : Continuous (chapter10UnitReduction A)) :
    ¬ Chapter10CompactUnitGroup (G := Aˣ) := by
  classical
  intro hcompact
  let _ : CompactSpace Aˣ := ⟨hcompact⟩
  let _ : DiscreteTopology (Chapter10ResidueField A)ˣ :=
    ⟨eq_bot_of_singletons_open (fun x => hquotient_discrete {x})⟩
  have hrange : IsCompact (Set.range (chapter10UnitReduction A)) := by
    simpa only [Set.image_univ, hresidue_surjective.range_eq] using
      (isCompact_univ.image hresidue_continuous)
  have hfinite : (Set.range (chapter10UnitReduction A)).Finite :=
    hrange.finite_of_discrete
  have huniv : (Set.univ : Set (Chapter10ResidueField A)ˣ).Finite := by
    simpa only [hresidue_surjective.range_eq] using hfinite
  let _ : Finite (Chapter10ResidueField A)ˣ :=
    Finite.of_finite_univ huniv
  let f : Chapter10ResidueField A →
      (Chapter10ResidueField A)ˣ ⊕ Unit :=
    fun x => if hx : x = 0 then Sum.inr () else Sum.inl (Units.mk0 x hx)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · simp [hx, hy]
    · simp [f, hx, hy] at hxy
    · simp [f, hx, hy] at hxy
    · have hunit : Units.mk0 x hx = Units.mk0 y hy := by
        simpa [f, hx, hy] using hxy
      exact congrArg Units.val hunit
  have hfinite_residue : Finite (Chapter10ResidueField A) := by
    exact Finite.of_injective f hf
  let _ : Finite (Chapter10ResidueField A) := hfinite_residue
  exact not_finite (Chapter10ResidueField A)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
