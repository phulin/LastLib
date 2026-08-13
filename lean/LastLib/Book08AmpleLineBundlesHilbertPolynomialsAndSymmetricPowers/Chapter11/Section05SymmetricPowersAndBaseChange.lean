import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section04UniversalDivisorOnASmoothCurve

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeScheme

universe u v

/-!
### 11.5 Symmetric powers and base change
-/

theorem symmetricPower_curve_base_change_iso {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] (T : RelativeScheme S) :
    ∃ e : RelativeScheme.Iso
        (RelativeScheme.baseChange (symmetricPower C d) T)
        (symmetricPower (RelativeScheme.baseChange C T) d),
      RelativeScheme.baseChangeHom (symmetricPowerMap C d) T ≫ e.hom =
        relativePowerBaseChangeComparison C T d ≫
          symmetricPowerMap (RelativeScheme.baseChange C T) d := by
  sorry

theorem universalDivisor_proves_all_base_change {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    ∀ T : RelativeScheme S,
      ∃ e : RelativeScheme.Iso
          (RelativeScheme.baseChange (symmetricPower C d) T)
          (symmetricPower (RelativeScheme.baseChange C T) d),
        RelativeScheme.baseChangeHom (symmetricPowerMap C d) T ≫ e.hom =
          relativePowerBaseChangeComparison C T d ≫
            symmetricPowerMap (RelativeScheme.baseChange C T) d := by
  intro T
  exact symmetricPower_curve_base_change_iso C d T

theorem symmetricPower_curve_smooth {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    SmoothOfRelativeDimension d (symmetricPower C d).structuralMap := by
  sorry

noncomputable def symmetricPowerAddition {S : Scheme.{u}} (C : RelativeScheme S)
    (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier ⟶
      symmetricPower C (d + e) := by
  let P := relativeProduct (symmetricPower C d) (symmetricPower C e)
  let Dd := pullbackUniversalDivisor C P.carrier d P.fst
  let De := pullbackUniversalDivisor C P.carrier e P.snd
  let D : RelativeEffectiveCartierDivisor C P.carrier (d + e) :=
    { divisor := Dd.divisor.add De.divisor
      finite_flat_rank := relativeEffectiveCartierDivisor_add_rank d e Dd De }
  exact divisorToSymmetricPoint C P.carrier (d + e) D

theorem symmetricPowerAddition_from_divisor_sum {S : Scheme.{u}}
    (C : RelativeScheme S) (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    ∃ D : RelativeEffectiveCartierDivisor C
        (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier (d + e),
      D.divisor =
          (pullbackUniversalDivisor C
            (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier d
            (relativeProduct (symmetricPower C d) (symmetricPower C e)).fst).divisor.add
            (pullbackUniversalDivisor C
              (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier e
              (relativeProduct (symmetricPower C d) (symmetricPower C e)).snd).divisor ∧
      Chapter11FiniteLocallyFreeOfRank
        (D.divisor.inclusion ≫
          pullback.snd C.structuralMap
            (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier.structuralMap)
        (d + e) := by
  sorry

noncomputable def relativeProduct_swap_iso {S : Scheme.{u}} (X Y : RelativeScheme S) :
    RelativeScheme.Iso (relativeProduct X Y).carrier (relativeProduct Y X).carrier := by
  sorry

noncomputable def symmetricPower_index_swap_iso {S : Scheme.{u}} (C : RelativeScheme S) (d e : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    RelativeScheme.Iso (symmetricPower C (d + e)) (symmetricPower C (e + d)) := by
  rw [Nat.add_comm]
  exact RelativeScheme.Iso.refl _

noncomputable def symmetricPower_index_assoc_iso {S : Scheme.{u}} (C : RelativeScheme S)
    (d e f : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    RelativeScheme.Iso (symmetricPower C (d + (e + f)))
      (symmetricPower C ((d + e) + f)) := by
  rw [Nat.add_assoc]
  exact RelativeScheme.Iso.refl _

noncomputable def symmetricPower_zero_add_iso {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    RelativeScheme.Iso (symmetricPower C (0 + d)) (symmetricPower C d) := by
  rw [Nat.zero_add]
  exact RelativeScheme.Iso.refl _

noncomputable def symmetricPower_add_zero_iso {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    RelativeScheme.Iso (symmetricPower C (d + 0)) (symmetricPower C d) := by
  rw [Nat.add_zero]
  exact RelativeScheme.Iso.refl _

def Chapter11AdditionCommutativityStatement {S : Scheme.{u}} (C : RelativeScheme S)
    (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  ∃ eSwap : RelativeScheme.Iso
      (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
      (relativeProduct (symmetricPower C e) (symmetricPower C d)).carrier,
    eSwap.hom ≫ (relativeProduct (symmetricPower C e)
      (symmetricPower C d)).fst =
        (relativeProduct (symmetricPower C d)
          (symmetricPower C e)).snd ∧
    eSwap.hom ≫ (relativeProduct (symmetricPower C e)
      (symmetricPower C d)).snd =
        (relativeProduct (symmetricPower C d)
          (symmetricPower C e)).fst ∧
    eSwap.hom ≫ symmetricPowerAddition C e d =
      symmetricPowerAddition C d e ≫ (symmetricPower_index_swap_iso C d e).hom

theorem symmetricPowerAddition_commutative {S : Scheme.{u}} (C : RelativeScheme S)
    (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11AdditionCommutativityStatement C d e := by
  sorry

def Chapter11AdditionLeftUnitStatement {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  ∃ e : RelativeScheme.Iso
      (relativeProduct (symmetricPower C 0) (symmetricPower C d)).carrier
      (symmetricPower C d),
    e.hom = symmetricPowerAddition C 0 d ≫ (symmetricPower_zero_add_iso C d).hom

def Chapter11AdditionRightUnitStatement {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  ∃ e : RelativeScheme.Iso
      (relativeProduct (symmetricPower C d) (symmetricPower C 0)).carrier
      (symmetricPower C d),
    e.hom = symmetricPowerAddition C d 0 ≫ (symmetricPower_add_zero_iso C d).hom

theorem symmetricPowerAddition_left_unit {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11AdditionLeftUnitStatement C d := by
  sorry

theorem symmetricPowerAddition_right_unit {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11AdditionRightUnitStatement C d := by
  sorry

noncomputable def leftAssociatedAddition {S : Scheme.{u}} (C : RelativeScheme S)
    (d e f : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    (relativeProduct (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
      (symmetricPower C f)).carrier ⟶ symmetricPower C ((d + e) + f) := by
  let P := relativeProduct (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
      (symmetricPower C f)
  let Q := relativeProduct (symmetricPower C (d + e)) (symmetricPower C f)
  exact RelativeProduct.lift Q
      (P.fst ≫ symmetricPowerAddition C d e) P.snd ≫
        symmetricPowerAddition C (d + e) f

noncomputable def rightAssociatedAddition {S : Scheme.{u}} (C : RelativeScheme S)
    (d e f : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    (relativeProduct (symmetricPower C d)
      (relativeProduct (symmetricPower C e) (symmetricPower C f)).carrier).carrier ⟶
      symmetricPower C (d + (e + f)) := by
  let P := relativeProduct (symmetricPower C d)
      (relativeProduct (symmetricPower C e) (symmetricPower C f)).carrier
  let Q := relativeProduct (symmetricPower C d) (symmetricPower C (e + f))
  exact RelativeProduct.lift Q P.fst
      (P.snd ≫ symmetricPowerAddition C e f) ≫
        symmetricPowerAddition C d (e + f)

def Chapter11AdditionAssociativityStatement {S : Scheme.{u}} (C : RelativeScheme S)
    (d e f : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  ∃ eAssoc : RelativeScheme.Iso
      (relativeProduct (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
        (symmetricPower C f)).carrier
      (relativeProduct (symmetricPower C d)
        (relativeProduct (symmetricPower C e) (symmetricPower C f)).carrier).carrier,
    eAssoc.hom ≫
        (relativeProduct (symmetricPower C d)
          (relativeProduct (symmetricPower C e) (symmetricPower C f)).carrier).fst =
      (relativeProduct (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
        (symmetricPower C f)).fst ≫
        (relativeProduct (symmetricPower C d) (symmetricPower C e)).fst ∧
    eAssoc.hom ≫
        (relativeProduct (symmetricPower C d)
          (relativeProduct (symmetricPower C e) (symmetricPower C f)).carrier).snd ≫
        (relativeProduct (symmetricPower C e) (symmetricPower C f)).fst =
      (relativeProduct (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
        (symmetricPower C f)).fst ≫
        (relativeProduct (symmetricPower C d) (symmetricPower C e)).snd ∧
    eAssoc.hom ≫
        (relativeProduct (symmetricPower C d)
          (relativeProduct (symmetricPower C e) (symmetricPower C f)).carrier).snd ≫
        (relativeProduct (symmetricPower C e) (symmetricPower C f)).snd =
      (relativeProduct (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
        (symmetricPower C f)).snd ∧
    eAssoc.hom ≫ rightAssociatedAddition C d e f ≫
        (symmetricPower_index_assoc_iso C d e f).hom =
      leftAssociatedAddition C d e f

theorem symmetricPowerAddition_associative {S : Scheme.{u}} (C : RelativeScheme S)
    (d e f : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11AdditionAssociativityStatement C d e f := by
  sorry

noncomputable def relativeProductBaseChangeComparison {S : Scheme.{u}}
    (C T : RelativeScheme S) (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    RelativeScheme.baseChange
      (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier T
      ⟶ (relativeProduct (symmetricPower (RelativeScheme.baseChange C T) d)
        (symmetricPower (RelativeScheme.baseChange C T) e)).carrier := by
  let P := relativeProduct (symmetricPower (RelativeScheme.baseChange C T) d)
      (symmetricPower (RelativeScheme.baseChange C T) e)
  exact RelativeProduct.lift P
    (RelativeScheme.baseChangeHom (relativeProduct (symmetricPower C d)
      (symmetricPower C e)).fst T ≫ (symmetricPower_curve_base_change_iso C d T).choose.hom)
    (RelativeScheme.baseChangeHom (relativeProduct (symmetricPower C d)
      (symmetricPower C e)).snd T ≫ (symmetricPower_curve_base_change_iso C e T).choose.hom)

theorem relativeProductBaseChangeComparison_isIso {S : Scheme.{u}}
    (C T : RelativeScheme S) (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    IsIso (relativeProductBaseChangeComparison C T d e) := by
  sorry

theorem symmetricPowerAddition_base_change {S : Scheme.{u}} (C : RelativeScheme S)
    (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] (T : RelativeScheme S) :
    RelativeScheme.baseChangeHom (symmetricPowerAddition C d e) T ≫
        (symmetricPower_curve_base_change_iso C (d + e) T).choose.hom =
      relativeProductBaseChangeComparison C T d e ≫
        symmetricPowerAddition (RelativeScheme.baseChange C T) d e := by
  sorry

structure Chapter11GradedCommutativeMonoidScheme {S : Scheme.{u}} where
  component : ℕ → RelativeScheme S
  zero : RelativeScheme.Iso (component 0) (RelativeScheme.base S)
  add : ∀ (d e : ℕ), (relativeProduct (component d) (component e)).carrier ⟶ component (d + e)
  zeroAdd : ∀ d : ℕ, RelativeScheme.Iso (component (0 + d)) (component d)
  addZero : ∀ d : ℕ, RelativeScheme.Iso (component (d + 0)) (component d)
  addAssoc : ∀ d e f : ℕ,
    RelativeScheme.Iso (component (d + (e + f))) (component ((d + e) + f))
  addSwap : ∀ d e : ℕ,
    RelativeScheme.Iso (component (d + e)) (component (e + d))
  leftAssociated : ∀ d e f : ℕ,
    (relativeProduct (relativeProduct (component d) (component e)).carrier
      (component f)).carrier ⟶ component ((d + e) + f)
  rightAssociated : ∀ d e f : ℕ,
    (relativeProduct (component d)
      (relativeProduct (component e) (component f)).carrier).carrier ⟶
      component (d + (e + f))
  leftUnit : ∀ d : ℕ,
    ∃ e : RelativeScheme.Iso
        (relativeProduct (component 0) (component d)).carrier (component d),
      e.hom = add 0 d ≫ (zeroAdd d).hom
  rightUnit : ∀ d : ℕ,
    ∃ e : RelativeScheme.Iso
        (relativeProduct (component d) (component 0)).carrier (component d),
      e.hom = add d 0 ≫ (addZero d).hom
  commutative : ∀ d e : ℕ,
    ∃ eSwap : RelativeScheme.Iso
        (relativeProduct (component d) (component e)).carrier
        (relativeProduct (component e) (component d)).carrier,
      eSwap.hom ≫ (relativeProduct (component e)
        (component d)).fst = (relativeProduct (component d)
          (component e)).snd ∧
      eSwap.hom ≫ (relativeProduct (component e)
        (component d)).snd = (relativeProduct (component d)
          (component e)).fst ∧
      eSwap.hom ≫ add e d = add d e ≫ (addSwap d e).hom
  associative : ∀ d e f : ℕ,
    ∃ eAssoc : RelativeScheme.Iso
        (relativeProduct (relativeProduct (component d) (component e)).carrier
          (component f)).carrier
        (relativeProduct (component d)
          (relativeProduct (component e) (component f)).carrier).carrier,
      eAssoc.hom ≫
          (relativeProduct (component d)
            (relativeProduct (component e) (component f)).carrier).fst =
        (relativeProduct (relativeProduct (component d) (component e)).carrier
          (component f)).fst ≫ (relativeProduct (component d) (component e)).fst ∧
      eAssoc.hom ≫
          (relativeProduct (component d)
            (relativeProduct (component e) (component f)).carrier).snd ≫
          (relativeProduct (component e) (component f)).fst =
        (relativeProduct (relativeProduct (component d) (component e)).carrier
          (component f)).fst ≫ (relativeProduct (component d) (component e)).snd ∧
      eAssoc.hom ≫
          (relativeProduct (component d)
            (relativeProduct (component e) (component f)).carrier).snd ≫
          (relativeProduct (component e) (component f)).snd =
        (relativeProduct (relativeProduct (component d) (component e)).carrier
          (component f)).snd ∧
      eAssoc.hom ≫ rightAssociated d e f ≫
          (addAssoc d e f).hom =
        leftAssociated d e f

noncomputable def symmetricPowerGradedCommutativeMonoid {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11GradedCommutativeMonoidScheme (S := S) where
  component := fun d => symmetricPower C d
  zero := symmetricPower_zero_iso C
  add := fun d e => symmetricPowerAddition C d e
  zeroAdd := fun d => symmetricPower_zero_add_iso C d
  addZero := fun d => symmetricPower_add_zero_iso C d
  addAssoc := fun d e f => symmetricPower_index_assoc_iso C d e f
  addSwap := fun d e => symmetricPower_index_swap_iso C d e
  leftAssociated := fun d e f => leftAssociatedAddition C d e f
  rightAssociated := fun d e f => rightAssociatedAddition C d e f
  leftUnit := fun d => by
    simpa [Chapter11AdditionLeftUnitStatement] using symmetricPowerAddition_left_unit C d
  rightUnit := fun d => by
    simpa [Chapter11AdditionRightUnitStatement] using symmetricPowerAddition_right_unit C d
  commutative := fun d e => by
    simpa [Chapter11AdditionCommutativityStatement] using symmetricPowerAddition_commutative C d e
  associative := by sorry

/- SOURCE_ISSUE: §11.5 says that the graded union is not finite type without
   spelling out the quasi-compactness distinction.  The formal statement uses
   the finite-type package `QuasiCompact ∧ LocallyOfFiniteType`; an infinite
   coproduct can still be locally of finite type. -/
noncomputable def symmetricPowerDisjointUnion {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C] : Scheme.{u} :=
  ∐ fun d : ℕ => (symmetricPower C d).carrier

noncomputable def symmetricPowerDisjointUnionMap {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C] :
    symmetricPowerDisjointUnion C ⟶ S :=
  Sigma.desc (fun d => (symmetricPower C d).structuralMap)

theorem symmetricPower_disjoint_union_locally_of_finite_type {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C] :
    LocallyOfFiniteType (symmetricPowerDisjointUnionMap C) := by
  sorry

theorem symmetricPower_disjoint_union_not_finite_type {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C]
    (hC : Nonempty C.carrier) :
    ¬ Chapter11FiniteType (symmetricPowerDisjointUnionMap C) := by
  sorry

/- For a nonsmooth curve the symmetric power still exists as a categorical
   quotient, but this chapter deliberately does not introduce a relative
   cycle functor.  In particular, no identification with finite-flat
   subschemes is asserted here: the Hilbert functor retains embedded
   structure, while the cycle comparison requires a separate construction. -/

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
