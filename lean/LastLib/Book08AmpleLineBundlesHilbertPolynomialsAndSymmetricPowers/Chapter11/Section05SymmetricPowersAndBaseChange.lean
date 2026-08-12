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
      Nonempty (RelativeScheme.Iso
          (RelativeScheme.baseChange (symmetricPower C d) T)
          (symmetricPower (RelativeScheme.baseChange C T) d)) := by
  intro T
  exact ⟨(symmetricPower_curve_base_change_iso C d T).choose⟩

noncomputable def symmetricPowerAddition {S : Scheme.{u}} (C : RelativeScheme S)
    (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier ⟶
      symmetricPower C (d + e) := by
  let P := relativeProduct (symmetricPower C d) (symmetricPower C e)
  let Dd := pullbackUniversalDivisor C P.carrier d P.fst
  let De := pullbackUniversalDivisor C P.carrier e P.snd
  let D : RelativeEffectiveCartierDivisor C P.carrier (d + e) :=
    { divisor := Dd.divisor.add De.divisor
      finite_flat_rank := by sorry }
  exact divisorToSymmetricPoint C P.carrier (d + e) D

theorem symmetricPowerAddition_from_divisor_sum {S : Scheme.{u}}
    (C : RelativeScheme S) (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] :
    ∃ D : RelativeEffectiveCartierDivisor C
        (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier (d + e),
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
  sorry

def Chapter11AdditionCommutativityStatement {S : Scheme.{u}} (C : RelativeScheme S)
    (d e : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  ∃ eSwap : RelativeScheme.Iso
      (relativeProduct (symmetricPower C d) (symmetricPower C e)).carrier
      (relativeProduct (symmetricPower C e) (symmetricPower C d)).carrier,
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
    HEq e.hom (symmetricPowerAddition C 0 d)

def Chapter11AdditionRightUnitStatement {S : Scheme.{u}} (C : RelativeScheme S)
    (d : ℕ) [Chapter11SmoothQuasiProjectiveCurve C] : Prop :=
  ∃ e : RelativeScheme.Iso
      (relativeProduct (symmetricPower C d) (symmetricPower C 0)).carrier
      (symmetricPower C d),
    HEq e.hom (symmetricPowerAddition C d 0)

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
    HEq (eAssoc.hom ≫ rightAssociatedAddition C d e f)
      (leftAssociatedAddition C d e f)

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
  leftUnit : ∀ (_d : ℕ), Prop
  rightUnit : ∀ (_d : ℕ), Prop
  commutative : ∀ (_d _e : ℕ), Prop
  associative : ∀ (_d _e _f : ℕ), Prop

noncomputable def symmetricPowerGradedCommutativeMonoid {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11GradedCommutativeMonoidScheme (S := S) where
  component := fun d => symmetricPower C d
  zero := symmetricPower_zero_iso C
  add := fun d e => symmetricPowerAddition C d e
  leftUnit := fun d => Chapter11AdditionLeftUnitStatement C d
  rightUnit := fun d => Chapter11AdditionRightUnitStatement C d
  commutative := fun d e => Chapter11AdditionCommutativityStatement C d e
  associative := fun d e f => Chapter11AdditionAssociativityStatement C d e f

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

theorem symmetricPower_disjoint_union_not_finite_type {S : Scheme.{u}}
    (C : RelativeScheme S) [Chapter11SmoothQuasiProjectiveCurve C]
    (hC : Nonempty C.carrier) :
    ¬ Chapter11FiniteType (symmetricPowerDisjointUnionMap C) := by
  sorry

/- SOURCE_ISSUE: the source says that for a nonsmooth curve the symmetric
   power "represents cycles" and contrasts it with finite-flat subschemes,
   but it does not define the relative cycle functor or state hypotheses under
   which that functor is represented.  The local cycle record below is an
   explicit provisional interface rather than a claim that it is canonical.
-/
/-!
For a nonsmooth curve the symmetric power remains the cycle space, while the
Hilbert functor remembers embedded finite-flat structures.
-/

structure RelativeFiniteFlatSubscheme {S : Scheme.{u}}
    (X T : RelativeScheme S) (d : ℕ) where
  carrier : Scheme.{u}
  mapToBase : carrier ⟶ T.carrier
  mapToX : carrier ⟶ pullback X.structuralMap T.structuralMap
  over_base : mapToX ≫ pullback.snd X.structuralMap T.structuralMap = mapToBase
  closed : IsClosedImmersion mapToX
  finite_flat : Chapter11FiniteLocallyFreeOfRank mapToBase d

structure Chapter11EffectiveDegreeDZeroCycle (X : Type u) (d : ℕ) where
  cycle : X →₀ ℕ
  degree : cycle.sum (fun _ n => n) = d

def Chapter11CycleOfFiniteFlatSubscheme {S : Scheme.{u}}
    {X T : RelativeScheme S} {d : ℕ}
    (Z : RelativeFiniteFlatSubscheme X T d) :
    Chapter11EffectiveDegreeDZeroCycle
      (pullback (C := Scheme) X.structuralMap T.structuralMap) d := by
  sorry

def Chapter11SymmetricPowerRepresentsCycles {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver C] : Prop :=
    ∀ T : RelativeScheme S,
    Nonempty ((T ⟶ symmetricPower C d) ≃
      Chapter11EffectiveDegreeDZeroCycle
        (pullback (C := Scheme) C.structuralMap T.structuralMap) d)

theorem nonsmooth_symmetric_power_represents_cycles {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver C]
    (hC : ¬ SmoothOfRelativeDimension 1 C.structuralMap) :
    Chapter11SymmetricPowerRepresentsCycles C d := by
  sorry

def Chapter11CycleForgetfulMap {S : Scheme.{u}} {C T : RelativeScheme S} (d : ℕ)
    (Z : RelativeFiniteFlatSubscheme C T d) :
    Chapter11EffectiveDegreeDZeroCycle
      (pullback (C := Scheme) C.structuralMap T.structuralMap) d :=
  Chapter11CycleOfFiniteFlatSubscheme Z

def Chapter11SameCycleDifferentStructures {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) : Prop :=
  ∃ (Z₁ Z₂ : RelativeFiniteFlatSubscheme C T d),
    Z₁ ≠ Z₂ ∧ Chapter11CycleForgetfulMap d Z₁ = Chapter11CycleForgetfulMap d Z₂

theorem hilbert_retains_embedded_structure {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ)
    (h : Chapter11SameCycleDifferentStructures C T d) :
    ∃ Z₁ Z₂ : RelativeFiniteFlatSubscheme C T d,
      Z₁ ≠ Z₂ ∧ Chapter11CycleForgetfulMap d Z₁ = Chapter11CycleForgetfulMap d Z₂ :=
  h

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
