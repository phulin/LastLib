import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section02RationalSectionsRecoverDivisors
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u

/-! ## 4.3. Principal divisors and linear equivalence -/

structure Chapter04PrincipalCartierDivisorData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [Chapter04RationalFunctionLocalValueAPI X]
    (f : X.functionFieldˣ) where
  divisor : Chapter04CartierDivisor X
  cover_nonempty :
    ∀ i : divisor.cover.I₀,
      Set.Nonempty ((divisor.cover.f i).opensRange : Set X)
  local_equation :
    ∀ i : divisor.cover.I₀,
      divisor.equation i =
        Chapter04RationalFunctionLocalValueAPI.value
          ⟨(divisor.cover.f i).opensRange, cover_nonempty i⟩
          (f : X.functionField)

theorem chapter04_principalCartierDivisor_exists {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (f : X.functionFieldˣ) :
    Nonempty (Chapter04PrincipalCartierDivisorData f) := by
  sorry

noncomputable def chapter04PrincipalCartierDivisorData {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (f : X.functionFieldˣ) : Chapter04PrincipalCartierDivisorData f :=
  Classical.choice (chapter04_principalCartierDivisor_exists f)

noncomputable def chapter04PrincipalCartierDivisor {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (f : X.functionFieldˣ) : Chapter04CartierDivisor X :=
  (chapter04PrincipalCartierDivisorData f).divisor

theorem chapter04_principalCartierDivisor_local_equation {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (f : X.functionFieldˣ) :
    ∀ i : (chapter04PrincipalCartierDivisor f).cover.I₀,
      (chapter04PrincipalCartierDivisor f).equation i =
        Chapter04RationalFunctionLocalValueAPI.value
          ⟨((chapter04PrincipalCartierDivisor f).cover.f i).opensRange,
            (chapter04PrincipalCartierDivisorData f).cover_nonempty i⟩
          (f : X.functionField) := by
  intro i
  exact (chapter04PrincipalCartierDivisorData f).local_equation i

/-!
On a regular integral noetherian scheme the order API is canonical: the order
of a local Cartier equation is the order of its image in the function field.
The explicit bridge keeps later Weil-divisor statements usable without making
the caller rebuild this standard DVR construction.
-/
theorem chapter04_canonical_cartierOrderAPI_exists_of_regular_integral_noetherian
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular X] :
    Nonempty (Chapter04CartierOrderAPI X) := by
  sorry

@[instance_reducible]
noncomputable def chapter04CanonicalCartierOrderAPI {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X]
    [Chapter04RationalFunctionLocalValueAPI X]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular X] :
    Chapter04CartierOrderAPI X :=
  Classical.choice
    (chapter04_canonical_cartierOrderAPI_exists_of_regular_integral_noetherian (X := X))

attribute [instance] chapter04CanonicalCartierOrderAPI

def chapter04CartierDivisorsLinearlyEquivalent {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (D E : Chapter04CartierDivisor X) : Prop :=
  ∃ f : X.functionFieldˣ,
    chapter04CartierLocalEquationRelation
      (chapter04PrincipalCartierDivisor f) E D

theorem chapter04_cartier_linearEquivalence_refl {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (D : Chapter04CartierDivisor X) :
    chapter04CartierDivisorsLinearlyEquivalent D D := by
  sorry

theorem chapter04_cartier_linearEquivalence_symm {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    {D E : Chapter04CartierDivisor X}
    (h : chapter04CartierDivisorsLinearlyEquivalent D E) :
    chapter04CartierDivisorsLinearlyEquivalent E D := by
  sorry

theorem chapter04_cartier_linearEquivalence_trans {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    {D E F : Chapter04CartierDivisor X}
    (hDE : chapter04CartierDivisorsLinearlyEquivalent D E)
    (hEF : chapter04CartierDivisorsLinearlyEquivalent E F) :
    chapter04CartierDivisorsLinearlyEquivalent D F := by
  sorry

def chapter04WeilDivisorOfCartierDivisor {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04WeilDivisor X :=
  Finsupp.ofSupportFinite
    (fun x => chapter04CartierOrder D x)
    (by
      simpa [Function.support, chapter04CartierOrder] using
        (Chapter04CartierOrderAPI.order_support_finite D))

/-!
The Weil divisor of a global rational unit is obtained from the coherent
codimension-one order supplied by `Chapter04CartierOrderAPI`.  The separate
compatibility hypothesis below identifies this order with the local-equation
presentation when Cartier and Weil divisors are compared.
-/
noncomputable def chapter04PrincipalDivisor {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (f : X.functionFieldˣ) : Chapter04WeilDivisor X :=
  Finsupp.ofSupportFinite
    (Chapter04CartierOrderAPI.principalOrder f)
    (by
      simpa [Function.support] using
        (Chapter04CartierOrderAPI.principalOrder_support_finite f))

theorem chapter04_principalDivisor_one {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] :
    chapter04PrincipalDivisor (1 : X.functionFieldˣ) = 0 := by
  sorry

theorem chapter04_principalDivisor_mul {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] (f g : X.functionFieldˣ) :
    chapter04PrincipalDivisor (f * g) =
      chapter04PrincipalDivisor f + chapter04PrincipalDivisor g := by
  sorry

theorem chapter04_principalDivisor_inv {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] (f : X.functionFieldˣ) :
    chapter04PrincipalDivisor f⁻¹ = -chapter04PrincipalDivisor f := by
  sorry

def chapter04WeilDivisorsLinearlyEquivalent {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D E : Chapter04WeilDivisor X) : Prop :=
  ∃ f : X.functionFieldˣ, D - E = chapter04PrincipalDivisor f

theorem chapter04_weil_linearEquivalence_refl {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04WeilDivisor X) :
    chapter04WeilDivisorsLinearlyEquivalent D D := by
  sorry

theorem chapter04_weil_linearEquivalence_symm {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    {D E : Chapter04WeilDivisor X}
    (h : chapter04WeilDivisorsLinearlyEquivalent D E) :
    chapter04WeilDivisorsLinearlyEquivalent E D := by
  sorry

theorem chapter04_weil_linearEquivalence_trans {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    {D E F : Chapter04WeilDivisor X}
    (hDE : chapter04WeilDivisorsLinearlyEquivalent D E)
    (hEF : chapter04WeilDivisorsLinearlyEquivalent E F) :
    chapter04WeilDivisorsLinearlyEquivalent D F := by
  sorry

theorem chapter04_cartier_linearEquivalence_to_weil_linearEquivalence
    {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    {D E : Chapter04CartierDivisor X}
    (hprincipal : ∀ f : X.functionFieldˣ,
      ∀ x : Chapter04CodimensionOnePoint X,
        chapter04CartierOrder (chapter04PrincipalCartierDivisor f) x =
          Chapter04CartierOrderAPI.principalOrder f x)
    (h : chapter04CartierDivisorsLinearlyEquivalent D E) :
    chapter04WeilDivisorsLinearlyEquivalent
      (chapter04WeilDivisorOfCartierDivisor D)
      (chapter04WeilDivisorOfCartierDivisor E) := by
  sorry

instance chapter04WeilDivisorLinearEquivalenceSetoid {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] :
    Setoid (Chapter04WeilDivisor X) where
  r := chapter04WeilDivisorsLinearlyEquivalent
  iseqv :=
    { refl := chapter04_weil_linearEquivalence_refl
      symm := chapter04_weil_linearEquivalence_symm
      trans := chapter04_weil_linearEquivalence_trans }

abbrev Chapter04WeilDivisorClass {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] :=
  Quotient (chapter04WeilDivisorLinearEquivalenceSetoid (X := X))

noncomputable def chapter04WeilDivisorClassMk {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (D : Chapter04WeilDivisor X) : Chapter04WeilDivisorClass (X := X) :=
  @Quotient.mk' _ (chapter04WeilDivisorLinearEquivalenceSetoid (X := X)) D

noncomputable def chapter04WeilDivisorClassAdd {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a b : Chapter04WeilDivisorClass (X := X)) :
    Chapter04WeilDivisorClass (X := X) :=
  Quotient.liftOn₂ a b
    (fun D E => chapter04WeilDivisorClassMk (D + E))
    (by
      intro D₁ E₁ D₂ E₂ hD hE
      apply Quotient.sound
      sorry)

noncomputable def chapter04WeilDivisorClassZero {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] :
    Chapter04WeilDivisorClass (X := X) :=
  chapter04WeilDivisorClassMk 0

noncomputable def chapter04WeilDivisorClassNeg {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a : Chapter04WeilDivisorClass (X := X)) :
    Chapter04WeilDivisorClass (X := X) :=
  Quotient.liftOn a
    (fun D => chapter04WeilDivisorClassMk (-D))
    (by
      intro D E hDE
      apply Quotient.sound
      sorry)

noncomputable def chapter04WeilDivisorClassNSMul {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (n : ℕ) (a : Chapter04WeilDivisorClass (X := X)) :
    Chapter04WeilDivisorClass (X := X) :=
  Quotient.liftOn a
    (fun D => chapter04WeilDivisorClassMk (n • D))
    (by
      intro D E hDE
      apply Quotient.sound
      sorry)

noncomputable def chapter04WeilDivisorClassZSMul {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (z : ℤ) (a : Chapter04WeilDivisorClass (X := X)) :
    Chapter04WeilDivisorClass (X := X) :=
  Quotient.liftOn a
    (fun D => chapter04WeilDivisorClassMk (z • D))
    (by
      intro D E hDE
      apply Quotient.sound
      sorry)

theorem chapter04_weilDivisorClass_add_assoc {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a b c : Chapter04WeilDivisorClass (X := X)) :
    chapter04WeilDivisorClassAdd (chapter04WeilDivisorClassAdd a b) c =
      chapter04WeilDivisorClassAdd a (chapter04WeilDivisorClassAdd b c) := by
  sorry

theorem chapter04_weilDivisorClass_zero_add {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a : Chapter04WeilDivisorClass (X := X)) :
    chapter04WeilDivisorClassAdd (chapter04WeilDivisorClassZero (X := X)) a = a := by
  sorry

theorem chapter04_weilDivisorClass_add_zero {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a : Chapter04WeilDivisorClass (X := X)) :
    chapter04WeilDivisorClassAdd a (chapter04WeilDivisorClassZero (X := X)) = a := by
  sorry

theorem chapter04_weilDivisorClass_add_comm {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a b : Chapter04WeilDivisorClass (X := X)) :
    chapter04WeilDivisorClassAdd a b =
      chapter04WeilDivisorClassAdd b a := by
  sorry

theorem chapter04_weilDivisorClass_neg_add_cancel {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (a : Chapter04WeilDivisorClass (X := X)) :
    chapter04WeilDivisorClassAdd (chapter04WeilDivisorClassNeg a) a =
      chapter04WeilDivisorClassZero (X := X) := by
  sorry

noncomputable instance chapter04WeilDivisorClassAddCommGroup (X : Scheme.{u})
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X] :
    AddCommGroup (Chapter04WeilDivisorClass (X := X)) where
  add := chapter04WeilDivisorClassAdd
  zero := chapter04WeilDivisorClassZero (X := X)
  neg := chapter04WeilDivisorClassNeg
  add_assoc := chapter04_weilDivisorClass_add_assoc
  zero_add := chapter04_weilDivisorClass_zero_add
  add_zero := chapter04_weilDivisorClass_add_zero
  neg_add_cancel := chapter04_weilDivisorClass_neg_add_cancel
  add_comm := chapter04_weilDivisorClass_add_comm
  nsmul := chapter04WeilDivisorClassNSMul
  zsmul := chapter04WeilDivisorClassZSMul
  nsmul_zero := by sorry
  nsmul_succ := by sorry
  sub_eq_add_neg := by sorry
  zsmul_zero' := by sorry
  zsmul_succ' := by sorry
  zsmul_neg' := by sorry

theorem chapter04_cartier_linearEquivalence_iff_lineBundle_isomorphic {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    (D E : Chapter04CartierDivisor X) :
    chapter04CartierDivisorsLinearlyEquivalent D E ↔
      chapter04LineBundleIsomorphic (chapter04OofD D) (chapter04OofD E) := by
  sorry

theorem chapter04_multiplication_by_rational_unit {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    {D E : Chapter04CartierDivisor X}
    (h : chapter04CartierDivisorsLinearlyEquivalent D E) :
    ∃ f : X.functionFieldˣ,
      chapter04CartierLocalEquationRelation
          (chapter04PrincipalCartierDivisor f) E D ∧
        Nonempty ((chapter04OofD D).sheaf ≅ (chapter04OofD E).sheaf) := by
  sorry

theorem chapter04_lineBundle_isomorphic_gives_linearEquivalence {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    {D E : Chapter04CartierDivisor X}
    (h : chapter04LineBundleIsomorphic (chapter04OofD D) (chapter04OofD E)) :
    chapter04CartierDivisorsLinearlyEquivalent D E := by
  sorry

/-! ### Complete curves, constants, and principal degree -/

def chapter04CurveConstantsUnitMap {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k) :
    kˣ →* Γ(C.carrier, ⊤)ˣ :=
  Units.map (chapter04CurveConstantsMap C).toMonoidHom

theorem chapter04_proper_geometricallyConnected_global_regular_units_constant
    {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [GeometricallyConnected C.structureMap]
    [GeometricallyReduced C.structureMap] :
    ∀ u : Γ(C.carrier, ⊤)ˣ, ∃ a : kˣ,
      chapter04CurveConstantsUnitMap C a = u := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the residue-degree construction for closed points
and the complete-curve theorem that the degree of a principal divisor is zero
are not bundled in the pinned Mathlib tree.  This interface records the
canonical residue-degree input and leaves the theorem as its reusable bridge.
-/
noncomputable def chapter04ClosedPointDegree {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    (x : Chapter04CodimensionOnePoint C.carrier) : ℕ := by
  letI : Algebra k (C.carrier.residueField x.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.structureMap.appTop ≫
      C.carrier.Γevaluation x.1).hom.toAlgebra
  exact Module.finrank k (C.carrier.residueField x.1)

def chapter04IsResidueDegree {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    (degree : Chapter04CodimensionOnePoint C.carrier → ℕ) : Prop :=
  ∀ x : Chapter04CodimensionOnePoint C.carrier,
    degree x = chapter04ClosedPointDegree C x

structure Chapter04CompleteCurveDegreeData {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [Chapter04TotalQuotientRingAPI C.carrier]
    [Chapter04RationalFunctionLocalValueAPI C.carrier]
    [IsLocallyNoetherian C.carrier]
    [Chapter04CartierOrderAPI C.carrier] where
  pointDegree : Chapter04CodimensionOnePoint C.carrier → ℕ
  pointDegree_is_residueDegree : chapter04IsResidueDegree C pointDegree

def chapter04CompleteCurveDegree {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [Chapter04TotalQuotientRingAPI C.carrier]
    [Chapter04RationalFunctionLocalValueAPI C.carrier]
    [IsLocallyNoetherian C.carrier]
    [Chapter04CartierOrderAPI C.carrier]
    (data : Chapter04CompleteCurveDegreeData C) :
    Chapter04CodimensionOnePoint C.carrier → ℕ :=
  data.pointDegree

noncomputable def chapter04CanonicalCompleteCurveDegreeData
    {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [Chapter04TotalQuotientRingAPI C.carrier]
    [Chapter04RationalFunctionLocalValueAPI C.carrier]
    [IsLocallyNoetherian C.carrier]
    [Chapter04CartierOrderAPI C.carrier] :
    Chapter04CompleteCurveDegreeData C where
  pointDegree := chapter04ClosedPointDegree C
  pointDegree_is_residueDegree := by
    intro x
    rfl

theorem chapter04_principal_divisor_has_total_degree_zero
    {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [Chapter04TotalQuotientRingAPI C.carrier]
    [Chapter04RationalFunctionLocalValueAPI C.carrier]
    [IsLocallyNoetherian C.carrier]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular C.carrier]
    (data : Chapter04CompleteCurveDegreeData C)
    (f : C.carrier.functionFieldˣ) :
    chapter04WeilDivisorDegree (chapter04CompleteCurveDegree C data)
      (chapter04PrincipalDivisor f) = 0 := by
  sorry

theorem chapter04_principal_divisor_has_canonical_total_degree_zero
    {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [Chapter04TotalQuotientRingAPI C.carrier]
    [Chapter04RationalFunctionLocalValueAPI C.carrier]
    [IsLocallyNoetherian C.carrier]
    [LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Chapter03Regular C.carrier]
    (f : C.carrier.functionFieldˣ) :
    chapter04WeilDivisorDegree (chapter04ClosedPointDegree C)
      (chapter04PrincipalDivisor f) = 0 := by
  exact chapter04_principal_divisor_has_total_degree_zero C
    (chapter04CanonicalCompleteCurveDegreeData C) f

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
