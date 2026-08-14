import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Section02RationalSectionsRecoverDivisors

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
  local_equation :
    ∀ i : divisor.cover.I₀,
      divisor.equation i =
        Chapter04RationalFunctionLocalValueAPI.value
          (divisor.cover.f i).opensRange (f : X.functionField)

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
          ((chapter04PrincipalCartierDivisor f).cover.f i).opensRange
          (f : X.functionField) := by
  intro i
  exact (chapter04PrincipalCartierDivisorData f).local_equation i

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
    [IsLocallyNoetherian X] [Chapter04CartierOrderAPI X]
    (D : Chapter04CartierDivisor X) : Chapter04WeilDivisor X :=
  Finsupp.ofSupportFinite
    (fun x => chapter04CartierOrder D x)
    (by
      simpa [Function.support] using
        (Chapter04CartierOrderAPI.order_support_finite D))

/-!
The Weil divisor of a global rational unit is obtained by taking the order of
its principal Cartier divisor at every codimension-one point.  The local
equation field above makes the construction independent of a presentation by
an open cover.
-/
noncomputable def chapter04PrincipalDivisor {X : Scheme.{u}}
    [Chapter04TotalQuotientRingAPI X] [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter04RationalFunctionLocalValueAPI X]
    [Chapter04CartierOrderAPI X]
    (f : X.functionFieldˣ) : Chapter04WeilDivisor X :=
  chapter04WeilDivisorOfCartierDivisor (chapter04PrincipalCartierDivisor f)

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
    (D : Chapter04WeilDivisor X) : Chapter04WeilDivisorClass :=
  Quotient.mk' D

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
    [GeometricallyConnected C.structureMap] :
    ∀ u : Γ(C.carrier, ⊤)ˣ, ∃ a : kˣ,
      chapter04CurveConstantsUnitMap C a = u := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the residue-degree construction for closed points
and the complete-curve theorem that the degree of a principal divisor is zero
are not bundled in the pinned Mathlib tree.  This interface records the
canonical residue-degree input and leaves the theorem as its reusable bridge.
-/
def chapter04IsResidueDegree {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    (degree : Chapter04CodimensionOnePoint C.carrier → ℕ) : Prop :=
  ∀ x : Chapter04CodimensionOnePoint C.carrier,
    ∃ A : Algebra k (C.carrier.residueField x.1),
      degree x =
        @Module.finrank k (C.carrier.residueField x.1) _ _
          (@Algebra.toModule k (C.carrier.residueField x.1) _ _ A)

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

theorem chapter04_principal_divisor_has_total_degree_zero
    {k : Type u} [Field k]
    (C : Chapter04ProperIntegralCurveOverField k)
    [Chapter04TotalQuotientRingAPI C.carrier]
    [Chapter04RationalFunctionLocalValueAPI C.carrier]
    [IsLocallyNoetherian C.carrier]
    [Chapter04CartierOrderAPI C.carrier]
    (data : Chapter04CompleteCurveDegreeData C)
    (f : C.carrier.functionFieldˣ) :
    chapter04WeilDivisorDegree (chapter04CompleteCurveDegree C data)
      (chapter04PrincipalDivisor f) = 0 := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
