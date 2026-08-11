import LastLib.Book03RamificationTheory.Chapter12.Core

namespace LastLib.Book03RamificationTheory.Chapter12

noncomputable section

open scoped BigOperators

/-!
## 12.4. Towers and transitivity
-/

structure Chapter12TowerNumericalData where
  topOverBase : Chapter12LocalExtensionNumbers
  topOverMiddle : Chapter12LocalExtensionNumbers
  middleOverBase : Chapter12LocalExtensionNumbers
  ramification_mul :
    topOverBase.ramificationIndex =
      topOverMiddle.ramificationIndex * middleOverBase.ramificationIndex
  residueDegree_mul :
    topOverBase.residueDegree =
      topOverMiddle.residueDegree * middleOverBase.residueDegree
  different_transitivity :
    topOverBase.differentExponent =
      topOverMiddle.differentExponent +
        topOverMiddle.ramificationIndex * middleOverBase.differentExponent
  degree_mul :
    topOverBase.degree = topOverMiddle.degree * middleOverBase.degree

theorem chapter12_tower_different_transitivity
    (T : Chapter12TowerNumericalData) :
    T.topOverBase.differentExponent =
      T.topOverMiddle.differentExponent +
        T.topOverMiddle.ramificationIndex * T.middleOverBase.differentExponent :=
  T.different_transitivity

theorem chapter12_tower_discriminant_exponent_expansion
    (T : Chapter12TowerNumericalData) :
    T.topOverBase.discriminantExponent =
      T.middleOverBase.discriminantExponent * T.topOverMiddle.degree +
        T.middleOverBase.residueDegree * T.topOverMiddle.discriminantExponent := by
  sorry

/- Mathlib's induction construction is used on the two composable group
homomorphisms.  The transitivity equivalence is the representation-theoretic
interface needed before applying the conductor formula. -/
theorem chapter12_induction_representation_transitive
    {G H L V : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [Group L] [Fintype L] [AddCommGroup V] [Module ℚ V]
    (ιHG : H →* G) (ιLH : L →* H) (ιLG : L →* G)
    (hcomp : ιHG.comp ιLH = ιLG)
    (ρ : Representation ℚ L V) :
    Nonempty
      ((Representation.ind ιHG (Representation.ind ιLH ρ)).Equiv
        (Representation.ind ιLG ρ)) := by
  sorry

/- The two applications of the induction formula expand to the one-step
formula.  The middle-stage dimension is the degree times the original
dimension, and the final conductor is transferred by the product of residue
degrees. -/
theorem chapter12_induction_rhs_tower
    (T : Chapter12TowerNumericalData) (dimension conductor : ℕ) :
    chapter12InductionRHS T.middleOverBase
        (T.topOverMiddle.degree * dimension)
        (chapter12InductionRHS T.topOverMiddle dimension conductor) =
      chapter12InductionRHS T.topOverBase dimension conductor := by
  sorry

theorem chapter12_induction_rhs_tower_using_discriminant_exponent
    (T : Chapter12TowerNumericalData) (dimension conductor : ℕ) :
    chapter12InductionRHS T.middleOverBase
        (T.topOverMiddle.degree * dimension)
        (chapter12InductionRHS T.topOverMiddle dimension conductor) =
      T.topOverBase.discriminantExponent * dimension +
        T.topOverBase.residueDegree * conductor := by
  sorry

theorem chapter12_tower_transferred_conductor_coefficient
    (T : Chapter12TowerNumericalData) (conductor : ℕ) :
    T.middleOverBase.residueDegree *
        (T.topOverMiddle.residueDegree * conductor) =
      T.topOverBase.residueDegree * conductor := by
  rw [T.residueDegree_mul]
  ac_rfl

/- This is the normalization check emphasized at the end of the source: both
the coefficient of the dimension and the transferred conductor agree. -/
theorem chapter12_tower_normalization_check
    (T : Chapter12TowerNumericalData) (dimension conductor : ℕ) :
    chapter12InductionRHS T.middleOverBase
        (T.topOverMiddle.degree * dimension)
        (chapter12InductionRHS T.topOverMiddle dimension conductor) =
      T.topOverBase.discriminantExponent * dimension +
        T.topOverBase.residueDegree * conductor := by
  exact chapter12_induction_rhs_tower_using_discriminant_exponent T dimension conductor

end
end LastLib.Book03RamificationTheory.Chapter12
