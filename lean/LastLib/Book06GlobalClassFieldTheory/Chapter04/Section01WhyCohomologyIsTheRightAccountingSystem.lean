import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section04ArchitectureOfTheProof

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v

open scoped BigOperators

/-! ## 4.1. Why cohomology is the right accounting system -/

/-- The source's norm quotient in degree zero, with the target written as the invariant subgroup.

The invariant subgroup is the additive encoding of `C_K` inside `C_L`; the norm map is the sum of
the conjugates.  This is a genuine construction, independent of any class-formation theorem.
-/
def chapter04InvariantSubgroup {G : Type u} [Group G]
    (M : Chapter04GModule.{u, v} G) : AddSubgroup M.V :=
  letI := M.addCommGroupV
  letI := M.moduleV
  { carrier := {x | ∀ g : G, M.ρ g x = x}
    zero_mem' := by
      intro g
      simp
    add_mem' := by
      intro x y hx hy g
      simp [hx g, hy g]
    neg_mem' := by
      intro x hx g
      simpa using congrArg Neg.neg (hx g) }

/-- The norm map from a finite group module to its invariant subgroup. -/
def chapter04NormToInvariants {G : Type u} [Group G] [Fintype G]
    (M : Chapter04GModule.{u, v} G) : M.V →+ (chapter04InvariantSubgroup M) :=
  letI := M.addCommGroupV
  letI := M.moduleV
  { toFun := fun x =>
      ⟨∑ g : G, M.ρ g x, by
        intro h
        simpa [Representation.norm] using Representation.self_norm_apply M.ρ h x⟩
    map_zero' := by
      classical
      simp
    map_add' := by
      intro x y
      classical
      apply Subtype.ext
      simp [Finset.sum_add_distrib] }

theorem chapter04_tate_degree_zero_is_norm_quotient
    {G : Type} [Group G] [Fintype G]
    (M : Chapter04GModule.{0, 0} G) :
    Nonempty
      (chapter04TateH M 0 ≃+
        chapter04AddNormQuotient (chapter04NormToInvariants M)) := by
  sorry

noncomputable def chapter04TateDegreeZeroNormQuotientEquiv
    {G : Type} [Group G] [Fintype G]
    (M : Chapter04GModule.{0, 0} G) :
    chapter04TateH M 0 ≃+
      chapter04AddNormQuotient (chapter04NormToInvariants M) :=
  Classical.choice (chapter04_tate_degree_zero_is_norm_quotient M)

/-! The abstract Tate quotient above is also connected to the canonical
idele-class quotient exposed by the earlier global architecture.  Keeping
this bridge explicit prevents the generic invariant-subgroup model from
silently standing in for `C_K / N C_L`. -/
theorem chapter04_canonical_tate_degree_zero_class_norm_bridge
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : LastLib.Book06GlobalClassFieldTheory.Chapter01.FiniteGaloisFundamentalClassData
      K L) :
    Nonempty
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05TateCohomology
          (Gal(L / K))
          (LastLib.Book06GlobalClassFieldTheory.Chapter01.globalIdeleClassCoefficientRep
            D.ideleClassAction) 0 ≃+
        Additive
          (LastLib.Book06GlobalClassFieldTheory.Chapter01.finiteClassArtinQuotient
            D.normData)) := by
  rcases LastLib.Book06GlobalClassFieldTheory.Chapter01.global_idele_class_degree_zero_norm_bridge_exists D with ⟨B⟩
  exact ⟨B.equiv⟩

/-- The negative degree-two Tate group of the trivial module is the abelianization. -/
theorem chapter04_tate_degree_neg_two_is_abelianization
    (G : Type) [Group G] [Fintype G] :
    Nonempty
      (chapter04TateH (chapter04TrivialGModule G) (-2) ≃+
        Additive (Abelianization G)) := by
  sorry

noncomputable def chapter04TateDegreeNegTwoAbelianizationEquiv
    (G : Type) [Group G] [Fintype G] :
    chapter04TateH (chapter04TrivialGModule G) (-2) ≃+
      Additive (Abelianization G) :=
  Classical.choice (chapter04_tate_degree_neg_two_is_abelianization G)

theorem chapter04_fundamental_class_restriction_normalization
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G) :
    U.invariant H (chapter04RestrictTwoClass U.C H U.u) =
      chapter04QModZOfRat ((1 : ℚ) / Nat.card H) := by
  exact U.invariant_normalization H

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
