import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.1. Why the idele class group is the source
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

open CategoryTheory

/-! The source object is the quotient of ideles, not the ideal class group. -/

theorem chapter14_idele_class_group_is_the_idele_quotient {K : Type*} [Field K]
    [NumberField K] :
    chapter14IdeleClassGroup K =
      (chapter14IdeleGroup K ⧸ chapter14PrincipalIdeleSubgroup K) :=
  rfl

theorem chapter14_principal_ideles_are_the_diagonal_units {K : Type*} [Field K]
    [NumberField K] (x : Kˣ) :
    chapter14PrincipalIdeleEmbedding K x =
      Units.map (algebraMap K (chapter14AdeleRing K)).toMonoidHom x :=
  rfl

/-!
An individual finite quotient is a continuous finite quotient of the topological idele class
group.  The kernel package is useful when translating between finite quotients and open finite
index subgroups.
-/

def chapter14FiniteQuotientPresentation (C H : Type*) [Group C] [TopologicalSpace C]
    [Group H] [Finite H] [TopologicalSpace H] (f : C →* H) : Prop :=
  Function.Surjective f ∧ Continuous f ∧
    IsOpen (f.ker : Set C) ∧ f.ker.FiniteIndex

theorem chapter14_finite_quotient_kernel_is_open {C H : Type*} [Group C]
    [TopologicalSpace C] [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : C →* H) (hf : Continuous f) :
    IsOpen (f.ker : Set C) := by
  sorry

theorem chapter14_finite_quotient_kernel_has_finite_index {C H : Type*} [Group C]
    [TopologicalSpace C] [Group H] [Finite H] (f : C →* H)
    (hf : Function.Surjective f) : f.ker.FiniteIndex := by
  sorry

def chapter14FiniteLevelCompatibility {C H₁ H₂ : Type*} [Group C] [Group H₁] [Group H₂]
    (f₁ : C →* H₁) (f₂ : C →* H₂) (q : H₁ →* H₂) : Prop :=
  f₂ = q.comp f₁

theorem chapter14_global_reciprocity_completion_is_the_compatible_finite_level_limit
    (K : Type*) [Field K] [NumberField K] :
    chapter14IdeleClassProfiniteCompletion K =
      chapter14ProfiniteCompletion (chapter14IdeleClassGroup K) :=
  rfl

/-!
The chapter records the global reciprocity statement as an interface.  Its construction and proof
are intentionally deferred to the reciprocity chapter.
-/

theorem chapter14_global_reciprocity_statement (K : Type*) [Field K] [NumberField K] :
    chapter14GlobalReciprocityStatement K := by
  sorry

end LastLib.Book04AdelesAndIdeles.Chapter14
