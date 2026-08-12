import LastLib.Book04AdelesAndIdeles.Chapter09.Section01TheGlobalModuleAndDegree
import LastLib.Book04AdelesAndIdeles.Chapter09.Section03CompactnessOfNormOneClassGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain

/-!
## 9.4. Structure of the full idele class group
-/

def chapter09ClassNormOneInclusion
    (K : Type*) [Field K] [NumberField K] :
    chapter09ClassNormOne K →* Chapter09IdeleClassGroup K :=
  (chapter09ClassNormOne K).subtype

theorem chapter09ClassModule_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter09IdeleClassModule K) := by
  sorry

theorem chapter09ClassModule_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter09IdeleClassModule K) := by
  exact chapter09_module_descends_to_idele_class_group K

def chapter09ClassModule_short_exact
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ShortExactGroup
      (chapter09ClassNormOne K) (Chapter09IdeleClassGroup K) Chapter09PositiveReal := by
  refine
    { left := chapter09ClassNormOneInclusion K
      right := chapter09IdeleClassModule K
      left_injective := ?_
      exact := ?_
      right_surjective := ?_ }
  · sorry
  · sorry
  · exact chapter09ClassModule_surjective K

/- The splitting is stated as a choice-dependent section.  At a real place its
coordinate is `t`; at a complex place it is `sqrt t`, because the normalized
complex absolute value is the square of the usual modulus. -/
theorem chapter09_exists_class_module_section
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    ∃ s : Chapter09PositiveReal →* Chapter09IdeleClassGroup K,
      Continuous s ∧
        (chapter09IdeleClassModule K).comp s = MonoidHom.id _ := by
  sorry

noncomputable def chapter09ClassModuleSection
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    Chapter09PositiveReal →* Chapter09IdeleClassGroup K :=
  Classical.choose (chapter09_exists_class_module_section K v)

theorem chapter09ClassModuleSection_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    Continuous (chapter09ClassModuleSection K v) := by
  exact (Classical.choose_spec (chapter09_exists_class_module_section K v)).1

theorem chapter09ClassModuleSection_right_inverse
    (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    (chapter09IdeleClassModule K).comp (chapter09ClassModuleSection K v) =
      MonoidHom.id _ := by
  exact (Classical.choose_spec (chapter09_exists_class_module_section K v)).2

theorem chapter09_idele_class_group_split
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter09IdeleClassGroup K ≃*
      chapter09ClassNormOne K × Chapter09PositiveReal) := by
  sorry

theorem chapter09_positive_real_compact_subgroup_trivial
    (H : Subgroup Chapter09PositiveReal)
    (hH : IsCompact (H : Set Chapter09PositiveReal)) :
    H = ⊥ := by
  sorry

theorem chapter09_compact_subgroup_le_classNormOne
    (K : Type*) [Field K] [NumberField K]
    (H : Subgroup (Chapter09IdeleClassGroup K))
    (hH : IsCompact (H : Set (Chapter09IdeleClassGroup K))) :
    H ≤ chapter09ClassNormOne K := by
  sorry

theorem chapter09_classNormOne_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (chapter09ClassNormOne K : Set (Chapter09IdeleClassGroup K)) := by
  sorry

theorem chapter09_classNormOne_is_unique_maximal_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (chapter09ClassNormOne K : Set (Chapter09IdeleClassGroup K)) ∧
      ∀ H : Subgroup (Chapter09IdeleClassGroup K),
        IsCompact (H : Set (Chapter09IdeleClassGroup K)) →
          H ≤ chapter09ClassNormOne K := by
  exact ⟨chapter09_classNormOne_is_compact K,
    fun H hH => chapter09_compact_subgroup_le_classNormOne K H hH⟩

theorem chapter09_idele_class_group_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter09IdeleClassGroup K)) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter09
