import LastLib.Book04AdelesAndIdeles.Chapter09.Section03CompactnessOfNormOneClassGroup

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain

/-!
## 9.5. The compact kernel over the ideal class group
-/

/- This is the representative-level map on norm-one ideles.  The exact
sequence below uses `chapter09NormOneClassIdealClassMap`, the map descended to
the norm-one idele class group. -/
def chapter09NormOneIdealClassMap
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter09IdeleIdealData K) :
    chapter09NormOneIdeles K →* ClassGroup (𝓞 K) :=
  D.idealClassMap.comp
    ((chapter09FiniteIdelePartHom K).comp (chapter09NormOneIdeles K).subtype)

theorem chapter09NormOneIdealClassMap_surjective
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter09IdeleIdealData K) :
    Function.Surjective (chapter09NormOneIdealClassMap K D) := by
  sorry

def chapter09ArchFiniteToClassNormOne
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchFiniteUnitKernel K →* chapter09ClassNormOne K :=
  (chapter09NormOneClassGroup_equiv_classNormOne (K := K)).toMonoidHom.comp
    (chapter09ArchFiniteToNormOneClassGroup K)

theorem chapter09ArchFiniteToClassNormOne_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter09ArchFiniteUnitKernel K) :
    chapter09ArchFiniteToClassNormOne K x =
      (chapter09NormOneClassGroup_equiv_classNormOne (K := K))
        (chapter09ArchFiniteToNormOneClassGroup K x) :=
  rfl

def chapter09CompactKernel_short_exact
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter09IdeleIdealData K) :
      Chapter09ShortExactGroup
      (Chapter09ArchFiniteUnitKernel K) (chapter09ClassNormOne K)
        (ClassGroup (𝓞 K)) := by
  refine
    { left := chapter09ArchFiniteToClassNormOne K
      right := chapter09NormOneClassIdealClassMap K D
      left_injective := ?_
      exact := ?_
      right_surjective := ?_ }
  · sorry
  · sorry
  · sorry

theorem chapter09_compact_kernel_over_class_group
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter09IdeleIdealData K) :
    Function.MulExact (chapter09ArchFiniteToClassNormOne K)
      (chapter09NormOneClassIdealClassMap K D) := by
  exact (chapter09CompactKernel_short_exact K D).exact

theorem chapter09NormOneClassIdealClassMap_surjective
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter09IdeleIdealData K) :
    Function.Surjective (chapter09NormOneClassIdealClassMap K D) := by
  exact (chapter09CompactKernel_short_exact K D).right_surjective

theorem chapter09ArchFiniteUnitKernel_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter09ArchFiniteUnitKernel K)) := by
  sorry

theorem chapter09KInfinityOne_is_archimedean_norm_one
    (K : Type*) [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) :
    x ∈ chapter09KInfinityOne K ↔
      chapter09InfiniteIdeleModule x = 1 := by
  rfl

theorem chapter09CompactKernel_finite_factor_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09FiniteUnitIdeles K)) := by
  exact chapter09_finite_unit_ideles_compact K

theorem chapter09CompactKernel_archimedean_factor_compact_mod_units
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter09ArchimedeanUnitQuotient K)) := by
  exact chapter09_archimedean_unit_quotient_compact K

/- The quotient is structural rather than a canonical direct product: the
global-unit range is the diagonal gluing between the archimedean and finite
unit factors. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter09
