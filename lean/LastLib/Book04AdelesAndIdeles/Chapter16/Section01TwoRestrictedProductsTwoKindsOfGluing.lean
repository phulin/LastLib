import LastLib.Book04AdelesAndIdeles.Chapter16.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter16

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators NumberField Topology

/-!
## 16.1 Two restricted products, two kinds of gluing

This section records the additive/multiplicative dictionary.  The two tail
conditions intentionally remain separate: integral tails and unit tails are
not interchangeable.
-/

theorem chapter16_additive_tail_iff (K : Type*) [Field K] [NumberField K]
    (x : Chapter16FiniteAdeleRing K) :
    chapter16AdditiveTail K x ↔
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        x v ∈ v.adicCompletionIntegers K := by
  rfl

theorem chapter16_idele_unit_tail_iff (K : Type*) [Field K] [NumberField K]
    (x : Chapter16Ideles K) :
    chapter16IdeleUnitTail K x ↔
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        Valued.v ((x : Chapter16AdeleRing K).2 v) = 1 := by
  rfl

theorem chapter16_idele_unit_tail_iff_eventually_isUnit
    (K : Type*) [Field K] [NumberField K] (x : Chapter16Ideles K) :
    chapter16IdeleUnitTail K x ↔
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        IsUnit ((x : Chapter16AdeleRing K).2 v) := by
  sorry

theorem chapter16_additive_quotient_is_the_compact_gluing_space
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter16AdditiveQuotient K)) := by
  sorry

theorem chapter16_unit_lattice_controls_norm_one_classes
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter16NormOneClassGroup K)) := by
  sorry

theorem chapter16_full_idele_class_group_is_not_compact
    (K : Type*) [Field K] [NumberField K] :
    ¬ IsCompact (Set.univ : Set (Chapter16IdeleClassGroup K)) := by
  sorry

open scoped Classical in
theorem chapter16_idelic_compactness_requires_class_and_unit_inputs
    (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) ∧
      DiscreteTopology (Chapter16LogarithmicUnitLattice K) ∧
      @IsZLattice ℝ _ (NumberField.Units.dirichletUnitTheorem.logSpace K)
        (Pi.normedAddCommGroup) (Pi.normedSpace)
        (NumberField.Units.unitLattice K) _ := by
  sorry

theorem chapter16_idele_topology_controls_inversion
    (K : Type*) [Field K] [NumberField K] :
    Continuous (fun x : Chapter16Ideles K => x⁻¹) := by
  sorry

theorem chapter16_additive_archimedean_lattice_is_integral_embedding
    (K : Type*) [Field K] [NumberField K] :
    (chapter16ArchimedeanIntegerLattice K : Set (NumberField.InfiniteAdeleRing K)) =
      Set.range (fun a : 𝓞 K => algebraMap K (NumberField.InfiniteAdeleRing K) (a : K)) := by
  rfl

theorem chapter16_logarithmic_lattice_is_the_unit_lattice
    (K : Type*) [Field K] [NumberField K] :
    Chapter16LogarithmicUnitLattice K =
      (NumberField.Units.unitLattice K).toAddSubgroup := by
  rfl

/-!
The table in the text has no canonical additive arithmetic quotient: the
additive compact quotient is the relevant global object, whereas the
multiplicative finite arithmetic quotients are class and ray class groups.
The following aliases expose the remaining rows without manufacturing a
spurious additive quotient.
-/

abbrev Chapter16AdditiveGlobalSubgroup (K : Type*) [Field K] [NumberField K] := K

abbrev Chapter16MultiplicativeGlobalSubgroup (K : Type*) [Field K] [NumberField K] := Kˣ

theorem chapter16_two_restricted_products_have_distinct_tail_conditions
    (K : Type*) [Field K] [NumberField K] :
      (∀ x : Chapter16FiniteAdeleRing K,
        chapter16AdditiveTail K x ↔
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
            x v ∈ v.adicCompletionIntegers K) ∧
      (∀ x : Chapter16Ideles K,
        chapter16IdeleUnitTail K x ↔
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
            Valued.v ((x : Chapter16AdeleRing K).2 v) = 1) := by
  constructor
  · intro x
    exact chapter16_additive_tail_iff K x
  · intro x
    exact chapter16_idele_unit_tail_iff K x

end

end LastLib.Book04AdelesAndIdeles.Chapter16
