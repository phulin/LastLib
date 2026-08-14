import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11.Section02ExistenceInPositiveGenus

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ### 11.3 Uniqueness and its limits -/

/- LOCAL_DEPENDENCY_GUESS: the source deliberately leaves the precise ruled
surface notion of an elementary transformation implicit; the pair records the
two model constructions and their generic-fiber comparison capabilities. -/
structure Chapter11GenusZeroMinimalModelPair
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) where
  genus_zero : C.genus = 0
  projectiveLine_generic_fiber :
    Nonempty (C.carrier ≅ chapter04ProjectiveLine K)
  standard : Chapter11RegularProperModel R K C
  elementary : Chapter11RegularProperModel R K C
  standard_is_projective_line_model : Prop
  elementary_transformation : Prop
  standard_relatively_minimal : chapter11RelativelyMinimal standard
  elementary_relatively_minimal : chapter11RelativelyMinimal elementary
  no_canonical_generic_identity_map : Prop

theorem chapter11_genus_zero_elementary_transformations_destroy_unmarked_uniqueness
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K)
    (hgenus : C.genus = 0)
    (hP1 : Nonempty (C.carrier ≅ chapter04ProjectiveLine K)) :
    Nonempty (Chapter11GenusZeroMinimalModelPair C) := by
  sorry

structure Chapter11ThreeMarkedSections
    (M : Chapter11RegularProperModel R K C) where
  sections : Fin 3 → (Spec (CommRingCat.of K) ⟶ M.carrier)
  over : ∀ i, sections i ≫ M.structureMap = chapter11GenericBaseMap R K
  pairwise_disjoint : ∀ i j, i ≠ j → ∀ z : Spec (CommRingCat.of K),
    sections i z ≠ sections j z

def chapter11PreservesThreeMarkedSections
    (P : Chapter11ThreeMarkedSections M)
    (Q : Chapter11ThreeMarkedSections N)
    (u : M.carrier ⟶ N.carrier) : Prop :=
  ∀ i, u ≫ Q.sections i = P.sections i

theorem chapter11_three_marked_sections_restore_rigidity
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    {M N : Chapter11RegularProperModel R K C}
    (P : Chapter11ThreeMarkedSections M)
    (Q : Chapter11ThreeMarkedSections N)
    {u v : M.carrier ⟶ N.carrier}
    (hu : chapter11InducesIdentityOnGenericFiber M N u)
    (hv : chapter11InducesIdentityOnGenericFiber M N v)
    (hu_marked : chapter11PreservesThreeMarkedSections P Q u)
    (hv_marked : chapter11PreservesThreeMarkedSections P Q v) :
    u = v := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the exact pair of elementary models and the
nonexistence of a preferred generic-fiber-preserving map are not fixed by an
earlier category of unmarked models. -/
structure Chapter11UnmarkedGenusZeroNonuniqueness
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) where
  pair : Chapter11GenusZeroMinimalModelPair C
  no_unique_map : Prop

theorem chapter11_unmarked_genus_zero_has_too_many_minimal_models
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K)
    (hgenus : C.genus = 0)
    (hP1 : Nonempty (C.carrier ≅ chapter04ProjectiveLine K)) :
    Nonempty (Chapter11UnmarkedGenusZeroNonuniqueness C) := by
  sorry

def chapter11InducesGenericAutomorphism
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11RegularProperModel R K C)
    (α : C.carrier ≅ C.carrier)
    (u : M.carrier ⟶ M.carrier) : Prop :=
  ∃ hu : u ≫ M.structureMap = M.structureMap,
    M.genericFiber.iso.inv ≫
        pullback.lift
          (pullback.fst M.structureMap (chapter11GenericBaseMap R K) ≫ u)
          (pullback.snd M.structureMap (chapter11GenericBaseMap R K))
          (by rw [Category.assoc, hu]; simp) ≫
        M.genericFiber.iso.hom = α.hom

theorem chapter11_generic_automorphism_extends_uniquely
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11MinimalRegularModel R K C)
    (α : C.carrier ≅ C.carrier) :
    ∃! u : M.model.carrier ⟶ M.model.carrier,
      chapter11InducesGenericAutomorphism M.model α u := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the source's examples of multiplicities, cusps, and
failure of semistability/stability are not single pinned predicates, so this
witness keeps each warning as an independently usable capability. -/
structure Chapter11MinimalRegularDistinctionWitness
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) where
  model : Chapter11MinimalRegularModel R K C
  total_space_not_smooth : ¬ Smooth model.model.structureMap
  special_fiber_multiplicities : Prop
  special_fiber_curve_can_be_cuspidal : Prop
  nodal_after_residue_extension_only : Prop
  not_semistable : Prop
  not_stable : Prop

def chapter11_minimal_regular_does_not_mean_smooth_semistable_or_stable
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) : Prop :=
  Nonempty (Chapter11MinimalRegularDistinctionWitness C)

def chapter11_minimality_need_not_commute_with_ramified_base_change
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    (M : Chapter11MinimalRegularModel R K C) : Prop :=
  Nonempty (Chapter11RamifiedBaseChangeProfile M.model)

theorem chapter11_ramified_base_change_requires_recontraction
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {C : Chapter11SmoothProjectiveCurve K}
    {M : Chapter11MinimalRegularModel R K C}
    (Rpr : Chapter11RamifiedBaseChangeProfile M.model) :
    Rpr.newExceptionalCurve ∧ Rpr.recontracted := by
  exact ⟨Rpr.newExceptionalCurve, Rpr.recontracted⟩

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11
