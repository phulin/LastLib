import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05.Section01InvariantModule

/-!
# 5.2 Proof of effectivity

The direct effectivity statements are recorded with the same invariant and evaluation maps as in
§5.1.  The categorical comparison theorem is also exposed, since it is the pinned Mathlib route
to the equivalence of modules and descent data.
-/

open CategoryTheory
open TensorProduct
open scoped TensorProduct

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05

noncomputable section

section FaithfullyFlatComparison

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The source's functor `M ↦ (B ⊗[A] M, canonical datum)`. -/
noncomputable def faithfullyFlatDescentFunctor :
    ModuleCat A ⥤ DescentDatum A B :=
  descentComparison A B

theorem faithfullyFlatDescentFunctor_obj_underlying (M : ModuleCat A) :
    ((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A =
      (ModuleCat.extendScalars (algebraMap A B)).obj M :=
  rfl

/-- Faithfully flat module descent: the comparison functor is an equivalence. -/
theorem faithfullyFlat_module_descent
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) :
    (faithfullyFlatDescentFunctor (A := A) (B := B)).IsEquivalence := by
  sorry

theorem faithfullyFlat_module_descent_of_instance [Module.FaithfullyFlat A B] :
    (faithfullyFlatDescentFunctor (A := A) (B := B)).IsEquivalence := by
  apply faithfullyFlat_module_descent
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

end FaithfullyFlatComparison

section SplitCover

variable {C D : Type u} [CommRing C] [CommRing D] [Algebra C D]

/-- The invariant module used for a split cover `C → D` with algebra retraction `s`. -/
noncomputable def splitInvariant (s : D →ₐ[C] C) (Q : DescentDatum C D) : ModuleCat C :=
  letI : Module D C := s.toRingHom.toModule
  ModuleCat.of C (C ⊗[D] (Q.A : Type u))

/-- Evaluation for the split-cover invariant.  The displayed tensor product is
`Q₀ = C ⊗_{D,s} Q`. -/
noncomputable def splitEvaluation (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    (ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q) ⟶ Q.A := by
  sorry

theorem splitCover_effective (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    Function.Bijective (splitEvaluation s Q) := by
  sorry

noncomputable def splitCover_effectiveIso (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    (ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q) ≅ Q.A :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (splitEvaluation s Q).hom (splitCover_effective s Q))

/- The split-cover calculation identifies the evaluation map itself with a morphism of descent
data; retaining this equation is stronger and more useful than only asserting existence of some
isomorphism of underlying modules. -/
theorem splitEvaluation_compatible_with_descent_data (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    ((descentComparison C D).obj (splitInvariant s Q)).a ≫
        (descentComonad C D).map (splitEvaluation s Q) =
      splitEvaluation s Q ≫ Q.a := by
  sorry

theorem splitEvaluation_is_underlying_descent_iso (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    ∃ e : ((descentComparison C D).obj (splitInvariant s Q)) ≅ Q,
      e.hom.f = splitEvaluation s Q := by
  sorry

@[simp]
theorem splitCover_effectiveIso_hom_inv (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    (splitCover_effectiveIso s Q).hom ≫ (splitCover_effectiveIso s Q).inv = 𝟙 _ :=
  (splitCover_effectiveIso s Q).hom_inv_id

@[simp]
theorem splitCover_effectiveIso_inv_hom (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    (splitCover_effectiveIso s Q).inv ≫ (splitCover_effectiveIso s Q).hom = 𝟙 _ :=
  (splitCover_effectiveIso s Q).inv_hom_id

theorem splitCover_invariant_is_canonically_effective (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    Nonempty
      (((descentComparison C D).obj (splitInvariant s Q)) ≅ Q) := by
  exact ⟨(splitEvaluation_is_underlying_descent_iso s Q).choose⟩

end SplitCover

section EffectivityMap

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

theorem evaluationMap_bijective_of_faithfullyFlat
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (D : DescentDatum A B) :
    Function.Bijective (evaluationMap D) := by
  sorry

theorem evaluationMap_bijective_of_instance [Module.FaithfullyFlat A B]
    (D : DescentDatum A B) : Function.Bijective (evaluationMap D) := by
  apply evaluationMap_bijective_of_faithfullyFlat
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/- The invariant equalizer does not merely produce an abstract descended object: its canonical
evaluation map is the comparison morphism carrying the canonical datum to `D`. -/
theorem evaluationMap_compatible_with_descent_data (D : DescentDatum A B) :
    ((descentComparison A B).obj (invariantModuleCat D)).a ≫
        (descentComonad A B).map (evaluationMap D) =
      evaluationMap D ≫ D.a := by
  sorry

theorem evaluationMap_is_underlying_descent_iso
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (D : DescentDatum A B) :
    ∃ e : ((descentComparison A B).obj (invariantModuleCat D)) ≅ D,
      e.hom.f = evaluationMap D := by
  sorry

noncomputable def evaluationIso_of_faithfullyFlat
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (D : DescentDatum A B) :
    invariantExtension D ≅ D.A :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (evaluationMap D).hom (evaluationMap_bijective_of_faithfullyFlat hAB D))

theorem evaluationIso_respects_canonical_descent_data
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (D : DescentDatum A B) :
    Nonempty (((descentComparison A B).obj (invariantModuleCat D)) ≅ D) := by
  exact ⟨(evaluationMap_is_underlying_descent_iso hAB D).choose⟩

theorem faithfullyFlat_module_descent_essential_surjective
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (D : DescentDatum A B) :
    ∃ M : ModuleCat A, Nonempty (((descentComparison A B).obj M) ≅ D) := by
  exact ⟨invariantModuleCat D, evaluationIso_respects_canonical_descent_data hAB D⟩

end EffectivityMap

section AmitsurEqualizer

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The exact Amitsur equalizer in difference-map form. -/
theorem invariant_amitsur_exact (D : DescentDatum A B) :
    Function.Exact
      (invariantModule D).subtype
      (((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom -
        (canonicalCechMap (A := A) (B := B) D.A).hom) := by
  intro n
  constructor
  · intro hn
    refine ⟨⟨n, ?_⟩, rfl⟩
    exact (mem_invariantModule_iff D n).2 (sub_eq_zero.mp hn)
  · rintro ⟨m, rfl⟩
    rw [LinearMap.sub_apply]
    change
      ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom m.1 -
          (canonicalCechMap (A := A) (B := B) D.A).hom m.1 = 0
    rw [sub_eq_zero]
    exact (mem_invariantModule_iff D m.1).1 m.property

theorem invariant_amitsur_subtype_injective (D : DescentDatum A B) :
    Function.Injective (invariantModule D).subtype := by
  exact (invariantModule D).subtype_injective

theorem invariant_amitsur_equalizer (D : DescentDatum A B) :
    LinearMap.range (invariantModule D).subtype =
      LinearMap.ker
        (((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom -
          (canonicalCechMap (A := A) (B := B) D.A).hom) := by
  exact (invariant_amitsur_exact D).linearMap_ker_eq.symm

theorem flat_base_change_preserves_invariant_equalizer
    [Module.Flat A B] (D : DescentDatum A B) :
    LinearMap.range
        ((invariantModule D).subtype.lTensor B) =
      LinearMap.eqLocus
        (((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom.lTensor B)
        ((canonicalCechMap (A := A) (B := B) D.A).hom.lTensor B) := by
  rw [LinearMap.eqLocus_eq_ker_sub, ← LinearMap.lTensor_sub]
  exact (Module.Flat.lTensor_exact B (invariant_amitsur_exact D)).linearMap_ker_eq.symm

theorem faithful_flatness_reflects_invariant_equalizer
    [Module.FaithfullyFlat A B] (D : DescentDatum A B) :
    Function.Bijective (evaluationMap D) := by
  exact evaluationMap_bijective_of_instance D

end AmitsurEqualizer

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05
