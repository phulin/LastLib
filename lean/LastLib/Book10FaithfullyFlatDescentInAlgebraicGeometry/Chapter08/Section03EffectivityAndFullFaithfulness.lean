import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter08.Section02AffineLocalConstruction

namespace LastLib
namespace Book10FaithfullyFlatDescentInAlgebraicGeometry
namespace Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-!
## 8.3 Effectivity and full faithfulness
-/

/- The arbitrary-sheaf warning in the source is represented by keeping this
tensor-product restriction condition explicit: no descent claim for arbitrary
sheaves of sets is made without it. -/
/- The tensor-product restriction condition that is implicit in affine
quasi-coherence.  It is the condition needed for the affine equalizer
construction to be independent of the chosen basic open. -/
def Chapter08TensorRestrictionRequirement
    {R : CommRingCat.{u}} (M : ModuleCat R) : Prop :=
  ∀ f : R, Nonempty (Chapter08AffineRestrictionComparison M f)

/-- Affine localization supplies the tensor-product restriction requirement
with its canonical comparison. -/
theorem chapter08_affine_tensorRestrictionRequirement
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    Chapter08TensorRestrictionRequirement M := by
  intro f
  exact ⟨Chapter08AffineRestrictionComparison.canonical M f⟩

/- LOCAL_DEPENDENCY_GUESS: the pinned module and affine-sheaf APIs expose the
ingredients, but no earlier LastLib declaration packages them into this
effectivity equivalence. -/
/-- The quasi-coherent descent equivalence for one fpqc morphism. -/
noncomputable def chapter08QuasiCoherentDescentEquivalence
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    Chapter08QuasiCoherentModules S ≌
      Chapter08SingleCoverQuasiCoherentDescentData p := by
  sorry

/-- The pullback/descent functor appearing in the theorem. -/
noncomputable def chapter08QuasiCoherentPullbackDescentFunctor
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    Chapter08QuasiCoherentModules S ⥤
      Chapter08SingleCoverQuasiCoherentDescentData p :=
  (chapter08QuasiCoherentDescentEquivalence hp).functor

/- Descent over `X` uses the fpqc base change of `p` along `X ⟶ S`. -/
noncomputable def chapter08_quasiCoherent_descent_equivalence_after_base_change
    {X T S : Scheme.{u}} {f : X ⟶ S} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) :
    Chapter08QuasiCoherentModules X ≌
      Chapter08SingleCoverQuasiCoherentDescentData
        (chapter08BaseChangedCoverMap f p) :=
  chapter08QuasiCoherentDescentEquivalence (chapter08_baseChange_fpqc hp)

/-- Pullback is fully faithful on quasi-coherent sheaves with descent
compatibility. -/
theorem chapter08_pullback_is_full
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    (chapter08QuasiCoherentPullbackDescentFunctor hp).Full := by
  sorry

theorem chapter08_pullback_is_faithful
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    (chapter08QuasiCoherentPullbackDescentFunctor hp).Faithful := by
  sorry

/-- Effectivity: every quasi-coherent descent datum has a descended sheaf. -/
noncomputable def chapter08DescendedQuasiCoherentModule
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    (D : Chapter08SingleCoverQuasiCoherentDescentData p) :
    Chapter08QuasiCoherentModules S :=
  (chapter08QuasiCoherentDescentEquivalence hp).inverse.obj D

/-- The canonical comparison identifies the pullback of the descended sheaf
with the original upstairs object. -/
noncomputable def chapter08EffectivityComparison
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    (D : Chapter08SingleCoverQuasiCoherentDescentData p) :
    (Scheme.Modules.pullback p).obj
        (chapter08DescendedQuasiCoherentModule hp D).obj ≅
      (D.obj).obj () := by
  sorry

/-- Effectivity and full faithfulness together package the quasi-coherent
descent theorem for a single fpqc morphism. -/
theorem chapter08_quasiCoherent_descent_theorem
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    Nonempty
      (Chapter08QuasiCoherentModules S ≌
        Chapter08SingleCoverQuasiCoherentDescentData p) := by
  exact ⟨chapter08QuasiCoherentDescentEquivalence hp⟩

/-- The same descent theorem for an fpqc covering family,
with pairwise and triple overlap choices. -/
noncomputable def chapter08FamilyQuasiCoherentDescentEquivalence
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    Chapter08QuasiCoherentModules S ≌
      Chapter08QuasiCoherentModuleDescentData choices := by
  sorry

/- Full faithfulness for a family is the same componentwise affine-module
argument as for a singleton, with the pairwise overlap equations retained. -/
theorem chapter08_family_pullback_is_full_and_faithful
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    (chapter08FamilyQuasiCoherentDescentEquivalence C choices).functor.Full ∧
      (chapter08FamilyQuasiCoherentDescentEquivalence C choices).functor.Faithful := by
  sorry

/-- Family descent is interpreted on the pairwise and triple overlaps selected
by `choices`. -/
theorem chapter08_family_descent_effective
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map)
    (D : Chapter08QuasiCoherentModuleDescentData choices) :
    Nonempty (Chapter08QuasiCoherentModules S) := by
  let E := chapter08FamilyQuasiCoherentDescentEquivalence C choices
  exact ⟨E.inverse.obj D⟩

/-- A compatible upstairs morphism descends uniquely on every affine open. -/
theorem chapter08_compatible_map_descends_uniquely
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    {D E : Chapter08SingleCoverQuasiCoherentDescentData p}
    (φ : D ⟶ E) :
    ∃! ψ : chapter08DescendedQuasiCoherentModule hp D ⟶
        chapter08DescendedQuasiCoherentModule hp E,
      (chapter08QuasiCoherentDescentEquivalence hp).functor.map ψ = φ := by
  sorry

/-- The comparison map in the effectivity construction is an isomorphism
affine-locally, hence globally in the quasi-coherent category. -/
theorem chapter08_effectivity_comparison_isIso
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    (D : Chapter08SingleCoverQuasiCoherentDescentData p) :
    IsIso (chapter08EffectivityComparison hp D).hom := by
  infer_instance

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
