import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter08.Dependencies

namespace LastLib
namespace Book10FaithfullyFlatDescentInAlgebraicGeometry
namespace Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped AlgebraicGeometry

noncomputable section

universe u v

/-!
## 8.3 Effectivity and full faithfulness
-/

/-- The affine scalar-extension normalization used by quasi-coherent modules.
This records an equality of the chosen restriction model with extension of
scalars; it is not an existential comparison with an unrelated module. -/
def Chapter08TensorRestrictionRequirement
    {R : CommRingCat.{u}} (M : ModuleCat R) : Prop :=
  ∀ f : R,
    Nonempty (Chapter08AffineRestrictionSheafComparison M f)

/-- Affine localization supplies the tensor-product restriction requirement
with its canonical comparison. -/
theorem chapter08_affine_tensorRestrictionRequirement
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    Chapter08TensorRestrictionRequirement M := by
  intro f
  exact chapter08_affine_restriction_sheaf_comparison M f

/-- The canonical pullback functor into the chosen quasi-coherent descent
category.  Its object part is the actual family of pullback sheaves with the
canonical overlap datum, rather than the functor part of an unrelated chosen
equivalence. -/
noncomputable def chapter08CanonicalQuasiCoherentDescentFunctor
    {T S : Scheme.{u}} {p : T ⟶ S} :
    Chapter08QuasiCoherentModules S ⥤
      Chapter08SingleCoverQuasiCoherentDescentData p where
  obj := fun M =>
    chapter08CanonicalQuasiCoherentDescentData
      (chapter08SingleCoverChoices p) M
  map := fun {_M _N} φ =>
    chapter08CanonicalQuasiCoherentDescentMap
      (chapter08SingleCoverChoices p) φ
  map_id := fun M =>
    chapter08CanonicalQuasiCoherentDescentMap_id
      (chapter08SingleCoverChoices p) M
  map_comp := fun f g =>
    chapter08CanonicalQuasiCoherentDescentMap_comp
      (chapter08SingleCoverChoices p) f g

/- A generic categorical view of effective descent.  The equivalence field
   records effectivity, while the explicit full and faithful fields keep the
   two parts available to consumers that only need uniqueness of maps. -/
structure Chapter08EffectiveFullFaithfulDescent
    {C : Type u} {D : Type v} [Category C] [Category D] (F : C ⥤ D) : Prop where
  effective : Functor.IsEquivalence F
  full : F.Full
  faithful : F.Faithful

/-- A reusable effective-descent package for a specified descent functor.

The equivalence alone records effectivity, while the comparison identifies the
chosen equivalence with the particular functor produced by the construction.
This is the interface needed when another chapter presents the same descent
data with a different but canonically comparable model. -/
structure Chapter08EffectiveFullFaithfulDescentPackage
    {C : Type u} {D : Type v} [Category C] [Category D] (F : C ⥤ D) where
  equivalence : C ≌ D
  canonical : Nonempty (F ≅ equivalence.functor)

/-- The generic comparison package supplies effectivity, fullness, and
faithfulness for the specified descent functor. -/
theorem chapter08_effective_full_faithful_of_package
    {C : Type u} {D : Type v} [Category C] [Category D]
    {F : C ⥤ D}
    (P : Chapter08EffectiveFullFaithfulDescentPackage F) :
    Chapter08EffectiveFullFaithfulDescent F := by
  sorry

/- The equivalence used below is bundled with its comparison to the canonical
   pullback functor.  The quasi-coherent package is an instance of the generic
   package above, rather than a second incompatible interface. -/
abbrev Chapter08QuasiCoherentDescentEquivalencePackage
    {T S : Scheme.{u}} {p : T ⟶ S} (_hp : Chapter08FpqcMorphism p) :=
  Chapter08EffectiveFullFaithfulDescentPackage
    (chapter08CanonicalQuasiCoherentDescentFunctor (p := p))

noncomputable def chapter08QuasiCoherentDescentEquivalencePackage
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    Chapter08QuasiCoherentDescentEquivalencePackage hp := by
  sorry

/-- The quasi-coherent descent equivalence for one fpqc morphism. -/
noncomputable def chapter08QuasiCoherentDescentEquivalence
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
      Chapter08QuasiCoherentModules S ≌
      Chapter08SingleCoverQuasiCoherentDescentData p := by
  exact (chapter08QuasiCoherentDescentEquivalencePackage hp).equivalence

/-- The chosen equivalence is compatible, up to isomorphism in the descent
category, with the canonical datum obtained by pulling a quasi-coherent module
back to the cover.  An arbitrary equivalence between the two categories would
not by itself provide effectivity for the canonical pullback functor. -/
theorem chapter08_quasiCoherent_descent_equivalence_canonical
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    (M : Chapter08QuasiCoherentModules S) :
    Nonempty
      ((chapter08QuasiCoherentDescentEquivalence hp).functor.obj M ≅
        chapter08CanonicalQuasiCoherentDescentData
          (chapter08SingleCoverChoices p) M) := by
  let h := Classical.choice
    (chapter08QuasiCoherentDescentEquivalencePackage hp).canonical
  exact ⟨(h.app M).symm⟩

/-- The chosen equivalence is naturally identified with the canonical
pullback/descent functor.  Objectwise comparisons alone would not transport
full faithfulness or descended morphisms. -/
theorem chapter08_quasiCoherent_descent_equivalence_naturally_canonical
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    Nonempty
      (chapter08CanonicalQuasiCoherentDescentFunctor ≅
        (chapter08QuasiCoherentDescentEquivalence hp).functor) := by
  exact (chapter08QuasiCoherentDescentEquivalencePackage hp).canonical

/-- The pullback/descent functor appearing in the theorem. -/
noncomputable def chapter08QuasiCoherentPullbackDescentFunctor
    {T S : Scheme.{u}} {p : T ⟶ S} (_hp : Chapter08FpqcMorphism p) :
    Chapter08QuasiCoherentModules S ⥤
      Chapter08SingleCoverQuasiCoherentDescentData p :=
  chapter08CanonicalQuasiCoherentDescentFunctor

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

/- The canonical quasi-coherent descent functor therefore has one reusable
   effective/full/faithful interface, rather than requiring downstream users to
   unpack three unrelated assertions. -/
theorem chapter08_quasiCoherent_descent_effective_full_faithful
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p) :
    Chapter08EffectiveFullFaithfulDescent
      (chapter08QuasiCoherentPullbackDescentFunctor hp) := by
  sorry

/-- Effectivity: every quasi-coherent descent datum has a descended sheaf. -/
noncomputable def chapter08DescendedQuasiCoherentModule
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    (D : Chapter08SingleCoverQuasiCoherentDescentData p) :
    Chapter08QuasiCoherentModules S :=
  (chapter08QuasiCoherentDescentEquivalence hp).inverse.obj D

/-- The canonical pullback datum of the descended object is identified with
the original datum. -/
noncomputable def chapter08CanonicalEffectivityComparison
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    (D : Chapter08SingleCoverQuasiCoherentDescentData p) :
    chapter08CanonicalQuasiCoherentDescentData
        (chapter08SingleCoverChoices p)
        (chapter08DescendedQuasiCoherentModule hp D) ≅ D := by
  let h := Classical.choice
    (chapter08_quasiCoherent_descent_equivalence_canonical hp
      (chapter08DescendedQuasiCoherentModule hp D))
  exact h.symm ≪≫ (chapter08QuasiCoherentDescentEquivalence hp).counitIso.app D

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

/-- The same descent theorem for an fpqc covering family, with pairwise and
triple overlap choices. -/
/- The canonical family pullback functor is defined before the bundled
   equivalence so that the package can record its natural comparison. -/
noncomputable def chapter08CanonicalFamilyQuasiCoherentDescentFunctor
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    Chapter08QuasiCoherentModules S ⥤
      Chapter08QuasiCoherentModuleDescentData choices where
  obj := fun M => chapter08CanonicalQuasiCoherentDescentData choices M
  map := fun {_M _N} φ =>
    chapter08CanonicalQuasiCoherentDescentMap choices φ
  map_id := fun M =>
    chapter08CanonicalQuasiCoherentDescentMap_id choices M
  map_comp := fun f g =>
    chapter08CanonicalQuasiCoherentDescentMap_comp choices f g

abbrev Chapter08FamilyQuasiCoherentDescentEquivalencePackage
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :=
  Chapter08EffectiveFullFaithfulDescentPackage
    (chapter08CanonicalFamilyQuasiCoherentDescentFunctor C choices)

noncomputable def chapter08FamilyQuasiCoherentDescentEquivalencePackage
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    Chapter08FamilyQuasiCoherentDescentEquivalencePackage C choices := by
  sorry

/-- The same descent theorem for an fpqc covering family,
   with pairwise and triple overlap choices. -/
noncomputable def chapter08FamilyQuasiCoherentDescentEquivalence
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
      Chapter08QuasiCoherentModules S ≌
      Chapter08QuasiCoherentModuleDescentData choices := by
  exact (chapter08FamilyQuasiCoherentDescentEquivalencePackage C choices).equivalence

/-- The family equivalence is compatible, up to isomorphism in the descent
category, with the canonical pullback datum. -/
theorem chapter08_family_quasiCoherent_descent_equivalence_canonical
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map)
    (M : Chapter08QuasiCoherentModules S) :
    Nonempty
      ((chapter08FamilyQuasiCoherentDescentEquivalence C choices).functor.obj M ≅
        chapter08CanonicalQuasiCoherentDescentData choices M) := by
  let h := Classical.choice
    (chapter08FamilyQuasiCoherentDescentEquivalencePackage C choices).canonical
  exact ⟨(h.app M).symm⟩

/-- The family equivalence is naturally identified with the canonical family
pullback functor; this retains functorial compatibility of local comparisons. -/
theorem chapter08_family_quasiCoherent_descent_equivalence_naturally_canonical
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    Nonempty
      (chapter08CanonicalFamilyQuasiCoherentDescentFunctor C choices ≅
        (chapter08FamilyQuasiCoherentDescentEquivalence C choices).functor) := by
  exact (chapter08FamilyQuasiCoherentDescentEquivalencePackage C choices).canonical

/-- The canonical family pullback/descent functor. -/
noncomputable def chapter08FamilyQuasiCoherentPullbackDescentFunctor
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    Chapter08QuasiCoherentModules S ⥤
      Chapter08QuasiCoherentModuleDescentData choices :=
  chapter08CanonicalFamilyQuasiCoherentDescentFunctor C choices

/-- The family counit, transported through the canonicality comparison, gives
the required effectivity comparison for a family datum. -/
noncomputable def chapter08FamilyCanonicalEffectivityComparison
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map)
    (D : Chapter08QuasiCoherentModuleDescentData choices) :
    chapter08CanonicalQuasiCoherentDescentData choices
        ((chapter08FamilyQuasiCoherentDescentEquivalence C choices).inverse.obj D) ≅ D := by
  let h := Classical.choice
    (chapter08_family_quasiCoherent_descent_equivalence_canonical C choices
      ((chapter08FamilyQuasiCoherentDescentEquivalence C choices).inverse.obj D))
  exact h.symm ≪≫ (chapter08FamilyQuasiCoherentDescentEquivalence C choices).counitIso.app D

/- Full faithfulness for a family is the same componentwise affine-module
argument as for a singleton, with the pairwise overlap equations retained. -/
theorem chapter08_family_pullback_is_full_and_faithful
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map) :
    (chapter08FamilyQuasiCoherentPullbackDescentFunctor C choices).Full ∧
      (chapter08FamilyQuasiCoherentPullbackDescentFunctor C choices).Faithful := by
  sorry

/-- Family descent is interpreted on the pairwise and triple overlaps selected
by `choices`. -/
theorem chapter08_family_descent_effective
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι)
    (choices : Chapter08PullbackChoices C.source C.map)
    (D : Chapter08QuasiCoherentModuleDescentData choices) :
    ∃ M : Chapter08QuasiCoherentModules S,
      Nonempty
        (chapter08CanonicalQuasiCoherentDescentData choices M ≅ D) := by
  let E := chapter08FamilyQuasiCoherentDescentEquivalence C choices
  exact ⟨E.inverse.obj D, ⟨chapter08FamilyCanonicalEffectivityComparison C choices D⟩⟩

/-- A compatible upstairs morphism descends uniquely on every affine open. -/
theorem chapter08_compatible_map_descends_uniquely
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    {D E : Chapter08SingleCoverQuasiCoherentDescentData p}
    (φ : D ⟶ E) :
    ∃! ψ : chapter08DescendedQuasiCoherentModule hp D ⟶
        chapter08DescendedQuasiCoherentModule hp E,
      (chapter08QuasiCoherentPullbackDescentFunctor hp).map ψ =
        (chapter08CanonicalEffectivityComparison hp D).hom ≫ φ ≫
          (chapter08CanonicalEffectivityComparison hp E).inv := by
  sorry

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
