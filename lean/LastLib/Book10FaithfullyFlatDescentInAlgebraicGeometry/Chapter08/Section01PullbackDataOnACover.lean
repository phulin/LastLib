import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter08.Dependencies

namespace LastLib
namespace Book10FaithfullyFlatDescentInAlgebraicGeometry
namespace Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-!
## 8.1 Pullback data on a cover

The concrete single-cover notation in the source is the unit-indexed instance
of Mathlib's chosen-pullback descent category.  This keeps the comparison map
and its unit/triple-overlap conditions available as named projections. -/

/-- The quasi-coherent pullback datum attached to a single fpqc morphism. -/
abbrev Chapter08QuasiCoherentPullbackData {T S : Scheme.{u}} (p : T ⟶ S) :=
  Chapter08SingleCoverQuasiCoherentDescentData p

/-- The underlying upstairs module in a pullback datum. -/
abbrev chapter08UpstairsModule
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) : T.Modules :=
  (D.obj).obj ()

/-- The comparison map `p₁^* F_T ⟶ p₂^* F_T` before using its canonical
invertibility. -/
def chapter08PullbackComparison
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :=
  (D.obj).hom () ()

/-- The comparison map is an isomorphism, as forced by the unit and cocycle
conditions in the canonical descent-data interface. -/
instance chapter08PullbackComparison.isIso
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :
    IsIso (chapter08PullbackComparison D) := by
  dsimp [chapter08PullbackComparison]
  infer_instance

/-- The book-facing isomorphism `θ : p₁^* F_T ≅ p₂^* F_T`. -/
noncomputable def chapter08PullbackComparisonIso
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :=
  asIso (chapter08PullbackComparison D)

/-- The identity normalization on the diagonal overlap. -/
def chapter08PullbackComparison_on_diagonal
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :=
  (D.obj).pullHom'_hom_self ()

/-- The cocycle on the triple overlap. -/
def chapter08PullbackComparison_cocycle
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :=
  (D.obj).pullHom'_hom_comp () () ()

/-- A compatible morphism between two single-cover descent data. -/
abbrev Chapter08CompatibleUpstairsMap
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D E : Chapter08QuasiCoherentPullbackData p) := D ⟶ E

/-- Compatibility on the overlap is the defining equation for a morphism in
the descent category. -/
def chapter08CompatibleUpstairsMap_condition
    {T S : Scheme.{u}} {p : T ⟶ S}
    {D E : Chapter08QuasiCoherentPullbackData p}
    (φ : Chapter08CompatibleUpstairsMap D E) :=
  φ.hom.comm () ()

/-- A compatible upstairs map is unique when its component on the cover is
fixed. -/
theorem chapter08_compatible_upstairs_map_ext
    {T S : Scheme.{u}} {p : T ⟶ S}
    {D E : Chapter08QuasiCoherentPullbackData p}
    {φ ψ : Chapter08CompatibleUpstairsMap D E}
    (h : φ.hom.hom () = ψ.hom.hom ()) : φ = ψ := by
  exact chapter08_descent_hom_ext h

/-- Pullback of a quasi-coherent module along a scheme morphism, packaged in
the book's quasi-coherent full subcategory. -/
def chapter08PullbackQuasiCoherentModule
    {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Chapter08QuasiCoherentModules S) :
    Chapter08QuasiCoherentModules X := by
  refine ⟨(Scheme.Modules.pullback f).obj M.obj, ?_⟩
  sorry

/-- The pullback operation on quasi-coherent modules is functorial up to the
canonical pseudofunctorial identifications. -/
noncomputable def chapter08PullbackQuasiCoherentComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Chapter08QuasiCoherentModules Z) :
    (Scheme.Modules.pullback (f ≫ g)).obj M.obj ≅
      (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback g).obj M.obj) :=
  (Scheme.Modules.pullbackComp f g).symm.app M.obj

/-- Pullback along an identity morphism is canonically the original
quasi-coherent module. -/
noncomputable def chapter08PullbackQuasiCoherentIdentityComparison
    {X : Scheme.{u}} (M : Chapter08QuasiCoherentModules X) :
    (Scheme.Modules.pullback (𝟙 X)).obj M.obj ≅ M.obj :=
  (Scheme.Modules.pullbackId X).app M.obj

/-- A family-level overlap datum has pairwise comparison maps and the
triple-overlap cocycle, all supplied by `DescentData'`. -/
abbrev Chapter08QuasiCoherentFamilyPullbackData
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f) :=
  Chapter08QuasiCoherentModuleDescentData choices

/-- The family version of the pairwise comparison map. -/
def chapter08FamilyPullbackComparison
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S}
    {choices : Chapter08PullbackChoices X f}
    (D : Chapter08QuasiCoherentFamilyPullbackData choices) (i j : ι) :=
  (D.obj).hom i j

/-- The family comparison maps are invertible. -/
instance chapter08FamilyPullbackComparison.isIso
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S}
    {choices : Chapter08PullbackChoices X f}
    (D : Chapter08QuasiCoherentFamilyPullbackData choices) (i j : ι) :
    IsIso (chapter08FamilyPullbackComparison D i j) := by
  dsimp [chapter08FamilyPullbackComparison]
  infer_instance

/-- The family cocycle on a specified triple of indices. -/
def chapter08FamilyPullbackComparison_cocycle
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S}
    {choices : Chapter08PullbackChoices X f}
    (D : Chapter08QuasiCoherentFamilyPullbackData choices)
    (i j k : ι) :=
  (D.obj).pullHom'_hom_comp i j k

/-- Family descent morphisms are extensional on each member of the cover. -/
theorem chapter08_family_descent_hom_ext
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S}
    {choices : Chapter08PullbackChoices X f}
    {D E : Chapter08QuasiCoherentFamilyPullbackData choices}
    {φ ψ : D ⟶ E} (h : ∀ i, φ.hom.hom i = ψ.hom.hom i) : φ = ψ := by
  sorry

/- A finite affine refinement exists over every affine open in the base. -/
theorem chapter08_exists_finite_affine_refinement
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    {U : S.Opens} (hU : IsAffineOpen U) :
    Nonempty (Chapter08FiniteAffineRefinement p U) := by
  sorry

/-- The finite affine refinement in the source supplies a product faithfully
flat algebra over the affine coordinate ring. -/
theorem chapter08_affine_refinement_product_algebra
    {T S : Scheme.{u}} {p : T ⟶ S} {U : S.Opens}
    (hp : Chapter08FpqcMorphism p) (hU : IsAffineOpen U)
    (hcover : Chapter08FiniteAffineRefinement p U) :
    Nonempty
      (Chapter08FaithfullyFlatProductAlgebra
        (S.presheaf.obj (.op U)) hcover.coordinateRing) := by
  sorry

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
