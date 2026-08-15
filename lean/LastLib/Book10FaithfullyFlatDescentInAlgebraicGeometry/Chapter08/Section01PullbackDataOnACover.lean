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
abbrev chapter08PullbackComparison_on_diagonal
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :=
  (D.obj).pullHom'_hom_self ()

/-- The cocycle on the triple overlap. -/
abbrev chapter08PullbackComparison_cocycle
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter08QuasiCoherentPullbackData p) :=
  (D.obj).pullHom'_hom_comp () () ()

/-- A compatible morphism between two single-cover descent data. -/
abbrev Chapter08CompatibleUpstairsMap
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D E : Chapter08QuasiCoherentPullbackData p) := D ⟶ E

/-- Compatibility on the overlap is the defining equation for a morphism in
the descent category. -/
abbrev chapter08CompatibleUpstairsMap_condition
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
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData'.hom_ext
  intro i
  simpa using h

/-- Pullback of a quasi-coherent module along a scheme morphism, packaged in
the book's quasi-coherent full subcategory. -/
def chapter08PullbackQuasiCoherentModule
    {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Chapter08QuasiCoherentModules S) :
    Chapter08QuasiCoherentModules X := by
  refine ⟨(Scheme.Modules.pullback f).obj M.obj, ?_⟩
  exact chapter08_pullback_is_quasicoherent f M

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
abbrev chapter08FamilyPullbackComparison_cocycle
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
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData'.hom_ext
  exact h

/- A finite affine refinement exists over every affine open in the base. -/
theorem chapter08_exists_finite_affine_refinement
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter08FpqcMorphism p)
    {U : S.Opens} (hU : IsAffineOpen U) :
    Nonempty (Chapter08FiniteAffineRefinement p U) := by
  let Q : Scheme.{u} := pullback U.ι p
  let q : Q ⟶ U.toScheme := pullback.fst U.ι p
  have hq : Chapter08FpqcMorphism q := by
    exact chapter08_baseChange_fpqc hp
  let : IsAffine U.toScheme := hU
  obtain ⟨R⟩ := Chapter02.exists_affine_singleton_refinement
    hU (Chapter02.fpqcMorphism_is_singletonFamily hq)
  refine ⟨{
    index := ULift.{u} (Fin R.cardinality)
    finite := inferInstance
    source := fun i => (R.affineOpen i.down).toScheme
    map := fun i => (R.affineOpen i.down).ι
    affine := fun i => R.affine i.down
    flat := fun i => by infer_instance
    isOpenImmersion := fun i => by infer_instance
    coordinateRing := fun i => Γ(Q, R.affineOpen i.down)
    source_isSpec := fun i => ⟨(R.affine i.down).isoSpec⟩
    jointlySurjective := ?_ }⟩
  intro x
  have hx : x ∈ q '' (R.sourceOpen : Set Q) := by
    rw [R.sourceOpen_surjective]
    exact Set.mem_univ x
  rcases hx with ⟨y, hy, hqy⟩
  have hy' : y ∈ ⋃ i : Fin R.cardinality,
      (R.affineOpen i : Set Q) := by
    rw [← R.covers]
    exact hy
  rcases Set.mem_iUnion.1 hy' with ⟨i, hyi⟩
  refine ⟨ULift.up i, ⟨y, hyi⟩, ?_⟩
  simpa [q, Q] using hqy

/-- The finite affine refinement in the source supplies a product faithfully
flat algebra over the affine coordinate ring. -/
theorem chapter08_affine_refinement_product_algebra
    {T S : Scheme.{u}} {p : T ⟶ S} {U : S.Opens}
    (hp : Chapter08FpqcMorphism p) (hU : IsAffineOpen U)
    (hcover : Chapter08FiniteAffineRefinement p U) :
    Nonempty
      (Chapter08FaithfullyFlatProductAlgebra
        (S.presheaf.obj (.op U)) hcover.coordinateRing) := by
  classical
  let Q : Scheme.{u} := pullback U.ι p
  let q : Q ⟶ U.toScheme := pullback.fst U.ι p
  have hq : Chapter08FpqcMorphism q := by
    exact chapter08_baseChange_fpqc hp
  let sourceIso : ∀ i : hcover.index,
      hcover.source i ≅ Spec (hcover.coordinateRing i) := fun i =>
    Classical.choice (hcover.source_isSpec i)
  let f : ∀ i : hcover.index,
      Spec (hcover.coordinateRing i) ⟶
        Spec (S.presheaf.obj (.op U)) := fun i =>
    (sourceIso i).inv ≫ hcover.map i ≫ q ≫ hU.isoSpec.hom
  let φ : ∀ i : hcover.index,
      S.presheaf.obj (.op U) ⟶ hcover.coordinateRing i := fun i =>
    (Scheme.ΓSpecIso (S.presheaf.obj (.op U))).inv ≫ (f i).appTop ≫
      (Scheme.ΓSpecIso (hcover.coordinateRing i)).hom
  have hφ_flat : ∀ i : hcover.index, RingHom.Flat (φ i).hom := by
    intro i
    let : Flat q := hq.1
    let : Flat (hcover.map i) := hcover.flat i
    have hf : Flat (f i) := by
      dsimp [f]
      infer_instance
    have hfa : RingHom.Flat (f i).appTop.hom := f i |>.flat_appTop
    change RingHom.Flat
      (((Scheme.ΓSpecIso (S.presheaf.obj (.op U))).inv ≫ (f i).appTop ≫
        (Scheme.ΓSpecIso (hcover.coordinateRing i)).hom).hom)
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (S.presheaf.obj (.op U))).inv))
      (RingHom.Flat.comp hfa
        (RingHom.Flat.of_bijective
          (ConcreteCategory.bijective_of_isIso
            (Scheme.ΓSpecIso (hcover.coordinateRing i)).hom)))
  let productRingHom : (S.presheaf.obj (.op U) : Type u) →+*
      (∀ i, hcover.coordinateRing i) :=
    RingHom.pi (fun i => (φ i).hom)
  let : Finite hcover.index := hcover.finite
  let : Fintype hcover.index := Fintype.ofFinite hcover.index
  have hproduct_flat : RingHom.Flat productRingHom := by
    let : ∀ i, Algebra (S.presheaf.obj (.op U) : Type u)
        (hcover.coordinateRing i : Type u) :=
      fun i => (φ i).hom.toAlgebra
    let : ∀ i, Module.Flat (S.presheaf.obj (.op U) : Type u)
        (hcover.coordinateRing i : Type u) :=
      fun i => hφ_flat i
    change Module.Flat (S.presheaf.obj (.op U) : Type u)
      (∀ i, (hcover.coordinateRing i : Type u))
    apply Module.Flat.of_linearEquiv
      ((DirectSum.linearEquivFunOnFintype
        (S.presheaf.obj (.op U) : Type u) hcover.index
        (fun i => (hcover.coordinateRing i : Type u))).symm)
  have hproduct_faithfullyFlat : productRingHom.FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨hproduct_flat, ?_⟩
    intro z
    let x : U.toScheme := hU.isoSpec.inv z
    obtain ⟨i, y, hxy⟩ := hcover.jointlySurjective x
    let zi : PrimeSpectrum (hcover.coordinateRing i) := (sourceIso i).hom y
    have hf_spec : f i = Spec.map (φ i) := by
      apply AlgebraicGeometry.ext_of_isAffine
      apply (cancel_mono
        (Scheme.ΓSpecIso (hcover.coordinateRing i)).hom).1
      rw [Scheme.ΓSpecIso_naturality]
      simp [φ]
    have hfi : f i zi = z := by
      change hU.isoSpec.hom
          (q (hcover.map i ((sourceIso i).inv ((sourceIso i).hom y)))) = z
      have hsource : (sourceIso i).inv ((sourceIso i).hom y) = y := by
        exact congrArg (fun g : hcover.source i ⟶ hcover.source i => g y)
          (sourceIso i).hom_inv_id
      rw [hsource, hxy]
      change hU.isoSpec.hom (hU.isoSpec.inv z) = z
      exact congrArg (fun g : Spec (S.presheaf.obj (.op U)) ⟶
          Spec (S.presheaf.obj (.op U)) => g z) hU.isoSpec.inv_hom_id
    have hcomap : PrimeSpectrum.comap (φ i).hom zi = z := by
      change (Spec.map (φ i)) zi = z
      rw [← hf_spec]
      exact hfi
    refine ⟨PrimeSpectrum.sigmaToPi
      (fun i => (hcover.coordinateRing i : Type u)) ⟨i, zi⟩, ?_⟩
    rw [PrimeSpectrum.sigmaToPi_apply, ← PrimeSpectrum.comap_comp_apply]
    have heq : (Pi.evalRingHom (fun i => (hcover.coordinateRing i : Type u)) i).comp
        productRingHom = (φ i).hom := by
      ext a
      rfl
    rw [heq, hcomap]
  refine ⟨{
    finite := hcover.finite
    algebraMap := CommRingCat.ofHom productRingHom
    faithfullyFlat := hproduct_faithfullyFlat }⟩

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
