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
## 8.2 Affine-local construction

This section records the scalar-extension normalization on basic opens, the
local-to-global gluing interface, and the base-change reduction used for a
general morphism over the base.
-/

/-- The descended affine module restricted to `D(f)`. -/
def chapter08AffineRestrictedModule {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    ModuleCat (Localization.Away f) :=
  chapter08LocalizedModule M f

/-- The restriction calculation is exactly extension of scalars along
`R ⟶ R_f`. -/
theorem chapter08_affine_restriction_is_scalar_extension
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    chapter08AffineRestrictedModule M f =
      (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M := by
  rfl

/-- The canonical comparison object for the restriction of an affine module. -/
def chapter08AffineRestrictionComparisonData
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    Chapter08AffineRestrictionComparison M f :=
  chapter08AffineRestrictionComparison.canonical M f

/-- Restriction comparisons are normalized by the same scalar-extension
functor, so the two affine computations use the same module. -/
theorem chapter08_affine_restriction_comparison_is_canonical
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    (chapter08AffineRestrictionComparisonData M f).restricted =
      chapter08AffineRestrictedModule M f := by
  rfl

/-- LOCAL_DEPENDENCY_GUESS: the pinned categorical descent API supplies the
compatibility data, while the final Zariski gluing bridge for affine schemes is
not yet present in an earlier LastLib chapter. -/
structure Chapter08AffineLocalModuleSystem
    {S : Scheme.{u}} (C : Chapter08AffineOpenCover S)
    (choices : Chapter08PullbackChoices
      (fun i => Spec (C.coordinateRing i)) C.map) where
  module : ∀ i, ModuleCat (C.coordinateRing i)
  descent : Chapter08QuasiCoherentModuleDescentData choices
  tildeComparison : ∀ i,
    Nonempty (tilde (module i) ≅ (descent.obj).obj i)

/- LOCAL_DEPENDENCY_GUESS: the witness packages the canonical affine-module
descent and the ordinary quasi-coherent Zariski gluing theorem, which are not
yet exposed together by an earlier LastLib chapter. -/
structure Chapter08AffineLocalGluingWitness
    {S : Scheme.{u}} (C : Chapter08AffineOpenCover S)
    {choices : Chapter08PullbackChoices
      (fun i => Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) where
  descended : Chapter08QuasiCoherentModules S
  /-- The comparison in the descent category is compatible with the overlap
  datum.  Merely having an isomorphism on each member is not enough to effect
  descent. -/
  descentComparison :
    Nonempty
      (chapter08CanonicalQuasiCoherentDescentData choices descended ≅ D.descent)

/-- The coherent descent comparison supplies the local comparison on every
member of the affine cover.  It is derived rather than independent data, so
the local isomorphisms cannot be unrelated to the overlap datum. -/
theorem chapter08_affine_local_gluing_comparison
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices)
    (W : Chapter08AffineLocalGluingWitness C D) (i : C.index) :
    Nonempty
      ((Scheme.Modules.pullback (C.map i)).obj W.descended.obj ≅
        tilde (D.module i)) := by
  let e := Classical.choice W.descentComparison
  let ei := Classical.choice (D.tildeComparison i)
  change tilde (D.module i) ≅ D.descent.obj.obj i at ei
  let h := e.hom.hom.hom i
  let hi := e.inv.hom.hom i
  have h_hinv : h ≫ hi = 𝟙 _ := by
    exact congrArg (fun q => q.hom.hom i) e.hom_inv_id
  have hi_h : hi ≫ h = 𝟙 _ := by
    exact congrArg (fun q => q.hom.hom i) e.inv_hom_id
  let hIso :
      (chapter08CanonicalQuasiCoherentDescentData choices W.descended).obj.obj i ≅
        D.descent.obj.obj i :=
    { hom := h
      inv := hi
      hom_inv_id := h_hinv
      inv_hom_id := hi_h }
  exact ⟨hIso ≪≫ ei.symm⟩

/- The canonical identifications of the affine sheaves agree on every
pairwise intersection. -/
theorem chapter08_affine_tilde_restriction_agrees
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) (i j : C.index) :
    Nonempty
      ((Scheme.Modules.pullback (choices.sq i j).p₁).obj
          (tilde (D.module i)) ≅
        (Scheme.Modules.pullback (choices.sq i j).p₂).obj
          (tilde (D.module j))) := by
  let q : Chapter08ModuleDescentData choices := D.descent.obj
  let ei := Classical.choice (D.tildeComparison i)
  let ej := Classical.choice (D.tildeComparison j)
  change tilde (D.module i) ≅ q.obj i at ei
  change tilde (D.module j) ≅ q.obj j at ej
  let h := Pseudofunctor.DescentData'.pullHom' q.hom
    (choices.sq i j).p (choices.sq i j).p₁ (choices.sq i j).p₂
  let : IsIso h := by
    dsimp [h]
    infer_instance
  have e1 := Functor.mapIso (Scheme.Modules.pullback (choices.sq i j).p₁) ei
  have e2 := Functor.mapIso (Scheme.Modules.pullback (choices.sq i j).p₂) ej
  have e3 := asIso h
  exact ⟨e1 ≪≫ e3 ≪≫ e2.symm⟩

/-- The glued sheaf carries a single coherent descent comparison; its local
comparisons are recovered by `chapter08_affine_local_gluing_comparison`. -/
theorem chapter08_affine_local_gluing_with_comparisons
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) :
    Nonempty (Chapter08AffineLocalGluingWitness C D) := by
  sorry

/-- Canonical affine-local gluing produces a quasi-coherent sheaf on the base
together with its local comparisons and descent comparison.  Retaining these
comparisons is essential: `Nonempty (Chapter08QuasiCoherentModules S)` alone
would not say that the given local data glue. -/
theorem chapter08_affine_local_gluing
    {S : Scheme.{u}} {C : Chapter08AffineOpenCover S}
    {choices : Chapter08PullbackChoices
      (fun i => Spec (C.coordinateRing i)) C.map}
    (D : Chapter08AffineLocalModuleSystem C choices) :
    Nonempty (Chapter08AffineLocalGluingWitness C D) := by
  exact chapter08_affine_local_gluing_with_comparisons (C := C)
    (choices := choices) D

/-- A compatible affine module descent datum produces the ring-level witness
used in the affine-local construction.  The equality records which datum the
witness represents; a bare `Nonempty` witness would not connect it to `D`. -/
theorem chapter08_affine_module_descent_effective
    {A : CommRingCat.{u}} {ι : Type u} {B : ι → CommRingCat.{u}}
    (P : Chapter08FaithfullyFlatProductAlgebra A B)
    (D : Chapter08SingleCoverQuasiCoherentDescentData
      (Spec.map P.algebraMap)) :
    ∃ W : Chapter08AffineModuleDescentWitness A B P, W.descent = D := by
  sorry

/- The two presentations of a double basic-open localization have a
   canonical algebra equivalence; restriction of scalars transports modules to
the canonical localization ring. -/
noncomputable def chapter08LocalizationAssociativityEquiv
    {R : CommRingCat.{u}} (f g : R) :
    Localization.Away (f * g) ≃ₐ[R]
      Localization.Away (algebraMap R (Localization.Away f) g) :=
  IsLocalization.algEquiv (R := R) (Submonoid.powers (f * g))
    (Localization.Away (f * g))
    (Localization.Away (algebraMap R (Localization.Away f) g))

noncomputable def chapter08DoublyLocalizedModule
    {R : CommRingCat.{u}} (M : ModuleCat R) (f g : R) :
    ModuleCat (Localization.Away (f * g)) :=
  (ModuleCat.restrictScalars
    (chapter08LocalizationAssociativityEquiv f g).toRingEquiv.toRingHom).obj
    (chapter08LocalizedModule (R := CommRingCat.of (Localization.Away f))
      (chapter08LocalizedModule M f)
      (algebraMap R (Localization.Away f) g))

theorem chapter08_affine_restriction_associates
    {R : CommRingCat.{u}} (M : ModuleCat R) (f g : R) :
    Nonempty
      (chapter08LocalizedModule M (f * g) ≅
        chapter08DoublyLocalizedModule M f g) := by
  let e := chapter08LocalizationAssociativityEquiv (R := R) f g
  let hB : (R : Type u) →+* Localization.Away f :=
    algebraMap R (Localization.Away f)
  let hC : (R : Type u) →+* Localization.Away (f * g) :=
    algebraMap R (Localization.Away (f * g))
  let hD : Localization.Away f →+* Localization.Away (algebraMap R (Localization.Away f) g) :=
    algebraMap _ _
  let hBC : Localization.Away f →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift f
      (IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (f * g))
        (x := f * g) (r := f) ⟨g, by simp⟩)
  let _algebra : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    hBC.toAlgebra
  have hCcomp : hBC.comp hB = hC := by
    ext x
    simp [hBC, hB, hC]
  have hcomp : e.toRingHom.comp hBC = hD := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp [e, hBC, hD, chapter08LocalizationAssociativityEquiv]
    rw [IsScalarTower.algebraMap_apply R (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g))]
  let Bobj : ModuleCat (R : Type u) :=
    (ModuleCat.restrictScalars hB).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f))
  let Cobj : ModuleCat (R : Type u) :=
    (ModuleCat.restrictScalars hC).obj
      (ModuleCat.of (Localization.Away (f * g)) (Localization.Away (f * g)))
  let Bmod : Type u := Bobj
  let Cmod : Type u := Cobj
  let _moduleRB : Module (R : Type u) Bmod := Bobj.isModule
  let _moduleRC : Module (R : Type u) Cmod := Cobj.isModule
  let _moduleBB : Module (Localization.Away f) Bmod := by
    change Module (Localization.Away f) (Localization.Away f)
    infer_instance
  let _moduleCC : Module (Localization.Away (f * g)) Cmod := by
    change Module (Localization.Away (f * g)) (Localization.Away (f * g))
    infer_instance
  let _moduleBC : Module (Localization.Away f) Cmod := hBC.toModule
  have _towerRB : IsScalarTower (R : Type u) (Localization.Away f) Bmod := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    rfl
  have _towerCC : IsScalarTower (R : Type u) (Localization.Away (f * g)) Cmod := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    rfl
  have _towerRC : IsScalarTower (R : Type u) (Localization.Away f) Cmod := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    change (hBC (hB r)) • (show (Cobj : Type u) from x) =
      r • (show (Cobj : Type u) from x)
    have hr : hBC (hB r) = hC r := by
      simpa using congrArg (fun k : (R : Type u) →+*
        Localization.Away (f * g) => k r) hCcomp
    calc
      hBC (hB r) • (show (Cobj : Type u) from x) =
          hC r • (show (Cobj : Type u) from x) := by rw [hr]
      _ = r • (show (Cobj : Type u) from x) :=
        (ModuleCat.restrictScalars.smul_def' (M := ModuleCat.of
          (Localization.Away (f * g)) (Localization.Away (f * g))) hC r
          (show Localization.Away (f * g) from x)).symm
  have _towerBC : IsScalarTower (Localization.Away f)
      (Localization.Away (f * g)) Cmod := by
    apply IsScalarTower.of_algebraMap_smul
    intro b x
    change algebraMap (Localization.Away f) (Localization.Away (f * g)) b •
      (show (Cobj : Type u) from x) =
      b • (show (Cobj : Type u) from x)
    rw [show algebraMap (Localization.Away f) (Localization.Away (f * g)) b =
      hBC b by rfl]
    rfl
  have _smulComm : SMulCommClass (Localization.Away f)
      (Localization.Away (f * g)) Cmod :=
    IsScalarTower.to_smulCommClass
  let targetD :=
    (ModuleCat.restrictScalars e.toRingHom).obj
      (ModuleCat.of (Localization.Away (algebraMap R (Localization.Away f) g))
        (Localization.Away (algebraMap R (Localization.Away f) g)))
  let _moduleBD : Module (Localization.Away f) (targetD : Type _) := hD.toModule
  have _towerBD : IsScalarTower (Localization.Away f)
      (Localization.Away (f * g)) (targetD : Type _) := by
    apply IsScalarTower.of_algebraMap_smul
    intro b x
    change algebraMap (Localization.Away f)
        (Localization.Away (f * g)) b •
      (show (targetD : Type _) from x) =
      b • (show (targetD : Type _) from x)
    rw [show algebraMap (Localization.Away f) (Localization.Away (f * g)) b =
      hBC b by rfl]
    change e (hBC b) *
        (show Localization.Away (algebraMap R (Localization.Away f) g) from x) =
      hD b * (show Localization.Away (algebraMap R (Localization.Away f) g) from x)
    rw [show e (hBC b) = hD b by
      exact congrArg (fun k : Localization.Away f →+*
        Localization.Away (algebraMap R (Localization.Away f) g) => k b) hcomp]
  let eLin : Localization.Away (f * g) ≃ₗ[Localization.Away (f * g)]
      (targetD : Type _) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro c d
        change e (c * d) = e c • e d
        calc
          e (c * d) = e c * e d := map_mul e c d
          _ = e c • e d := by rfl }
  let sourceObj := (ModuleCat.extendScalars hC).obj M
  let finalObj :=
    (ModuleCat.restrictScalars e.toRingHom).obj
      ((ModuleCat.extendScalars hD).obj
        ((ModuleCat.extendScalars hB).obj M))
  let _moduleSource : Module (Localization.Away (f * g))
      (TensorProduct (R : Type u) Cmod (M : Type _)) := by
    change Module (Localization.Away (f * g)) (sourceObj : Type _)
    exact sourceObj.isModule
  let targetTensor :=
    TensorProduct (Localization.Away f) (targetD : Type _)
      (TensorProduct (R : Type u) Bmod (M : Type _))
  let _moduleTarget : Module (Localization.Away (f * g)) targetTensor := by
    change Module (Localization.Away (f * g)) (finalObj : Type _)
    exact finalObj.isModule
  let cRid :=
    TensorProduct.AlgebraTensorModule.rid
      (Localization.Away f : Type u)
      (Localization.Away (f * g) : Type u)
      Cmod
  let cAssoc :=
    TensorProduct.AlgebraTensorModule.assoc
      (R : Type u)
      (Localization.Away f : Type u)
      (Localization.Away (f * g) : Type u)
      Cmod Bmod (M : Type _)
  let cCongr :=
    TensorProduct.AlgebraTensorModule.congr cRid
      (LinearEquiv.refl (R : Type u) (M : Type _))
  let cCD :
      TensorProduct (Localization.Away f) Cmod
          (TensorProduct (R : Type u) Bmod (M : Type _)) ≃ₗ[Localization.Away (f * g)]
        targetTensor :=
    TensorProduct.AlgebraTensorModule.congr eLin
      (LinearEquiv.refl (Localization.Away f)
        (TensorProduct (R : Type u) Bmod (M : Type _)))
  let q := ((cCongr.symm.trans cAssoc).trans cCD)
  have hlin : (sourceObj : Type _) ≃ₗ[Localization.Away (f * g)] (finalObj : Type _) :=
    { toFun := q
      invFun := q.symm
      left_inv := by
        intro x
        exact q.left_inv x
      right_inv := by
        intro x
        exact q.right_inv x
      map_add' := by
        intro x y
        exact q.map_add x y
      map_smul' := by
        intro c x
        change q (c • x) = c • q x
        exact q.map_smul c x }
  change Nonempty ((sourceObj : ModuleCat (Localization.Away (f * g))) ≅ finalObj)
  exact ⟨LinearEquiv.toModuleIso hlin⟩

/-- The canonical affine restriction is the scalar-extension model used for
the direct descent calculation on a basic open. -/
theorem chapter08_affine_descent_commutes_with_restriction
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    chapter08AffineRestrictedModule M f =
      (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M ∧
        Nonempty (Chapter08AffineRestrictionSheafComparison M f) := by
  exact ⟨chapter08_affine_restriction_is_scalar_extension M f,
    chapter08_affine_restriction_sheaf_comparison M f⟩

/-- Base change of an fpqc cover is the cover used for descent over a morphism
`X ⟶ S`. -/
theorem chapter08_base_change_cover_for_morphism
    {X T S : Scheme.{u}} {f : X ⟶ S} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) :
    Chapter08FpqcMorphism (chapter08BaseChangedCoverMap f p) :=
  chapter08_baseChange_fpqc hp

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
