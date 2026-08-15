import Mathlib.CategoryTheory.Adjunction.Unique
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05.Section01InvariantModule

/-!
# 5.2 Proof of effectivity

The direct effectivity statements are recorded with the same invariant and evaluation maps as in
§5.1.  The categorical comparison theorem is also exposed, since it is the pinned Mathlib route
to the equivalence of modules and descent data.
-/

open CategoryTheory
open CategoryTheory.Limits
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
  exact faithfullyFlat_comonadic_comparison_is_equivalence hAB

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
  letI : Module D C := s.toRingHom.toModule
  letI : Module C Q.A :=
    ((ModuleCat.restrictScalars (algebraMap C D)).obj Q.A).isModule
  letI : Module C ((descentComonad C D).obj Q.A) :=
    ((ModuleCat.restrictScalars (algebraMap C D)).obj
      ((descentComonad C D).obj Q.A)).isModule
  letI : Module D
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u) :=
    ((descentComonad C D).obj Q.A).isModule
  letI : Module C ((descentComonad C D).obj Q.A) :=
    ((ModuleCat.restrictScalars (algebraMap C D)).obj
      ((descentComonad C D).obj Q.A)).isModule
  letI : IsScalarTower C D Q.A := IsScalarTower.of_compHom C D _
  letI : IsScalarTower C D
      (((ModuleCat.restrictScalars (algebraMap C D)).obj Q.A) : Type u) :=
    IsScalarTower.of_compHom C D _
  let eDAdd :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        ≃+ D :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let eD :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        ≃ₗ[C] D :=
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)).isModule) _ eDAdd
      (fun c x => by
        have hD : ∀ z, eDAdd z = (z : D) := by intro z; rfl
        rw [hD, hD, ModuleCat.restrictScalars.smul_def]
        exact IsScalarTower.algebraMap_smul (R := C) (A := D) (M := D) c (x : D))
  let p :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        →ₗ[C] Q.A →ₗ[C] Q.A :=
    { toFun := fun d =>
        { toFun := fun q => algebraMap C D (s (eD d)) • q
          map_add' := by intro q q'; simp
          map_smul' := by
            intro c q
            exact smul_algebra_smul_comm c (algebraMap C D (s (eD d))) q }
      map_add' := by
        intro d d'
        ext q
        dsimp
        rw [eD.map_add]
        simp only [map_add, add_smul]
      map_smul' := by
        intro c d
        ext q
        dsimp
        change algebraMap C D (s (eD (c • d))) • q =
          c • (algebraMap C D (s (eD d)) • q)
        rw [eD.map_smul]
        rw [Algebra.smul_def, map_mul, s.commutes]
        rw [← IsScalarTower.algebraMap_smul (R := C) (A := D) (M := Q.A)]
        simp [map_mul, mul_smul] }
  let qa : Q.A →ₗ[C]
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u) :=
    { toFun := Q.a.hom
      map_add' := by
        intro x y
        exact Q.a.hom.map_add x y
      map_smul' := by
        intro c q
        change Q.a.hom ((algebraMap C D c) • q) =
          (algebraMap C D c) • Q.a.hom q
        exact Q.a.hom.map_smul _ _ }
  let pi : Q.A →ₗ[C] Q.A :=
    (TensorProduct.lift p).comp qa
  letI : Module D
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A)) :=
    ((descentComonad C D).obj Q.A).isModule
  have hlift : ∀ (d : D)
      (x : ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A))),
      (TensorProduct.lift p) (d • x) = s d • (TensorProduct.lift p) x := by
    intro d x
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul d' q' =>
        change p (d • d') q' = s d • s (eD d') • q'
        dsimp [p]
        have heD : eD (d • d') = d * eD d' := by
          change d * eD d' = d * eD d'
          rfl
        rw [heD, map_mul]
        rw [← IsScalarTower.algebraMap_smul (R := C) (A := D) (M := Q.A)]
        simp [mul_smul]
    | add x y hx hy =>
        simp only [smul_add, map_add, hx, hy]
  have hpi : ∀ (d : D)
      (q : Q.A),
      pi (d • q) = s d • pi q := by
    intro d q
    have hqa : qa (d • q) = d • qa q := by
      change Q.a.hom (d • (q : Q.A)) = d • Q.a.hom (q : Q.A)
      exact Q.a.hom.map_smul _ _
    change (TensorProduct.lift p) (qa (d • q)) =
      s d • (TensorProduct.lift p) (qa q)
    rw [hqa]
    exact hlift d (qa q)
  let fadd : C →+ Q.A →+ Q.A :=
    { toFun := fun c =>
        { toFun := fun q => c • pi q
          map_zero' := by simp
          map_add' := by
            intro q q'
            rw [map_add, smul_add] }
      map_zero' := by
        ext q
        simp
      map_add' := by
        intro c c'
        ext q
        change (c + c') • pi q = c • pi q + c' • pi q
        rw [add_smul] }
  have hbal : ∀ (d : D) (c : C) (q : Q.A),
      fadd (d • c) q = fadd c (d • q) := by
    intro d c q
    dsimp [fadd]
    rw [RingHom.toModule_smul, hpi]
    change (s d * c) • pi q = c • s d • pi q
    rw [mul_smul, smul_comm]
  let flift : (C ⊗[D] Q.A) →+ Q.A :=
    TensorProduct.liftAddHom fadd hbal
  let l : (C ⊗[D] Q.A) →ₗ[C] Q.A :=
    { toFun := flift
      map_add' := by
        intro x y
        exact flift.map_add x y
      map_smul' := by
        intro c x
        induction x using TensorProduct.induction_on with
        | zero => simp [flift]
        | tmul c' q' =>
            simp [flift, fadd, TensorProduct.smul_tmul']
            rw [mul_smul]
        | add x y hx hy =>
            simp only [smul_add, map_add, hx, hy] }
  let lHom : splitInvariant s Q ⟶
      (ModuleCat.restrictScalars (algebraMap C D)).obj Q.A :=
    ModuleCat.ofHom (X := splitInvariant s Q)
      (Y := (ModuleCat.restrictScalars (algebraMap C D)).obj Q.A) l
  exact
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap C D)).homEquiv
      (splitInvariant s Q) Q.A).symm lHom

theorem splitCover_effective (s : D →ₐ[C] C) (Q : DescentDatum C D) :
    Function.Bijective (splitEvaluation s Q) := by
  letI : Module D C := s.toRingHom.toModule
  letI : Module C Q.A :=
    ((ModuleCat.restrictScalars (algebraMap C D)).obj Q.A).isModule
  letI : Module C ((descentComonad C D).obj Q.A) :=
    ((ModuleCat.restrictScalars (algebraMap C D)).obj
      ((descentComonad C D).obj Q.A)).isModule
  letI : Module D
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u) :=
    ((descentComonad C D).obj Q.A).isModule
  letI : Module D
      (((ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q)) : Type u) :=
    ((ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q)).isModule
  letI : IsScalarTower C D
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u) :=
    IsScalarTower.of_compHom C D _
  letI : IsScalarTower C D Q.A := IsScalarTower.of_compHom C D _
  let j : Q.A →ₗ[C] (splitInvariant s Q : Type u) :=
    { toFun := fun q => (1 : C) ⊗ₜ[D] q
      map_add' := by
        intro q q'
        exact TensorProduct.tmul_add _ _ _
      map_smul' := by
        intro c q
        change (1 : C) ⊗ₜ[D] (algebraMap C D c • q) =
          c • ((1 : C) ⊗ₜ[D] q)
        rw [TensorProduct.tmul_smul]
        simp [RingHom.toModule_smul, s.commutes] }
  let t :
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u) →ₗ[D]
      (((ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q)) : Type u) :=
    TensorProduct.AlgebraTensorModule.lTensor D
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)) j
  let g : Q.A →ₗ[D]
      (((ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q)) : Type u) :=
    t.comp Q.a.hom
  let eDAdd :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        ≃+ D :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let eD :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        ≃ₗ[C] D :=
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)).isModule) _ eDAdd
      (fun c x => by
        have hD : ∀ z, eDAdd z = (z : D) := by intro z; rfl
        rw [hD, hD, ModuleCat.restrictScalars.smul_def]
        exact IsScalarTower.algebraMap_smul (R := C) (A := D) (M := D) c (x : D))
  let p :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        →ₗ[C] Q.A →ₗ[C] Q.A :=
    { toFun := fun d =>
        { toFun := fun q => algebraMap C D (s (eD d)) • q
          map_add' := by intro q q'; simp
          map_smul' := by
            intro c q
            exact smul_algebra_smul_comm c (algebraMap C D (s (eD d))) q }
      map_add' := by
        intro d d'
        ext q
        dsimp
        rw [eD.map_add]
        simp only [map_add, add_smul]
      map_smul' := by
        intro c d
        ext q
        dsimp
        change algebraMap C D (s (eD (c • d))) • q =
          c • (algebraMap C D (s (eD d)) • q)
        rw [eD.map_smul]
        rw [Algebra.smul_def, map_mul, s.commutes]
        rw [← IsScalarTower.algebraMap_smul (R := C) (A := D) (M := Q.A)]
        simp [map_mul, mul_smul] }
  let qa : Q.A →ₗ[C]
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u) :=
    { toFun := Q.a.hom
      map_add' := by intro x y; exact Q.a.hom.map_add x y
      map_smul' := by
        intro c q
        change Q.a.hom ((algebraMap C D c) • q) =
          (algebraMap C D c) • Q.a.hom q
        exact Q.a.hom.map_smul _ _ }
  let pi : Q.A →ₗ[C] Q.A := (TensorProduct.lift p).comp qa
  have hsplit (d :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u))
      (c : C) (q : Q.A) :
      splitEvaluation s Q
          (d ⊗ₜ[C] ((c ⊗ₜ[D] q) : (splitInvariant s Q : Type u))) =
        eD d • c • pi q := by
    rfl
  let rb :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        →ₗ[D] Q.A →ₗ[C] Q.A :=
    { toFun := fun d =>
        { toFun := fun q => eD d • pi q
          map_add' := by intro q q'; simp
          map_smul' := by
            intro c q
            rw [pi.map_smul]
            exact smul_algebra_smul_comm c (eD d) (pi q) }
      map_add' := by
        intro d d'
        ext q
        change eD (d + d') • pi q = eD d • pi q + eD d' • pi q
        rw [eD.map_add, add_smul]
      map_smul' := by
        intro d d'
        ext q
        change eD (d • d') • pi q = d • (eD d' • pi q)
        change (d * eD d') • pi q = d • (eD d' • pi q)
        rw [mul_smul] }
  let r :
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u) →ₗ[D] Q.A :=
    TensorProduct.AlgebraTensorModule.lift rb
  let p0 : ((descentComonad C D).obj Q.A : Type u) →ₗ[C] Q.A :=
    TensorProduct.lift p
  let kb :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u)
        →ₗ[D] ((descentComonad C D).obj Q.A : Type u) →ₗ[C] Q.A :=
    { toFun := fun d =>
        { toFun := fun x => eD d • p0 x
          map_add' := by
            intro x x'
            rw [p0.map_add, smul_add]
          map_smul' := by
            intro c x
            rw [p0.map_smul]
            exact smul_algebra_smul_comm c (eD d) (p0 x) }
      map_add' := by
        intro d d'
        ext x
        change eD (d + d') • p0 x = eD d • p0 x + eD d' • p0 x
        rw [eD.map_add, add_smul]
      map_smul' := by
        intro d d'
        ext x
        change eD (d • d') • p0 x = d • (eD d' • p0 x)
        change (d * eD d') • p0 x = d • (eD d' • p0 x)
        rw [mul_smul] }
  let k : (((descentComonad C D).toFunctor ⋙ (descentComonad C D).toFunctor).obj Q.A : Type u)
      →ₗ[D] Q.A :=
    TensorProduct.AlgebraTensorModule.lift kb
  have ht (d :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u))
      (q : Q.A) :
      t (d ⊗ₜ[C] q) =
        (d ⊗ₜ[C] j q :
          (((ModuleCat.extendScalars (algebraMap C D)).obj (splitInvariant s Q)) : Type u)) := by
    rfl
  have hr (d :
      (((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D)) : Type u))
      (q : Q.A) :
      r (d ⊗ₜ[C] q) = eD d • pi q := by
    rfl
  have hj (q : Q.A) : j q = (1 : C) ⊗ₜ[D] q := by
    rfl
  have h_eval_t (x :
      ((((ModuleCat.restrictScalars (algebraMap C D)).obj (ModuleCat.of D D) : Type u)
        ⊗[C] Q.A) : Type u)) :
      splitEvaluation s Q (t x) = r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul d q =>
        rw [ht, hr]
        rw [hj]
        simpa using hsplit d 1 q
    | add x y hx hy =>
        simp only [map_add, hx, hy]
  have hdelta_map :
      k.comp ((descentComonad C D).δ.app Q.A).hom =
        ((descentComonad C D).ε.app Q.A).hom := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro d q
    change k
        (((ModuleCat.extendScalars (algebraMap C D)).map
          ((ModuleCat.extendRestrictScalarsAdj (algebraMap C D)).unit.app
            ((ModuleCat.restrictScalars (algebraMap C D)).obj Q.A))).hom
          (d ⊗ₜ[C] q)) =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap C D)).counit.app Q.A).hom
        (d ⊗ₜ[C] q)
    rw [ModuleCat.ExtendScalars.map_tmul,
      ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    rfl
  have hkmap_map :
      k.comp ((descentComonad C D).map Q.a).hom = r := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro d q
    change k (((ModuleCat.extendScalars (algebraMap C D)).map Q.a).hom
      (d ⊗ₜ[C] q)) = r (d ⊗ₜ[C] q)
    rw [ModuleCat.ExtendScalars.map_tmul]
    rfl
  have hcoassoc (q : Q.A) := congrArg (fun f => f.hom q) Q.coassoc
  have hcounit (q : Q.A) := congrArg (fun f => f.hom q) Q.counit
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
  let adj := ModuleCat.extendRestrictScalarsAdj.{_, u, u} (algebraMap A B)
  let D' : adj.toComonad.Coalgebra := D
  let hK : (Comonad.comparison adj).IsEquivalence :=
    faithfullyFlat_comonadic_comparison_is_equivalence hAB
  let KEquiv := @Functor.asEquivalence _ _ _ _ (Comonad.comparison adj) hK
  have hc : IsIso ((Comonad.ComonadicityInternal.comparisonAdjunction adj).counit.app D') := by
    let adj' := KEquiv.toAdjunction
    rw [← Adjunction.rightAdjointUniq_hom_app_counit
      (Comonad.ComonadicityInternal.comparisonAdjunction adj) adj' D']
    let rIso :=
      (Comonad.ComonadicityInternal.comparisonAdjunction adj).rightAdjointUniq adj' |>.app D'
    have hIsoMap : IsIso ((Comonad.comparison adj).map rIso.hom) :=
      Iso.isIso_hom ((Comonad.comparison adj).mapIso rIso)
    have hIsoC : IsIso (adj'.counit.app D') := by
      dsimp [adj']
      change IsIso (KEquiv.counitIso.hom.app D')
      exact NatIso.hom_app_isIso _ _
    change IsIso ((Comonad.comparison adj).map rIso.hom ≫ adj'.counit.app D')
    exact IsIso.comp_isIso' hIsoMap hIsoC
  let i : invariantModuleCat D' ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj D'.A :=
    ModuleCat.ofHom (X := invariantModuleCat D')
      (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)
      (invariantModule D').subtype
  have hi : i ≫ (ModuleCat.restrictScalars (algebraMap A B)).map D'.a =
      i ≫ adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A) := by
    ext m
    change ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a).hom m.1 =
      (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)).hom m.1
    exact (mem_invariantModule_iff D' m.1).mp m.property
  let fork : Fork
      ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a)
      (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)) :=
    Fork.ofι i hi
  have hfork : IsLimit fork := by
    refine Fork.IsLimit.mk fork (fun s => ?_) (fun s => ?_) (fun s m hm => ?_)
    · refine ModuleCat.ofHom
        ((s.ι).hom.codRestrict (invariantModule D') (fun x => ?_))
      change ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a).hom
          ((s.ι).hom x) =
        (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)).hom
          ((s.ι).hom x)
      have hs := congrArg (fun k => k.hom x) s.condition
      change ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a).hom
          ((s.ι).hom x) =
        (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)).hom
          ((s.ι).hom x) at hs
      exact hs
    · ext x
      rfl
    · apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      exact congrArg (fun k => k.hom x) hm
  let iIso : invariantModuleCat D' ≅
      Comonad.ComonadicityInternal.comparisonRightAdjointObj adj D' :=
    IsLimit.conePointUniqueUpToIso hfork (limit.isLimit _)
  have hiIso : iIso.hom ≫
      equalizer.ι
        ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a)
        (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)) = i := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp hfork (limit.isLimit _) WalkingParallelPair.zero
  let c : (Comonad.comparison adj).obj
      (Comonad.ComonadicityInternal.comparisonRightAdjointObj adj D') ⟶ D' :=
    (Comonad.ComonadicityInternal.comparisonAdjunction adj).counit.app D'
  have hc' : IsIso c := hc
  let cIso : (Comonad.comparison adj).obj
      (Comonad.ComonadicityInternal.comparisonRightAdjointObj adj D') ≅ D' :=
    { hom := c
      inv := Classical.choose hc'.out
      hom_inv_id := (Classical.choose_spec hc'.out).1
      inv_hom_id := (Classical.choose_spec hc'.out).2 }
  have hfactor :
      ((Comonad.comparison adj).map iIso.hom ≫ c).f = evaluationMap D' := by
    change (ModuleCat.extendScalars (algebraMap A B)).map iIso.hom ≫ c.f =
      evaluationMap D'
    dsimp [c]
    rw [Comonad.ComonadicityInternal.comparisonAdjunction_counit_f_aux]
    change (ModuleCat.extendScalars (algebraMap A B)).map iIso.hom ≫
        (adj.homEquiv _ D'.A).symm
          (equalizer.ι
            ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a)
            (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A))) =
      (adj.homEquiv _ D'.A).symm i
    have hnat := adj.homEquiv_naturality_left_symm
      (Y := D'.A) iIso.hom
        (equalizer.ι
          ((ModuleCat.restrictScalars (algebraMap A B)).map D'.a)
          (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D'.A)))
    rw [← hnat, hiIso]
  let eIso : (Comonad.comparison adj).obj (invariantModuleCat D') ≅ D' :=
    (Comonad.comparison adj).mapIso iIso ≪≫ cIso
  let eIsoF : (ModuleCat.extendScalars (algebraMap A B)).obj
      (invariantModuleCat D') ≅ D'.A :=
    (Comonad.forget adj.toComonad).mapIso eIso
  have heval : eIsoF.hom = evaluationMap D' := by
    change ((Comonad.comparison adj).map iIso.hom ≫ c).f = evaluationMap D'
    exact hfactor
  have hevalIso : IsIso (evaluationMap D') := by
    rw [← heval]
    exact Iso.isIso_hom eIsoF
  change Function.Bijective (evaluationMap D')
  exact (ConcreteCategory.isIso_iff_bijective (evaluationMap D')).mp hevalIso

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
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap A B)
  let i : invariantModuleCat D ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj D.A :=
    ModuleCat.ofHom (X := invariantModuleCat D)
      (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj D.A)
      (invariantModule D).subtype
  have hi : i ≫ (ModuleCat.restrictScalars (algebraMap A B)).map D.a =
      i ≫ adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A) := by
    ext m
    change ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom m.1 =
      (adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A)).hom m.1
    exact (mem_invariantModule_iff D m.1).mp m.property
  have hev : evaluationMap D =
      (adj.homEquiv (invariantModuleCat D) D.A).symm i := rfl
  let a' : D.A ⟶
      (ModuleCat.extendScalars (algebraMap A B)).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A) := D.a
  have hei : adj.unit.app (invariantModuleCat D) ≫
        (ModuleCat.restrictScalars (algebraMap A B)).map
          ((adj.homEquiv (invariantModuleCat D) D.A).symm i) = i := by
    simpa only [Adjunction.homEquiv_unit] using
      (adj.homEquiv (invariantModuleCat D) D.A).apply_symm_apply i
  have hi' : i ≫ (ModuleCat.restrictScalars (algebraMap A B)).map a' =
      i ≫ adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A) := by
    change i ≫ (ModuleCat.restrictScalars (algebraMap A B)).map D.a =
      i ≫ adj.unit.app ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A)
    exact hi
  change
    (ModuleCat.extendScalars (algebraMap A B)).map
        (adj.unit.app (invariantModuleCat D)) ≫
      (ModuleCat.extendScalars (algebraMap A B)).map
        ((ModuleCat.restrictScalars (algebraMap A B)).map (evaluationMap D)) =
      evaluationMap D ≫ D.a
  rw [hev]
  change
    (ModuleCat.extendScalars (algebraMap A B)).map
        (adj.unit.app (invariantModuleCat D)) ≫
      (ModuleCat.extendScalars (algebraMap A B)).map
        ((ModuleCat.restrictScalars (algebraMap A B)).map
          ((adj.homEquiv (invariantModuleCat D) D.A).symm i)) =
      (adj.homEquiv (invariantModuleCat D) D.A).symm i ≫ a'
  simp only [Functor.id_obj, Functor.comp_obj]
  apply (adj.homEquiv (invariantModuleCat D)
      ((ModuleCat.extendScalars (algebraMap A B)).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A))).injective
  conv_lhs => rw [adj.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit]
  conv_lhs =>
    rw [Category.assoc]
    rw [← (ModuleCat.restrictScalars (algebraMap A B)).map_comp]
    rw [← (ModuleCat.extendScalars (algebraMap A B)).map_comp]
    rw [hei]
    rw [adj.unit_naturality]
  conv_rhs =>
    rw [Functor.map_comp]
    rw [← Category.assoc]
    rw [hei]
  exact hi'.symm

theorem evaluationMap_is_underlying_descent_iso
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (D : DescentDatum A B) :
    ∃ e : ((descentComparison A B).obj (invariantModuleCat D)) ≅ D,
      e.hom.f = evaluationMap D := by
  let e : (descentComparison A B).obj (invariantModuleCat D) ⟶ D :=
    { f := evaluationMap D
      h := evaluationMap_compatible_with_descent_data D }
  have heval : IsIso (evaluationMap D) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact evaluationMap_bijective_of_faithfullyFlat hAB D
  have he : IsIso e :=
    @Comonad.coalgebra_iso_of_iso _ _ (descentComonad A B) _ _ e heval
  let eIso : (descentComparison A B).obj (invariantModuleCat D) ≅ D :=
    { hom := e
      inv := Classical.choose he.out
      hom_inv_id := (Classical.choose_spec he.out).1
      inv_hom_id := (Classical.choose_spec he.out).2 }
  exact ⟨eIso, rfl⟩

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
