import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct
open scoped ChangeOfRings

universe u

/-- The module-descent object attached to extension and restriction of scalars.

This is the canonical comonadic packaging of a module descent datum.  It is used here instead
of duplicating the two overlap maps and their cocycle in every algebraic structure. -/
abbrev Chapter07ModuleDescentDatum (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad).Coalgebra

abbrev Chapter07ModuleBaseChange (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] :=
  ((ModuleCat.extendScalars (algebraMap A B)).obj
    ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B C)) : Type u)

/- The change-of-rings carrier is canonically the usual tensor product. The explicit bridge is
kept as a named interface because the categorical `ModuleCat` tensor carries a restricted module
instance, while the algebraic tensor notation carries the ordinary one. -/
noncomputable def chapter07ModuleBaseChangeEquiv
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Chapter07ModuleBaseChange A B C ≃ₗ[B] B ⊗[A] C := by
  let eBAdd : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)
      ≃+ B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let eB : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)
      ≃ₗ[A] B :=
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)).isModule) _ eBAdd
      (fun a x => by
        have hB : ∀ z, eBAdd z = (z : B) := by intro z; rfl
        rw [hB, hB, ModuleCat.restrictScalars.smul_def]
        exact IsScalarTower.algebraMap_smul (R := A) (A := B) (M := B) a (x : B))
  let eCAdd : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B C) : Type u)
      ≃+ C :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let eC : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B C) : Type u)
      ≃ₗ[A] C :=
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B C)).isModule) _ eCAdd
      (fun a x => by
        have hC : ∀ z, eCAdd z = (z : C) := by intro z; rfl
        rw [hC, hC, ModuleCat.restrictScalars.smul_def]
        exact IsScalarTower.algebraMap_smul (R := A) (A := B) (M := C) a (x : C))
  dsimp [Chapter07ModuleBaseChange, ModuleCat.extendScalars,
    ModuleCat.ExtendScalars.obj']
  letI : Module B
      (↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ⊗[A]
        ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B C))) :=
    ((ModuleCat.extendScalars (algebraMap A B)).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B C))).isModule
  let eA := TensorProduct.congr eB eC
  refine LinearEquiv.ofBijective
    { toFun := eA
      map_add' := eA.map_add
      map_smul' := ?_ } ?_
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change eB (b • x) ⊗ₜ[A] eC y = b • (eB x ⊗ₜ[A] eC y)
      change eBAdd (b • x) ⊗ₜ[A] eCAdd y = b • (eBAdd x ⊗ₜ[A] eCAdd y)
      rw [TensorProduct.smul_tmul']
      congr 1
  | add x y hx hy => simp [hx, hy]
  exact eA.bijective

/- The coaction transported across the chosen identification of the underlying module with the
  given algebra.  Keeping this map explicit is what lets the algebra datum below say that the
  module descent coaction is multiplicative, rather than hiding that requirement in an arbitrary
  proposition. -/
noncomputable def chapter07AlgebraDescentCoaction
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07ModuleDescentDatum A B)
    (carrier : D.A ≅ ModuleCat.of B C) : C →ₗ[B] Chapter07ModuleBaseChange A B C := by
  let G := (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad
  exact (G.map carrier.hom).hom.comp (D.a.hom.comp carrier.inv.hom)

theorem chapter07_faithfully_flat_reflects_linear_map_equality
    {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.FaithfullyFlat A B] (f g : M →ₗ[A] N)
    (h : LinearMap.lTensor B f = LinearMap.lTensor B g) : f = g := by
  have hz : f - g = 0 :=
    (Module.FaithfullyFlat.zero_iff_lTensor_zero A B (f - g)).mpr (by
      simpa [LinearMap.lTensor_sub] using sub_eq_zero.mpr h)
  exact sub_eq_zero.mp hz

/- The Amitsur equalizer used by affine descent.  This is the exact sequence/equalizer interface
behind the informal phrase “equality of maps is reflected”. -/
theorem chapter07_amitsur_is_effective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] : Algebra.IsEffective A B := by
  exact Algebra.IsEffective.of_faithfullyFlat A B

theorem chapter07_amitsur_equalizer_is_the_algebra_image
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
      (↑((Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B)).eqLocus
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom) : Set B) =
      Set.range (algebraMap A B) := by
  simpa using (Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (Algebra.IsEffective.of_faithfullyFlat A B))

/-- The maps and equations exposing the already-given `A`-algebra structure on a commutative ring. -/
structure Chapter07AlgebraStructureData (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] where
  mul : R ⊗[A] R →ₗ[A] R
  unit : A →ₗ[A] R
  mul_on_pure : ∀ x y : R, mul (x ⊗ₜ[A] y) = x * y
  unit_on_scalar : ∀ a : A, unit a = algebraMap A R a
  associative : ∀ x y z : R,
    mul (x ⊗ₜ[A] (y * z)) = mul ((x * y) ⊗ₜ[A] z)
  commutative : ∀ x y : R, mul (x ⊗ₜ[A] y) = mul (y ⊗ₜ[A] x)
  left_unit : ∀ x : R, mul (1 ⊗ₜ[A] x) = x
  right_unit : ∀ x : R, mul (x ⊗ₜ[A] 1) = x

/-- The canonical algebra structure data associated to an existing algebra instance. -/
def Chapter07AlgebraStructureData.canonical (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] : Chapter07AlgebraStructureData A R where
  mul := (Algebra.TensorProduct.lmul' A).toLinearMap
  unit := Algebra.linearMap A R
  mul_on_pure := by
    intro x y
    exact Algebra.TensorProduct.lmul'_apply_tmul x y
  unit_on_scalar := by
    intro a
    rfl
  associative := by
    intro x y z
    simp [Algebra.TensorProduct.lmul'_apply_tmul, mul_assoc]
  commutative := by
    intro x y
    simp [Algebra.TensorProduct.lmul'_apply_tmul, mul_comm]
  left_unit := by
    intro x
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
  right_unit := by
    intro x
    simp [Algebra.TensorProduct.lmul'_apply_tmul]

@[ext]
theorem Chapter07AlgebraStructureData.ext {A R : Type u} [CommRing A] [CommRing R]
    [Algebra A R] (x y : Chapter07AlgebraStructureData A R)
    (hmul : x.mul = y.mul) (hunit : x.unit = y.unit) : x = y := by
  cases x
  cases y
  simp_all

/-- An algebra descent datum records an actual coalgebra datum and requires its overlap
coaction to be an algebra homomorphism. In particular, the compatibility field is not an
unconstrained proposition. -/
structure Chapter07AlgebraDescentData (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] where
  moduleDatum : Chapter07ModuleDescentDatum A B
  carrier : moduleDatum.A ≅ ModuleCat.of B C
  algebra_structure : Chapter07AlgebraStructureData B C
  overlap_is_algebra_map :
    ∃ φ : C →ₐ[B] B ⊗[A] C,
      φ.toLinearMap = (chapter07ModuleBaseChangeEquiv A B C).toLinearMap.comp
        (chapter07AlgebraDescentCoaction moduleDatum carrier)

/-- The canonical coalgebra on the scalar extension of an `A`-module. -/
noncomputable def chapter07CanonicalModuleDescentDatum
    (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] : Chapter07ModuleDescentDatum A B :=
  (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).obj
    (ModuleCat.of A R)

noncomputable def chapter07CanonicalModuleDescentEquiv
    (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] :
    (chapter07CanonicalModuleDescentDatum A B R).A ≃ₗ[B] B ⊗[A] R := by
  change ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A R) : Type u) ≃ₗ[B]
    B ⊗[A] R
  let eBAdd : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)
      ≃+ B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl }
  let eB : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)
      ≃ₗ[A] B :=
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)).isModule) _ eBAdd
      (fun a x => by
        have hB : ∀ z, eBAdd z = (z : B) := by intro z; rfl
        rw [hB, hB, ModuleCat.restrictScalars.smul_def]
        exact IsScalarTower.algebraMap_smul (R := A) (A := B) (M := B) a (x : B))
  dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
  letI : Module B
      (↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ⊗[A] R) :=
    ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A R)).isModule
  let eA := TensorProduct.congr eB (LinearEquiv.refl A R)
  refine LinearEquiv.ofBijective
    { toFun := eA
      map_add' := eA.map_add
      map_smul' := ?_ } ?_
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change eB (b • x) ⊗ₜ[A] y = b • (eB x ⊗ₜ[A] y)
      change eBAdd (b • x) ⊗ₜ[A] y = b • (eBAdd x ⊗ₜ[A] y)
      rw [TensorProduct.smul_tmul']
      congr 1
  | add x y hx hy => simp [hx, hy]
  exact eA.bijective

/-- A comparison is compatible only when it is the underlying algebra map of an isomorphism of
the canonical module descent datum with the specified datum. -/
def Chapter07ComparisonCompatible
    {A B C R : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing R]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A R] [IsScalarTower A B C]
  (D : Chapter07AlgebraDescentData A B C)
    (e : B ⊗[A] R ≃ₐ[B] C) : Prop :=
  ∃ α :
      chapter07CanonicalModuleDescentDatum A B R ≅ D.moduleDatum,
    ∀ x : B ⊗[A] R,
      e x = D.carrier.hom.hom (α.hom.f.hom
        ((chapter07CanonicalModuleDescentEquiv A B R).symm x))

/-- A descended algebra, including a comparison compatible with the specified datum. -/
structure Chapter07AlgebraDescentResult
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C) where
  carrier : Type u
  commRing : CommRing carrier
  algebra :
    letI : CommRing carrier := commRing
    Algebra A carrier
  comparison :
    letI : CommRing carrier := commRing
    letI : Algebra A carrier := algebra
    B ⊗[A] carrier ≃ₐ[B] C
  comparison_compatible :
    letI : CommRing carrier := commRing
    letI : Algebra A carrier := algebra
    Chapter07ComparisonCompatible D comparison

private theorem chapter07_module_coalgebra_morphism_preimage
    {A B X Y : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (α : chapter07CanonicalModuleDescentDatum A B X ≅
      chapter07CanonicalModuleDescentDatum A B Y) :
    ∃ f : ModuleCat.of A X ⟶ ModuleCat.of A Y,
      (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).map f = α.hom := by
  let F := Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))
  let hcom : ComonadicLeftAdjoint (ModuleCat.extendScalars (algebraMap A B)) :=
    comonadicExtendScalars hff
  let heq : F.IsEquivalence := hcom.eqv
  exact ⟨(heq.full.map_surjective α.hom).choose, (heq.full.map_surjective α.hom).choose_spec⟩

private theorem chapter07_canonical_module_base_change_map
    {A B X Y : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (f : ModuleCat.of A X ⟶ ModuleCat.of A Y) (b : B) (x : X) :
      chapter07CanonicalModuleDescentEquiv A B Y
        (((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).map f).f.hom
          ((chapter07CanonicalModuleDescentEquiv A B X).symm (b ⊗ₜ[A] x))) =
      b ⊗ₜ[A] f.hom x := by
  have hx :
      (chapter07CanonicalModuleDescentEquiv A B X).symm (b ⊗ₜ[A] x) =
        (b ⊗ₜ[A] x :
          ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A X) : Type u)) := by
    apply (chapter07CanonicalModuleDescentEquiv A B X).injective
    rw [(chapter07CanonicalModuleDescentEquiv A B X).apply_symm_apply]
    dsimp [chapter07CanonicalModuleDescentEquiv]
    rfl
  rw [hx]
  let b' : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u) := b
  change (chapter07CanonicalModuleDescentEquiv A B Y)
      ((ModuleCat.extendScalars (algebraMap A B)).map f (b' ⊗ₜ[A] x)) =
    b ⊗ₜ[A] f.hom x
  erw [ModuleCat.ExtendScalars.map_tmul]
  have hy :
      (chapter07CanonicalModuleDescentEquiv A B Y).symm (b ⊗ₜ[A] f.hom x) =
        (b ⊗ₜ[A] f.hom x :
      ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A Y) : Type u)) := by
    apply (chapter07CanonicalModuleDescentEquiv A B Y).injective
    rw [(chapter07CanonicalModuleDescentEquiv A B Y).apply_symm_apply]
    dsimp [chapter07CanonicalModuleDescentEquiv]
    rfl
  dsimp [b']
  change (chapter07CanonicalModuleDescentEquiv A B Y)
      ((b ⊗ₜ[A] (ModuleCat.Hom.hom f) x :
        ((ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A Y) : Type u))) =
    b ⊗ₜ[A] (ModuleCat.Hom.hom f) x
  rw [← hy, (chapter07CanonicalModuleDescentEquiv A B Y).apply_symm_apply]

private theorem chapter07_module_equivalence_of_comparison_compatibility
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (X Y : Chapter07AlgebraDescentResult D) :
    letI : CommRing X.carrier := X.commRing
    letI : Algebra A X.carrier := X.algebra
    letI : CommRing Y.carrier := Y.commRing
    letI : Algebra A Y.carrier := Y.algebra
    ∃ e : X.carrier ≃ₗ[A] Y.carrier,
    ∀ (b : B) (x : X.carrier),
        X.comparison (b ⊗ₜ[A] x) = Y.comparison (b ⊗ₜ[A] e x) := by
  letI : CommRing X.carrier := X.commRing
  letI : Algebra A X.carrier := X.algebra
  letI : CommRing Y.carrier := Y.commRing
  letI : Algebra A Y.carrier := Y.algebra
  rcases X.comparison_compatible with ⟨αX, hX⟩
  rcases Y.comparison_compatible with ⟨αY, hY⟩
  let β : chapter07CanonicalModuleDescentDatum A B X.carrier ≅
      chapter07CanonicalModuleDescentDatum A B Y.carrier := αX ≪≫ αY.symm
  rcases chapter07_module_coalgebra_morphism_preimage hff β with ⟨f, hf⟩
  rcases chapter07_module_coalgebra_morphism_preimage hff β.symm with ⟨g, hg⟩
  let F := Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))
  let hcom : ComonadicLeftAdjoint (ModuleCat.extendScalars (algebraMap A B)) :=
    comonadicExtendScalars hff
  let heq : F.IsEquivalence := hcom.eqv
  let hfaith : F.Faithful := heq.faithful
  let ecat : ModuleCat.of A X.carrier ≅ ModuleCat.of A Y.carrier :=
    { hom := f
      inv := g
      hom_inv_id := by
        apply hfaith.map_injective
        rw [F.map_comp, hf, hg, F.map_id]
        change β.hom ≫ β.inv = 𝟙 _
        exact β.hom_inv_id
      inv_hom_id := by
        apply hfaith.map_injective
        rw [F.map_comp, hg, hf, F.map_id]
        change β.inv ≫ β.hom = 𝟙 _
        exact β.inv_hom_id }
  let e : X.carrier ≃ₗ[A] Y.carrier :=
    { toFun := ecat.hom.hom
      invFun := ecat.inv.hom
      left_inv := by
        intro x
        simpa using congrArg (fun k : ModuleCat.of A X.carrier ⟶ ModuleCat.of A X.carrier => k.hom x)
          ecat.hom_inv_id
      right_inv := by
        intro y
        simpa using congrArg (fun k : ModuleCat.of A Y.carrier ⟶ ModuleCat.of A Y.carrier => k.hom y)
          ecat.inv_hom_id
      map_add' := ecat.hom.hom.map_add
      map_smul' := ecat.hom.hom.map_smul }
  have hcoal : (F.map f).f ≫ αY.hom.f = αX.hom.f := by
    rw [hf]
    change (αX.hom.f ≫ αY.inv.f) ≫ αY.hom.f = αX.hom.f
    have h_id : αY.inv.f ≫ αY.hom.f = 𝟙 _ := congrArg (fun k => k.f) αY.inv_hom_id
    simp [Category.assoc, h_id]
  refine ⟨e, ?_⟩
  intro b x
  have hinput :
      (chapter07CanonicalModuleDescentEquiv A B Y.carrier).symm (b ⊗ₜ[A] e x) =
        (F.map f).f.hom
          ((chapter07CanonicalModuleDescentEquiv A B X.carrier).symm (b ⊗ₜ[A] x)) := by
    apply (chapter07CanonicalModuleDescentEquiv A B Y.carrier).injective
    rw [(chapter07CanonicalModuleDescentEquiv A B Y.carrier).apply_symm_apply]
    simpa [F, e, ecat] using (chapter07_canonical_module_base_change_map f b x).symm
  rw [hX, hY, hinput]
  have hz := congrArg
    (fun k => D.carrier.hom.hom (k.hom
      ((chapter07CanonicalModuleDescentEquiv A B X.carrier).symm (b ⊗ₜ[A] x)))) hcoal.symm
  change
    D.carrier.hom.hom
        (αX.hom.f.hom ((chapter07CanonicalModuleDescentEquiv A B X.carrier).symm (b ⊗ₜ[A] x))) =
      D.carrier.hom.hom
        (αY.hom.f.hom
          ((F.map f).f.hom
            ((chapter07CanonicalModuleDescentEquiv A B X.carrier).symm (b ⊗ₜ[A] x)))) at hz
  exact hz

private theorem chapter07_algebra_equiv_of_comparison_compatibility
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (X Y : Chapter07AlgebraDescentResult D) :
    letI : CommRing X.carrier := X.commRing
    letI : Algebra A X.carrier := X.algebra
    letI : CommRing Y.carrier := Y.commRing
    letI : Algebra A Y.carrier := Y.algebra
    ∃ e : X.carrier ≃ₐ[A] Y.carrier,
      ∀ (b : B) (x : X.carrier),
        X.comparison (b ⊗ₜ[A] x) = Y.comparison (b ⊗ₜ[A] e x) := by
  letI : CommRing X.carrier := X.commRing
  letI : Algebra A X.carrier := X.algebra
  letI : CommRing Y.carrier := Y.commRing
  letI : Algebra A Y.carrier := Y.algebra
  letI : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  rcases chapter07_module_equivalence_of_comparison_compatibility D hff X Y with ⟨e, he⟩
  have h_one : e 1 = 1 := by
    have hcomp : Y.comparison (1 ⊗ₜ[A] e 1) = Y.comparison (1 ⊗ₜ[A] (1 : Y.carrier)) := by
      rw [← he 1 1]
      have hXone : X.comparison (1 ⊗ₜ[A] (1 : X.carrier)) = 1 := by
        change X.comparison (1 : B ⊗[A] X.carrier) = 1
        exact map_one X.comparison
      have hYone : Y.comparison (1 ⊗ₜ[A] (1 : Y.carrier)) = 1 := by
        change Y.comparison (1 : B ⊗[A] Y.carrier) = 1
        exact map_one Y.comparison
      rw [hXone, hYone]
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) Y.carrier)
    apply Y.comparison.injective
    simpa using hcomp
  have h_mul : ∀ x y : X.carrier, e (x * y) = e x * e y := by
    intro x y
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) Y.carrier)
    apply Y.comparison.injective
    calc
      Y.comparison (1 ⊗ₜ[A] e (x * y)) = X.comparison (1 ⊗ₜ[A] (x * y)) :=
        (he 1 (x * y)).symm
      _ = X.comparison ((1 ⊗ₜ[A] x) * (1 ⊗ₜ[A] y)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
      _ = X.comparison (1 ⊗ₜ[A] x) * X.comparison (1 ⊗ₜ[A] y) := by
        rw [map_mul]
      _ = Y.comparison (1 ⊗ₜ[A] e x) * Y.comparison (1 ⊗ₜ[A] e y) := by
        rw [he 1 x, he 1 y]
      _ = Y.comparison ((1 ⊗ₜ[A] e x) * (1 ⊗ₜ[A] e y)) := by
        rw [map_mul]
      _ = Y.comparison (1 ⊗ₜ[A] (e x * e y)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
  refine ⟨AlgEquiv.ofLinearEquiv e h_one h_mul, ?_⟩
  simpa using he

structure Chapter07AlgebraDescentEquivalence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {D : Chapter07AlgebraDescentData A B C}
    (X Y : Chapter07AlgebraDescentResult D) where
  equivalence :
    letI : CommRing X.carrier := X.commRing
    letI : Algebra A X.carrier := X.algebra
    letI : CommRing Y.carrier := Y.commRing
    letI : Algebra A Y.carrier := Y.algebra
    X.carrier ≃ₐ[A] Y.carrier
  comparison_commutes :
    letI : CommRing X.carrier := X.commRing
    letI : Algebra A X.carrier := X.algebra
    letI : CommRing Y.carrier := Y.commRing
    letI : Algebra A Y.carrier := Y.algebra
    ∀ (b : B) (x : X.carrier),
      X.comparison (b ⊗ₜ[A] x) = Y.comparison (b ⊗ₜ[A] equivalence x)

theorem chapter07_algebra_structure_descends
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    Nonempty (Chapter07AlgebraDescentResult D) := by
  letI : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  rcases D.overlap_is_algebra_map with ⟨φ, hφ⟩
  let S : Subalgebra A C :=
    { carrier := {x | φ x = 1 ⊗ₜ[A] x}
      add_mem' := by
        intro x y hx hy
        change φ (x + y) = 1 ⊗ₜ[A] (x + y)
        change φ x = 1 ⊗ₜ[A] x at hx
        change φ y = 1 ⊗ₜ[A] y at hy
        rw [map_add, hx, hy, TensorProduct.tmul_add]
      mul_mem' := by
        intro x y hx hy
        change φ (x * y) = 1 ⊗ₜ[A] (x * y)
        change φ x = 1 ⊗ₜ[A] x at hx
        change φ y = 1 ⊗ₜ[A] y at hy
        rw [map_mul, hx, hy, Algebra.TensorProduct.tmul_mul_tmul]
        simp
      algebraMap_mem' := by
        intro a
        change φ (algebraMap A C a) = 1 ⊗ₜ[A] algebraMap A C a
        conv_lhs =>
          rw [IsScalarTower.algebraMap_apply A B C a, φ.commutes]
        rw [← IsScalarTower.algebraMap_apply A B (B ⊗[A] C) a]
        simpa only using
          (Algebra.TensorProduct.algebraMap_apply' (R := A) (A := B) (B := C) a) }
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap A B)
  let R := ModuleCat.restrictScalars (algebraMap A B)
  let F := Comonad.comparison adj
  let hcom : ComonadicLeftAdjoint (ModuleCat.extendScalars (algebraMap A B)) :=
    comonadicExtendScalars hff
  letI : F.IsEquivalence := hcom.eqv
  let compAdj := Comonad.ComonadicityInternal.comparisonAdjunction adj
  let M := (Comonad.ComonadicityInternal.rightAdjointComparison adj).obj D.moduleDatum
  let i : M ⟶ R.obj D.moduleDatum.A :=
    Limits.equalizer.ι (R.map D.moduleDatum.a) (adj.unit.app (R.obj D.moduleDatum.A))
  have hi := Limits.equalizer.condition (R.map D.moduleDatum.a)
    (adj.unit.app (R.obj D.moduleDatum.A))
  let valRhom : S →ₗ[A] (R.obj (ModuleCat.of B C) : Type u) :=
    { toFun := fun x => (x : C)
      map_add' := by intro x y; rfl
      map_smul' := by
        intro a x
        change (↑(a • x) : C) = (algebraMap A B a) • (x : C)
        rw [Subalgebra.coe_smul]
        exact (IsScalarTower.algebraMap_smul (R := A) (A := B) (M := C) a (x : C)).symm }
  let valR : ModuleCat.of A S ⟶ R.obj (ModuleCat.of B C) :=
    ConcreteCategory.ofHom (C := ModuleCat A) valRhom
  let j : ModuleCat.of A S ⟶ R.obj D.moduleDatum.A :=
    valR ≫ R.map D.carrier.inv
  have hj :
      j ≫ R.map D.moduleDatum.a =
        j ≫ adj.unit.app (R.obj D.moduleDatum.A) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change D.moduleDatum.a.hom (D.carrier.inv.hom (s : C)) =
      (adj.unit.app (R.obj D.moduleDatum.A)).hom (D.carrier.inv.hom (s : C))
    let G := adj.toComonad
    have hinj : Function.Injective (G.map D.carrier.hom).hom := by
      exact (ConcreteCategory.bijective_of_isIso _).1
    apply hinj
    apply (chapter07ModuleBaseChangeEquiv A B C).injective
    change chapter07ModuleBaseChangeEquiv A B C
        (chapter07AlgebraDescentCoaction D.moduleDatum D.carrier (s : C)) =
      chapter07ModuleBaseChangeEquiv A B C
        ((G.map D.carrier.hom).hom
          ((adj.unit.app (R.obj D.moduleDatum.A)).hom
            (D.carrier.inv.hom (s : C))))
    have hsφ : chapter07ModuleBaseChangeEquiv A B C
        (chapter07AlgebraDescentCoaction D.moduleDatum D.carrier (s : C)) =
        1 ⊗ₜ[A] (s : C) := by
      have hφs := DFunLike.congr_fun hφ (s : C)
      change φ (s : C) = chapter07ModuleBaseChangeEquiv A B C
        (chapter07AlgebraDescentCoaction D.moduleDatum D.carrier (s : C)) at hφs
      exact hφs.symm.trans s.property
    rw [hsφ]
    have hunit := ModuleCat.extendRestrictScalarsAdj_unit_app_apply
      (algebraMap A B) (R.obj D.moduleDatum.A) (D.carrier.inv.hom (s : C))
    rw [hunit]
    dsimp [G, adj]
    let m : R.obj D.moduleDatum.A := D.carrier.inv.hom (s : C)
    change 1 ⊗ₜ[A] (s : C) =
      chapter07ModuleBaseChangeEquiv A B C
        (((ModuleCat.extendScalars (algebraMap A B)).map
          ((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom)).hom
          ((1 : B) ⊗ₜ[A, algebraMap A B] m))
    have hmap :
        ((ModuleCat.extendScalars (algebraMap A B)).map
          ((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom)).hom
            ((1 : B) ⊗ₜ[A, algebraMap A B] m) =
          (1 : B) ⊗ₜ[A, algebraMap A B]
            (((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom).hom m) := by
      exact ModuleCat.ExtendScalars.map_tmul (algebraMap A B)
        ((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom) (1 : B) m
    rw [hmap]
    let cR : R.obj (ModuleCat.of B C) := (s : C)
    have hm :
        ((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom).hom m =
          cR := by
      change D.carrier.hom.hom (D.carrier.inv.hom (s : C)) = (s : C)
      simpa [cR] using
        congrArg (fun k : ModuleCat.of B C ⟶ ModuleCat.of B C => k.hom (s : C))
          D.carrier.inv_hom_id
    rw [hm]
    have hpure :
        (chapter07ModuleBaseChangeEquiv A B C).symm (1 ⊗ₜ[A] (s : C)) =
          ((1 : B) ⊗ₜ[A, algebraMap A B] cR : Chapter07ModuleBaseChange A B C) := by
      apply (chapter07ModuleBaseChangeEquiv A B C).injective
      rw [(chapter07ModuleBaseChangeEquiv A B C).apply_symm_apply]
      dsimp [chapter07ModuleBaseChangeEquiv, ModuleCat.extendScalars,
        ModuleCat.ExtendScalars.obj']
      rfl
    change 1 ⊗ₜ[A] (s : C) =
      chapter07ModuleBaseChangeEquiv A B C
        ((1 : B) ⊗ₜ[A, algebraMap A B] cR : Chapter07ModuleBaseChange A B C)
    simpa using congrArg (chapter07ModuleBaseChangeEquiv A B C) hpure
  let k : ModuleCat.of A S ⟶ M :=
    Limits.equalizer.lift j hj
  have hk : k ≫ i = j := by
    dsimp [k, i]
    exact Limits.equalizer.lift_ι j hj
  letI : Module A (D.moduleDatum.A : Type u) := (R.obj D.moduleDatum.A).isModule
  let i' : M →ₗ[A] D.moduleDatum.A :=
    { toFun := fun m => i.hom m
      map_add' := by intro m n; exact i.hom.map_add m n
      map_smul' := by intro a m; exact i.hom.map_smul a m }
  let lbase : M →ₗ[A] C :=
    { toFun := fun m => D.carrier.hom.hom (i' m)
      map_add' := by
        intro m n
        rw [map_add, map_add]
      map_smul' := by
        intro a m
        rw [i'.map_smul]
        have ha : a • i' m = (algebraMap A B a) • i' m := by rfl
        rw [ha]
        rw [map_smul]
        exact IsScalarTower.algebraMap_smul (R := A) (A := B) (M := C) a
          (D.carrier.hom.hom (i' m)) }
  have hinv : ∀ m : M, φ (lbase m) = (1 ⊗ₜ[A] lbase m) := by
    intro m
    let c : C := lbase m
    have hφc := DFunLike.congr_fun hφ c
    change φ c = chapter07ModuleBaseChangeEquiv A B C
      (chapter07AlgebraDescentCoaction D.moduleDatum D.carrier c) at hφc
    change φ c = 1 ⊗ₜ[A] c
    rw [hφc]
    have hi_m := congrArg (fun q => q.hom m) hi
    change D.moduleDatum.a.hom (i' m) =
      (adj.unit.app (R.obj D.moduleDatum.A)).hom (i' m) at hi_m
    have hc_inv : D.carrier.inv.hom c = i' m := by
      have hci := congrArg
        (fun q : D.moduleDatum.A ⟶ D.moduleDatum.A => q.hom (i' m))
        D.carrier.hom_inv_id
      simpa [c, lbase] using hci
    have hunit_m := ModuleCat.extendRestrictScalarsAdj_unit_app_apply
      (algebraMap A B) (R.obj D.moduleDatum.A) (i' m)
    rw [hunit_m] at hi_m
    let G := adj.toComonad
    have hcoaction :
        chapter07AlgebraDescentCoaction D.moduleDatum D.carrier c =
          (G.map D.carrier.hom).hom (D.moduleDatum.a.hom (i' m)) := by
      change (G.map D.carrier.hom).hom
          (D.moduleDatum.a.hom (D.carrier.inv.hom c)) =
        (G.map D.carrier.hom).hom (D.moduleDatum.a.hom (i' m))
      rw [hc_inv]
    rw [hcoaction]
    have hiG := congrArg (G.map D.carrier.hom).hom hi_m
    have hmap :
        (G.map D.carrier.hom).hom
            ((1 : B) ⊗ₜ[A, algebraMap A B] (i' m)) =
          (1 : B) ⊗ₜ[A, algebraMap A B]
            (((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom).hom (i' m)) := by
      dsimp [G, adj]
      exact ModuleCat.ExtendScalars.map_tmul (algebraMap A B)
        ((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom) (1 : B) (i' m)
    have hm :
        ((ModuleCat.restrictScalars (algebraMap A B)).map D.carrier.hom).hom (i' m) = c := by
      change D.carrier.hom.hom (i' m) = c
      simpa [c, lbase]
    have hiG' := hiG.trans hmap
    rw [hm] at hiG'
    have hiE := congrArg (chapter07ModuleBaseChangeEquiv A B C) hiG'
    exact hiE
  let lS : M →ₗ[A] S :=
    lbase.codRestrict S.toSubmodule (by
      intro m
      change φ (lbase m) = 1 ⊗ₜ[A] lbase m
      exact hinv m)
  let l : M ⟶ ModuleCat.of A S :=
    ConcreteCategory.ofHom lS
  have hl : l ≫ j = i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change D.carrier.inv.hom (D.carrier.hom.hom (i' m)) = i' m
    exact congrArg
      (fun q : D.moduleDatum.A ⟶ D.moduleDatum.A => q.hom (i' m))
      D.carrier.hom_inv_id
  have hlk : l ≫ k = 𝟙 M := by
    apply (Limits.equalizer.hom_ext
      (f := R.map D.moduleDatum.a)
      (g := adj.unit.app (R.obj D.moduleDatum.A)))
    change (l ≫ k) ≫ i = (𝟙 M) ≫ i
    rw [Category.assoc, hk, hl, Category.id_comp]
  have hkl : k ≫ l = 𝟙 (ModuleCat.of A S) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    have hki := congrArg
      (fun q : ModuleCat.of A S ⟶ R.obj D.moduleDatum.A => q.hom s) hk
    change i' (k.hom s) = D.carrier.inv.hom (s : C) at hki
    have hcar := congrArg
      (fun q : ModuleCat.of B C ⟶ ModuleCat.of B C => q.hom (s : C))
      D.carrier.inv_hom_id
    change D.carrier.hom.hom (i' (k.hom s)) = (s : C)
    rw [hki]
    simpa using hcar
  let kIso : ModuleCat.of A S ≅ M :=
    { hom := k
      inv := l
      hom_inv_id := hkl
      inv_hom_id := hlk }
  let qcat : (F.obj (ModuleCat.of A S)).A ⟶ ModuleCat.of B C :=
    (Comonad.forget adj.toComonad).map (F.map kIso.hom) ≫
      (Comonad.forget adj.toComonad).map (compAdj.counit.app D.moduleDatum) ≫
        D.carrier.hom
  let q : B ⊗[A] S →ₗ[B] C :=
    qcat.hom.comp (chapter07CanonicalModuleDescentEquiv A B S).symm.toLinearMap
  letI : IsIso kIso.hom := Iso.isIso_hom kIso
  letI : IsIso (F.map kIso.hom) := Functor.map_isIso _ _
  letI : IsIso ((Comonad.forget adj.toComonad).map (F.map kIso.hom)) :=
    Functor.map_isIso _ _
  letI : IsIso ((Comonad.forget adj.toComonad).map
      (compAdj.counit.app D.moduleDatum)) := Functor.map_isIso _ _
  letI : IsIso D.carrier.hom := Iso.isIso_hom D.carrier
  letI : IsIso qcat := by
    dsimp [qcat]
    have h23 : IsIso
        ((Comonad.forget adj.toComonad).map (compAdj.counit.app D.moduleDatum) ≫
          D.carrier.hom) :=
      IsIso.comp_isIso'
        (show IsIso ((Comonad.forget adj.toComonad).map
          (compAdj.counit.app D.moduleDatum)) from Functor.map_isIso _ _)
        (show IsIso D.carrier.hom from Iso.isIso_hom D.carrier)
    exact IsIso.comp_isIso'
      (show IsIso ((Comonad.forget adj.toComonad).map (F.map kIso.hom)) from
        Functor.map_isIso _ _)
      h23
  have hq : Function.Bijective q := by
    dsimp [q]
    exact (ConcreteCategory.bijective_of_isIso qcat).comp
      (chapter07CanonicalModuleDescentEquiv A B S).symm.bijective
  have hq_pure : ∀ (b : B) (s : S),
      q (b ⊗ₜ[A] s) = algebraMap B C b * (s : C) := by
    intro b s
    have hs :
        (chapter07CanonicalModuleDescentEquiv A B S).symm (b ⊗ₜ[A] s) =
          (b ⊗ₜ[A] s : (F.obj (ModuleCat.of A S)).A) := by
      apply (chapter07CanonicalModuleDescentEquiv A B S).injective
      rw [(chapter07CanonicalModuleDescentEquiv A B S).apply_symm_apply]
      dsimp [chapter07CanonicalModuleDescentEquiv]
      rfl
    change qcat.hom
        ((chapter07CanonicalModuleDescentEquiv A B S).symm (b ⊗ₜ[A] s)) =
      algebraMap B C b * (s : C)
    rw [hs]
    dsimp [qcat]
    change D.carrier.hom.hom
        ((compAdj.counit.app D.moduleDatum).f.hom
          ((F.map kIso.hom).f.hom (b ⊗ₜ[A] s))) =
      algebraMap B C b * (s : C)
    erw [ModuleCat.ExtendScalars.map_tmul]
    have heq :
        (adj.homEquiv M D.moduleDatum.A)
            ((compAdj.counit.app D.moduleDatum).f) = i := by
      rw [Comonad.ComonadicityInternal.comparisonAdjunction_counit_f_aux]
      exact (adj.homEquiv _ _).apply_symm_apply i
    have heq_m := congrArg
      (fun f : M ⟶ R.obj D.moduleDatum.A => f.hom (kIso.hom s)) heq
    have heq_m' :
        (compAdj.counit.app D.moduleDatum).f.hom
            ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s)) =
          i' (kIso.hom s) := by
      simpa [adj, R, M, compAdj, i',
        ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] using! heq_m
    letI : Module B
        (↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ⊗[A]
          (M : Type u)) :=
      ((ModuleCat.extendScalars (algebraMap A B)).obj M).isModule
    let hsmulM : SMul B ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type u) :=
      inferInstance
    let hsmulD :
        SMul B (((𝟭 adj.toComonad.Coalgebra).obj D.moduleDatum).A : Type u) :=
      inferInstance
    let hsmulC : SMul B C := inferInstance
    have hscale :
        (b ⊗ₜ[A, algebraMap A B] (kIso.hom s) :
          ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type u)) =
          hsmulM.smul b ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s) :
            ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type u)) := by
      change (b ⊗ₜ[A, algebraMap A B] (kIso.hom s)) =
        ((b * 1) ⊗ₜ[A, algebraMap A B] (kIso.hom s))
      simp
    have hcounit :
        (compAdj.counit.app D.moduleDatum).f.hom
            (b ⊗ₜ[A, algebraMap A B] (kIso.hom s)) =
          hsmulD.smul b (i' (kIso.hom s)) := by
      calc
        (compAdj.counit.app D.moduleDatum).f.hom
            (b ⊗ₜ[A, algebraMap A B] (kIso.hom s)) =
            (compAdj.counit.app D.moduleDatum).f.hom
              (hsmulM.smul b ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s) :
                ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type u))) := by
                rw [hscale]
        _ = hsmulD.smul b ((compAdj.counit.app D.moduleDatum).f.hom
              ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s))) := by
                have hmap :=
                  (compAdj.counit.app D.moduleDatum).f.hom.map_smul b
                    ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s))
                change (compAdj.counit.app D.moduleDatum).f.hom
                    (hsmulM.smul b
                      ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s) :
                        ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type u))) =
                  hsmulD.smul b ((compAdj.counit.app D.moduleDatum).f.hom
                    ((1 : B) ⊗ₜ[A, algebraMap A B] (kIso.hom s))) at hmap
                exact hmap
        _ = hsmulD.smul b (i' (kIso.hom s)) := by rw [heq_m']
    have hks : D.carrier.hom.hom (i' (kIso.hom s)) = (s : C) := by
      have hki := congrArg (fun q => q.hom s) hk
      change i' (kIso.hom s) = D.carrier.inv.hom (s : C) at hki
      have hcar := congrArg
        (fun q : ModuleCat.of B C ⟶ ModuleCat.of B C => q.hom (s : C))
        D.carrier.inv_hom_id
      change D.carrier.hom.hom (i' (kIso.hom s)) = (s : C)
      rw [hki]
      simpa using hcar
    calc
      D.carrier.hom.hom
          ((compAdj.counit.app D.moduleDatum).f.hom
            (b ⊗ₜ[A, algebraMap A B] (kIso.hom s))) =
        D.carrier.hom.hom (hsmulD.smul b (i' (kIso.hom s))) := by rw [hcounit]
      _ = hsmulC.smul b (D.carrier.hom.hom (i' (kIso.hom s))) := by
        change D.carrier.hom.hom (b • i' (kIso.hom s)) =
          b • D.carrier.hom.hom (i' (kIso.hom s))
        exact D.carrier.hom.hom.map_smul b (i' (kIso.hom s))
      _ = algebraMap B C b * (s : C) := by
        rw [hks]
        change b • (s : C) = algebraMap B C b * (s : C)
        exact Algebra.smul_def b (s : C)
  let qAlg : B ⊗[A] S →ₐ[B] C :=
    Algebra.TensorProduct.lift (Algebra.ofId B C) S.val
      (fun _ _ => Commute.all _ _)
  have hqAlg_pure : ∀ b : B, ∀ s : S,
      qAlg (b ⊗ₜ[A] s) = algebraMap B C b * (s : C) := by
    intro b s
    rfl
  have hq_eq : qAlg.toLinearMap = q := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b s =>
        change qAlg (b ⊗ₜ[A] s) = q (b ⊗ₜ[A] s)
        rw [hqAlg_pure, hq_pure]
    | add z w hz hw => simp [map_add, hz, hw]
  have hqAlg : Function.Bijective qAlg := by
    constructor
    · intro x y hxy
      apply hq.1
      calc
        q x = qAlg.toLinearMap x := by rw [hq_eq]
        _ = qAlg x := rfl
        _ = qAlg y := hxy
        _ = qAlg.toLinearMap y := rfl
        _ = q y := by rw [hq_eq]
    · intro z
      rcases hq.2 z with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      calc
        qAlg x = qAlg.toLinearMap x := rfl
        _ = q x := by rw [hq_eq]
        _ = z := hx
  let comparisonAlg : B ⊗[A] S ≃ₐ[B] C :=
    AlgEquiv.ofBijective qAlg hqAlg
  letI : IsIso (compAdj.counit.app D.moduleDatum) := by infer_instance
  let α0 : F.obj (ModuleCat.of A S) ≅ D.moduleDatum :=
    (asIso (F.map kIso.hom)) ≪≫ asIso (compAdj.counit.app D.moduleDatum)
  refine ⟨{
    carrier := S
    commRing := inferInstance
    algebra := inferInstance
    comparison := comparisonAlg
    comparison_compatible := ?_ }⟩
  refine ⟨?_, ?_⟩
  · simpa [F, adj, chapter07CanonicalModuleDescentDatum] using! α0
  · intro x
    change comparisonAlg x = q x
    rw [← hq_eq]
    rfl

theorem chapter07_algebra_structure_descends_unique_up_to_equivalence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    ∀ X Y : Chapter07AlgebraDescentResult D,
      Nonempty (Chapter07AlgebraDescentEquivalence X Y) := by
  intro X Y
  rcases chapter07_algebra_equiv_of_comparison_compatibility D hff X Y with ⟨e, he⟩
  exact ⟨{ equivalence := e, comparison_commutes := he }⟩

theorem chapter07_algebra_structure_descends_equivalence_unique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (_hff : RingHom.FaithfullyFlat (algebraMap A B))
    (X Y : Chapter07AlgebraDescentResult D)
    (e e' : Chapter07AlgebraDescentEquivalence X Y) : e = e' := by
  letI : CommRing X.carrier := X.commRing
  letI : Algebra A X.carrier := X.algebra
  letI : CommRing Y.carrier := Y.commRing
  letI : Algebra A Y.carrier := Y.algebra
  letI : Module.FaithfullyFlat A B :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp _hff
  have heq : e.equivalence = e'.equivalence := by
    apply AlgEquiv.ext
    intro x
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) Y.carrier)
    apply Y.comparison.injective
    calc
      Y.comparison (1 ⊗ₜ[A] e.equivalence x) = X.comparison (1 ⊗ₜ[A] x) :=
        (e.comparison_commutes 1 x).symm
      _ = Y.comparison (1 ⊗ₜ[A] e'.equivalence x) :=
        e'.comparison_commutes 1 x
  cases e with
  | mk e he =>
    cases e' with
    | mk e' he' =>
      dsimp at heq
      cases heq
      rfl

private theorem chapter07_test_counit_iso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    IsIso ((Comonad.ComonadicityInternal.comparisonAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).counit.app D.moduleDatum).f := by
  let hcom : ComonadicLeftAdjoint (ModuleCat.extendScalars (algebraMap A B)) :=
    comonadicExtendScalars hff
  letI : (Comonad.comparison
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).IsEquivalence := hcom.eqv
  haveI : IsIso ((Comonad.ComonadicityInternal.comparisonAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).counit.app
      D.moduleDatum) := by infer_instance
  haveI : IsIso ((Comonad.forget
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad).map
      ((Comonad.ComonadicityInternal.comparisonAdjunction
        (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).counit.app D.moduleDatum) ) :=
    Functor.map_isIso _ _
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (ConcreteCategory.hom
    ((Comonad.forget (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad).map
      ((Comonad.ComonadicityInternal.comparisonAdjunction
        (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).counit.app D.moduleDatum)))
  exact ConcreteCategory.bijective_of_isIso _

private theorem chapter07_base_change_counit
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    ∀ z : Chapter07ModuleBaseChange A B C,
      ((Algebra.TensorProduct.lift (Algebra.ofId B C) (AlgHom.id A C)
          (fun _ _ => Commute.all _ _)).restrictScalars A)
          (chapter07ModuleBaseChangeEquiv A B C z) =
      ((ModuleCat.restrictScalars (algebraMap A B)).map
          ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.app
            (ModuleCat.of B C))).hom z := by
  sorry

private theorem chapter07_test_coaction_counit
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C) :
    ∃ φ : C →ₐ[B] B ⊗[A] C,
      ((Algebra.TensorProduct.lift (Algebra.ofId B C) (AlgHom.id A C)
            (fun _ _ => Commute.all _ _)).restrictScalars A).comp
        (φ.restrictScalars A) = AlgHom.id A C := by
  rcases D.overlap_is_algebra_map with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  apply AlgHom.ext
  intro x
  have hx :
      φ x = chapter07ModuleBaseChangeEquiv A B C
        (chapter07AlgebraDescentCoaction D.moduleDatum D.carrier x) := by
    simpa using DFunLike.congr_fun hφ x
  change ((Algebra.TensorProduct.lift (Algebra.ofId B C) (AlgHom.id A C)
      (fun _ _ => Commute.all _ _)).restrictScalars A) (φ x) = x
  rw [hx, chapter07_base_change_counit]
  let G := (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad
  have hcat :
      D.carrier.inv ≫ D.moduleDatum.a ≫ G.map D.carrier.hom ≫
          G.ε.app (ModuleCat.of B C) = 𝟙 (ModuleCat.of B C) := by
    rw [G.counit_naturality]
    rw [← Category.assoc D.moduleDatum.a _ D.carrier.hom]
    rw [D.moduleDatum.counit]
    simpa only [Category.comp_id, Category.id_comp] using D.carrier.inv_hom_id
  change (G.ε.app (ModuleCat.of B C)).hom
      ((G.map D.carrier.hom).hom
        (D.moduleDatum.a.hom (D.carrier.inv.hom x))) = x
  have hcat_hom := congrArg
    (fun k : ModuleCat.of B C ⟶ ModuleCat.of B C => k.hom) hcat
  change (G.ε.app (ModuleCat.of B C)).hom.comp
      ((G.map D.carrier.hom).hom.comp
        (D.moduleDatum.a.hom.comp D.carrier.inv.hom)) = LinearMap.id at hcat_hom
  change ((G.ε.app (ModuleCat.of B C)).hom.comp
      ((G.map D.carrier.hom).hom.comp
        (D.moduleDatum.a.hom.comp D.carrier.inv.hom))) x = x
  rw [hcat_hom]
  simp only [LinearMap.id_apply]

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
