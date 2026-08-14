import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

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
      (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).map f = α.hom := by sorry

private theorem chapter07_canonical_module_base_change_map
    {A B X Y : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (f : ModuleCat.of A X ⟶ ModuleCat.of A Y) (b : B) (x : X) :
    chapter07CanonicalModuleDescentEquiv A B Y
        (((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).map f).f.hom
          ((chapter07CanonicalModuleDescentEquiv A B X).symm (b ⊗ₜ[A] x))) =
      b ⊗ₜ[A] f.hom x := by sorry

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
        X.comparison (b ⊗ₜ[A] x) = Y.comparison (b ⊗ₜ[A] e x) := by sorry

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
        X.comparison (b ⊗ₜ[A] x) = Y.comparison (b ⊗ₜ[A] e x) := by sorry

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
    ∃ e : X.carrier ≃ₐ[A] Y.carrier,
      ∀ (b : B) (x : X.carrier),
        X.comparison (b ⊗ₜ[A] x) = Y.comparison (b ⊗ₜ[A] e x)

theorem chapter07_algebra_structure_descends
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    Nonempty (Chapter07AlgebraDescentResult D) := by
  sorry

theorem chapter07_algebra_structure_descends_unique_up_to_equivalence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    ∀ X Y : Chapter07AlgebraDescentResult D,
      Nonempty (Chapter07AlgebraDescentEquivalence X Y) := by
  intro X Y
  refine ⟨{ equivalence := ?_ }⟩
  exact chapter07_algebra_equiv_of_comparison_compatibility D hff X Y

theorem chapter07_algebra_structure_descends_equivalence_unique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (_hff : RingHom.FaithfullyFlat (algebraMap A B))
    (X Y : Chapter07AlgebraDescentResult D)
    (e e' : Chapter07AlgebraDescentEquivalence X Y) : e = e' := by sorry

private theorem chapter07_test_counit_iso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    IsIso ((Comonad.ComonadicityInternal.comparisonAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))).counit.app D.moduleDatum).f := by sorry

private theorem chapter07_test_coaction_counit
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C) :
    ∃ φ : C →ₐ[B] B ⊗[A] C,
      ((Algebra.TensorProduct.lift (Algebra.ofId B C) (AlgHom.id A C)
            (fun _ _ => Commute.all _ _)).restrictScalars A).comp
        (φ.restrictScalars A) = AlgHom.id A C := by sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
