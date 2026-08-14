import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05.Section02ProofOfEffectivity
import Mathlib.LinearAlgebra.Complex.Module

/-!
# 5.3 Morphisms and exact sequences

This section records the morphism, subobject, and exact-sequence interfaces used by effective
descent.  The categorical coalgebra condition is kept next to the source's elementwise
compatibility condition, while the concrete module operations remain available for later
applications.
-/

open CategoryTheory
open TensorProduct
open scoped TensorProduct

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05

noncomputable section

section Morphisms

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A `B`-linear map between descent data is compatible precisely when it is a coalgebra map. -/
def compatibleDescentMorphism (D E : DescentDatum A B) (u : D.A ⟶ E.A) : Prop :=
  D.a ≫ (descentComonad A B).map u = u ≫ E.a

theorem descentHom_compatible (D E : DescentDatum A B) (f : D ⟶ E) :
    compatibleDescentMorphism D E f.f :=
  f.h

/-- Construct a morphism of descent data from its underlying compatible `B`-linear map. -/
def mkDescentMorphism (D E : DescentDatum A B) (u : D.A ⟶ E.A)
    (hu : compatibleDescentMorphism D E u) : D ⟶ E :=
  { f := u, h := hu }

@[simp]
theorem mkDescentMorphism_f (D E : DescentDatum A B) (u : D.A ⟶ E.A)
    (hu : compatibleDescentMorphism D E u) : (mkDescentMorphism D E u hu).f = u :=
  rfl

/-- The source's compatible `B`-linear maps between the two canonical scalar extensions. -/
def CompatibleBMap (M M' : ModuleCat A) : Type _ :=
  {u : ((descentComparison A B).obj M).A ⟶ ((descentComparison A B).obj M').A //
    compatibleDescentMorphism ((descentComparison A B).obj M)
      ((descentComparison A B).obj M') u}

noncomputable def canonicalCompatibleBMap (M M' : ModuleCat A) (f : M ⟶ M') :
    CompatibleBMap (A := A) (B := B) M M' :=
  ⟨((descentComparison A B).map f).f, ((descentComparison A B).map f).h⟩

theorem canonicalCompatibleBMap_bijective_of_faithfullyFlat
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (M M' : ModuleCat A) :
    Function.Bijective (canonicalCompatibleBMap (A := A) (B := B) M M') := by
  have hEq : (descentComparison A B).IsEquivalence := faithfullyFlat_module_descent hAB
  constructor
  · intro f g h
    apply hEq.faithful.map_injective
    apply Comonad.Coalgebra.Hom.ext'
    change ((descentComparison A B).map f).f = ((descentComparison A B).map g).f
    simpa [canonicalCompatibleBMap] using congrArg Subtype.val h
  · intro u
    let e : (descentComparison A B).obj M ⟶ (descentComparison A B).obj M' :=
      mkDescentMorphism _ _ u.1 u.2
    obtain ⟨f, hf⟩ := hEq.full.map_surjective e
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change ((descentComparison A B).map f).f = u.1
    simpa [e, mkDescentMorphism] using
      congrArg (fun k : (descentComparison A B).obj M ⟶
        (descentComparison A B).obj M' => k.f) hf

theorem canonicalCompatibleBMap_bijective_of_instance [Module.FaithfullyFlat A B]
    (M M' : ModuleCat A) :
    Function.Bijective (canonicalCompatibleBMap (A := A) (B := B) M M') := by
  apply canonicalCompatibleBMap_bijective_of_faithfullyFlat
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

theorem compatibleBMap_iff_unique_descent
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) (M M' : ModuleCat A)
    (u : CompatibleBMap (A := A) (B := B) M M') :
    ∃! f : M ⟶ M', canonicalCompatibleBMap (A := A) (B := B) M M' f = u := by
  let hbij := canonicalCompatibleBMap_bijective_of_faithfullyFlat hAB M M'
  obtain ⟨f, hf⟩ := hbij.2 u
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact hbij.1 (hg.trans hf.symm)

end Morphisms

section ConcreteModuleOperations

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

variable {D E : DescentDatum A B}

/-- The underlying kernel module of a morphism of descent data. -/
def kernelModule (f : D ⟶ E) : ModuleCat B :=
  ModuleCat.of B (LinearMap.ker f.f.hom)

def kernelInclusion (f : D ⟶ E) : kernelModule f ⟶ D.A :=
  ModuleCat.ofHom (LinearMap.ker f.f.hom).subtype

@[simp]
theorem kernelInclusion_hom (f : D ⟶ E) :
    (kernelInclusion f).hom = (LinearMap.ker f.f.hom).subtype :=
  rfl

/-- The underlying cokernel module of a morphism of descent data. -/
def cokernelModule (f : D ⟶ E) : ModuleCat B :=
  ModuleCat.of B (E.A ⧸ LinearMap.range f.f.hom)

def cokernelProjection (f : D ⟶ E) : E.A ⟶ cokernelModule f :=
  ModuleCat.ofHom (Submodule.mkQ (LinearMap.range f.f.hom))

@[simp]
theorem cokernelProjection_hom (f : D ⟶ E) :
    (cokernelProjection f).hom = Submodule.mkQ (LinearMap.range f.f.hom) :=
  rfl

/-- The concrete image module, viewed as a submodule of the target. -/
def imageModule (f : D ⟶ E) : ModuleCat B :=
  ModuleCat.of B (LinearMap.range f.f.hom)

def imageInclusion (f : D ⟶ E) : imageModule f ⟶ E.A :=
  ModuleCat.ofHom (LinearMap.range f.f.hom).subtype

@[simp]
theorem imageInclusion_hom (f : D ⟶ E) :
    (imageInclusion f).hom = (LinearMap.range f.f.hom).subtype :=
  rfl

theorem kernel_inherits_descent_data [Module.FaithfullyFlat A B] (f : D ⟶ E) :
    ∃ K : DescentDatum A B, Nonempty (K.A ≅ kernelModule f) := by
  sorry

theorem kernel_inherits_descent_data_with_inclusion [Module.FaithfullyFlat A B]
    (f : D ⟶ E) :
    ∃ (K : DescentDatum A B) (e : K.A ≅ kernelModule f) (i : K ⟶ D),
      e.hom ≫ kernelInclusion f = i.f := by
  sorry

theorem cokernel_inherits_descent_data [Module.FaithfullyFlat A B] (f : D ⟶ E) :
    ∃ Q : DescentDatum A B, Nonempty (Q.A ≅ cokernelModule f) := by
  sorry

theorem cokernel_inherits_descent_data_with_projection [Module.FaithfullyFlat A B]
    (f : D ⟶ E) :
    ∃ (Q : DescentDatum A B) (e : Q.A ≅ cokernelModule f) (q : E ⟶ Q),
      q.f ≫ e.hom = cokernelProjection f := by
  sorry

theorem image_inherits_descent_data [Module.FaithfullyFlat A B] (f : D ⟶ E) :
    ∃ I : DescentDatum A B, Nonempty (I.A ≅ imageModule f) := by
  sorry

theorem image_inherits_descent_data_with_inclusion [Module.FaithfullyFlat A B]
    (f : D ⟶ E) :
    ∃ (I : DescentDatum A B) (e : I.A ≅ imageModule f) (i : I ⟶ E),
      e.hom ≫ imageInclusion f = i.f := by
  sorry

/-- A finite direct sum of the underlying modules of a family of descent data. -/
def finiteDirectSumModule (ι : Type u) [Fintype ι] (D : ι → DescentDatum A B) : ModuleCat B :=
  ModuleCat.of B (∀ i, (D i).A)

theorem finiteDirectSum_inherits_descent_data [Module.FaithfullyFlat A B]
    (ι : Type u) [Fintype ι] (D : ι → DescentDatum A B) :
    ∃ S : DescentDatum A B,
      Nonempty (S.A ≅ finiteDirectSumModule (A := A) (B := B) ι D) := by
  sorry

/-- Tensor product of two underlying `B`-modules. -/
def tensorModule (D E : DescentDatum A B) : ModuleCat B :=
  ModuleCat.of B ((D.A : Type u) ⊗[B] (E.A : Type u))

theorem tensor_inherits_descent_data [Module.FaithfullyFlat A B]
    (D E : DescentDatum A B) :
    ∃ T : DescentDatum A B, Nonempty (T.A ≅ tensorModule D E) := by
  sorry

/-- The `n`th symmetric tensor power of a descended module. -/
def symmetricPowerModule (D : DescentDatum A B) (n : ℕ) : ModuleCat B :=
  ModuleCat.of B (SymmetricPower B (ULift (Fin n)) (D.A : Type u))

theorem symmetricPower_inherits_descent_data [Module.FaithfullyFlat A B]
    (D : DescentDatum A B) (n : ℕ) :
    ∃ S : DescentDatum A B,
      Nonempty (S.A ≅ symmetricPowerModule D n) := by
  sorry

/-- The `n`th exterior power of a descended module. -/
def exteriorPowerModule (D : DescentDatum A B) (n : ℕ) : ModuleCat B :=
  D.A.exteriorPower n

theorem exteriorPower_inherits_descent_data [Module.FaithfullyFlat A B]
    (D : DescentDatum A B) (n : ℕ) :
    ∃ E' : DescentDatum A B,
      Nonempty (E'.A ≅ exteriorPowerModule D n) := by
  sorry

/-- The module dual, with the usual finiteness/projectivity side conditions supplied when it is
used as a descended dual. -/
def dualModule (D : DescentDatum A B) : ModuleCat B :=
  ModuleCat.of B (Module.Dual B (D.A : Type u))

theorem dual_inherits_descent_data [Module.FaithfullyFlat A B]
    (D : DescentDatum A B) [Module.Finite B (D.A : Type u)]
    [Module.Projective B (D.A : Type u)] :
    ∃ Ddual : DescentDatum A B, Nonempty (Ddual.A ≅ dualModule D) := by
  sorry

end ConcreteModuleOperations

section Exactness

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

theorem exactness_reflected_by_faithfullyFlat [Module.FaithfullyFlat A B]
    {M₁ M₂ M₃ : ModuleCat A} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) :
    Function.Exact
        ((ModuleCat.extendScalars (algebraMap A B)).map f).hom
        ((ModuleCat.extendScalars (algebraMap A B)).map g).hom ↔
      Function.Exact f.hom g.hom := by
  sorry

theorem injective_reflected_by_faithfullyFlat [Module.FaithfullyFlat A B]
    {M₁ M₂ : ModuleCat A} (f : M₁ ⟶ M₂) :
      Function.Injective (((ModuleCat.extendScalars (algebraMap A B)).map f).hom) ↔
      Function.Injective f.hom := by
  sorry

theorem surjective_reflected_by_faithfullyFlat [Module.FaithfullyFlat A B]
    {M₁ M₂ : ModuleCat A} (f : M₁ ⟶ M₂) :
    Function.Surjective (((ModuleCat.extendScalars (algebraMap A B)).map f).hom) ↔
      Function.Surjective f.hom := by
  sorry

/-- A compatible short exact sequence remembers descent data on every term and on both maps. -/
structure CompatibleShortExact where
  X₁ : DescentDatum A B
  X₂ : DescentDatum A B
  X₃ : DescentDatum A B
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  exact : Function.Exact f.f g.f
  injective_f : Function.Injective f.f
  surjective_g : Function.Surjective g.f

def compatibleShortComplex (S : CompatibleShortExact (A := A) (B := B)) :
    ShortComplex (ModuleCat B) :=
  ShortComplex.moduleCatMkOfKerLERange S.f.f S.g.f
    (LinearMap.range_le_ker_iff.mpr S.exact.linearMap_comp_eq_zero)

theorem compatibleShortComplex_exact (S : CompatibleShortExact (A := A) (B := B)) :
    (compatibleShortComplex S).Exact := by
  exact ModuleCat.shortComplex_exact (compatibleShortComplex S) S.exact

theorem compatibleShortComplex_shortExact (S : CompatibleShortExact (A := A) (B := B)) :
    (compatibleShortComplex S).ShortExact := by
  exact ModuleCat.shortComplex_shortExact (compatibleShortComplex S) S.exact S.injective_f
    S.surjective_g

/-- A base short exact sequence together with the comparison isomorphisms to a compatible one.
This type keeps the datum on the middle module distinct from the datum on the whole sequence. -/
structure DescendedShortExact (S : CompatibleShortExact (A := A) (B := B)) where
  base : ShortComplex (ModuleCat A)
  exact : base.ShortExact
  e₁ : (descentComparison A B).obj base.X₁ ≅ S.X₁
  e₂ : (descentComparison A B).obj base.X₂ ≅ S.X₂
  e₃ : (descentComparison A B).obj base.X₃ ≅ S.X₃
  f_comm : (descentComparison A B).map base.f ≫ e₂.hom = e₁.hom ≫ S.f
  g_comm : (descentComparison A B).map base.g ≫ e₃.hom = e₂.hom ≫ S.g

theorem compatibleShortExact_descends [Module.FaithfullyFlat A B]
    (S : CompatibleShortExact (A := A) (B := B)) :
    Nonempty (DescendedShortExact S) := by
  sorry

theorem compatibleShortExact_descends_unique_up_to_isomorphism
    [Module.FaithfullyFlat A B] (S : CompatibleShortExact (A := A) (B := B))
    (T T' : DescendedShortExact S) :
    ∃ (e₁ : T.base.X₁ ≅ T'.base.X₁) (e₂ : T.base.X₂ ≅ T'.base.X₂)
      (e₃ : T.base.X₃ ≅ T'.base.X₃),
      e₁.hom ≫ T'.base.f = T.base.f ≫ e₂.hom ∧
      e₂.hom ≫ T'.base.g = T.base.g ≫ e₃.hom := by
  sorry

end Exactness

section Submodules

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The inclusion of the first Čech pullback of a submodule into the first Čech pullback
of the ambient descent datum. -/
noncomputable def firstOverlapInclusion (D : DescentDatum A B) (P : Submodule B D.A) :
    firstOverlap (A := A) (B := B) (ModuleCat.of B P) ⟶
      firstOverlap (A := A) (B := B) D.A := by
  letI : SMul B (CechRing A B) := (cech_d1 A B).toRingHom.toModule.toSMul
  letI : Module B (CechRing A B) := (cech_d1 A B).toRingHom.toModule
  letI : Algebra B (CechRing A B) := (cech_d1 A B).toRingHom.toAlgebra
  letI : SMulCommClass B (CechRing A B) (CechRing A B) := by
    constructor
    intro b x y
    simp [RingHom.toModule_smul, mul_assoc, mul_comm]
  exact ModuleCat.ofHom
    (TensorProduct.AlgebraTensorModule.map
      (LinearMap.id : CechRing A B →ₗ[CechRing A B] CechRing A B) P.subtype)

/-- The analogous inclusion for the second Čech pullback. -/
noncomputable def secondOverlapInclusion (D : DescentDatum A B) (P : Submodule B D.A) :
    secondOverlap (A := A) (B := B) (ModuleCat.of B P) ⟶
      secondOverlap (A := A) (B := B) D.A := by
  letI : SMul B (CechRing A B) := (cech_d0 A B).toRingHom.toModule.toSMul
  letI : Module B (CechRing A B) := (cech_d0 A B).toRingHom.toModule
  letI : Algebra B (CechRing A B) := (cech_d0 A B).toRingHom.toAlgebra
  letI : SMulCommClass B (CechRing A B) (CechRing A B) := by
    constructor
    intro b x y
    simp [RingHom.toModule_smul, mul_assoc, mul_comm]
  exact ModuleCat.ofHom
    (TensorProduct.AlgebraTensorModule.map
      (LinearMap.id : CechRing A B →ₗ[CechRing A B] CechRing A B) P.subtype)

/-- The overlap equality for a `B`-submodule, written in the normalized equalizer presentation. -/
def overlapGluingCondition (D : DescentDatum A B) (P : Submodule B D.A) : Prop :=
  ∃ e : firstOverlap (A := A) (B := B) (ModuleCat.of B P) ≅
      secondOverlap (A := A) (B := B) (ModuleCat.of B P),
    e.hom ≫ secondOverlapInclusion D P =
      firstOverlapInclusion D P ≫ (descentTheta D).hom

/-- A descended submodule includes its descended datum and the inclusion into the ambient datum. -/
def descendedSubmodule (D : DescentDatum A B) (P : Submodule B D.A) : Prop :=
  ∃ (E : DescentDatum A B) (e : E.A ≅ ModuleCat.of B P) (i : E ⟶ D),
    e.hom ≫ ModuleCat.ofHom P.subtype = i.f

theorem descendedSubmodule_iff_overlapGluing [Module.FaithfullyFlat A B]
    (D : DescentDatum A B) (P : Submodule B D.A) :
    descendedSubmodule D P ↔ overlapGluingCondition D P := by
  sorry

section DefinedOverBase

variable {K L M : Type u} [Field K] [Field L] [Algebra K L]
  [AddCommGroup M] [Module K M]

/-- The scalar-extension subspace generated by a base submodule. -/
def baseExtensionSubmodule (P : Submodule K M) : Submodule L (L ⊗[K] M) :=
  Submodule.span L
    (Set.range (TensorProduct.map (LinearMap.id : L →ₗ[K] L) P.subtype))

def DefinedOverBaseSubmodule (P : Submodule L (L ⊗[K] M)) : Prop :=
  ∃ P₀ : Submodule K M, P = baseExtensionSubmodule P₀

theorem arbitrarySubspace_need_not_be_defined_over_base :
    ∃ P : Submodule ℂ (ℂ ⊗[ℝ] ℂ),
      ¬ DefinedOverBaseSubmodule (K := ℝ) (L := ℂ) (M := ℂ) P := by
  sorry

end DefinedOverBase

end Submodules

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05
