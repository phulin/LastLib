import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05.Dependencies

/-!
# 5.1 The invariant module

The coalgebra presentation is Mathlib's canonical normalization of a Čech descent datum.  The
explicit overlap modules and the invariant submodule below keep the elementwise formulation from
the source visible as well.
-/

open CategoryTheory
open TensorProduct
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05

noncomputable section

section CanonicalCechMaps

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The canonical map `N → B ⊗[A] N`, `n ↦ 1 ⊗ n`, viewed as an `A`-linear map after restriction
of scalars. -/
def canonicalCechMap (N : ModuleCat B) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj N ⟶
      (ModuleCat.restrictScalars (algebraMap A B)).obj ((descentComonad A B).obj N) := by
  exact (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).unit.app
    ((ModuleCat.restrictScalars (algebraMap A B)).obj N)

@[simp]
theorem canonicalCechMap_apply (N : ModuleCat B) (n : N) :
    canonicalCechMap (A := A) (B := B) N n =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).unit.app
        ((ModuleCat.restrictScalars (algebraMap A B)).obj N)) n := by
  rfl

theorem canonicalCechMap_apply_eq_one_tmul (N : ModuleCat B)
    (n : (ModuleCat.restrictScalars (algebraMap A B)).obj N) :
    canonicalCechMap (A := A) (B := B) N n =
      (1 : B) ⊗ₜ[A, algebraMap A B] n := by
  rfl

end CanonicalCechMaps

section Invariant

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The equalizer of the coaction and `n ↦ 1 ⊗ n`.  This is the source's
`{n ∈ N | θ(n ⊗ 1) = 1 ⊗ n}` written in the normalized comonad presentation. -/
def invariantModule (D : DescentDatum A B) :
    Submodule A ((ModuleCat.restrictScalars (algebraMap A B)).obj D.A) :=
  LinearMap.eqLocus
    ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom
    (canonicalCechMap (A := A) (B := B) D.A).hom

theorem mem_invariantModule_iff (D : DescentDatum A B)
    (n : (ModuleCat.restrictScalars (algebraMap A B)).obj D.A) :
    n ∈ invariantModule D ↔
      ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom n =
        canonicalCechMap (A := A) (B := B) D.A n := by
  rfl

theorem mem_invariantModule_iff_one_tmul (D : DescentDatum A B)
    (n : (ModuleCat.restrictScalars (algebraMap A B)).obj D.A) :
    n ∈ invariantModule D ↔
      ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom n =
        (1 : B) ⊗ₜ[A, algebraMap A B] n := by
  rw [mem_invariantModule_iff, canonicalCechMap_apply_eq_one_tmul]

theorem invariantModule_isSubmodule (D : DescentDatum A B) :
    invariantModule D =
      LinearMap.eqLocus
        ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom
        (canonicalCechMap (A := A) (B := B) D.A).hom := by
  rfl

abbrev invariantModuleCat (D : DescentDatum A B) : ModuleCat A :=
  ModuleCat.of A (invariantModule D)

/-- The scalar extension of the invariant module, before applying the evaluation map. -/
noncomputable def invariantExtension (D : DescentDatum A B) : ModuleCat B :=
  (ModuleCat.extendScalars (algebraMap A B)).obj (invariantModuleCat D)

/-- The canonical evaluation map `B ⊗[A] M → N`, induced by the inclusion of invariants. -/
noncomputable def evaluationMap (D : DescentDatum A B) :
    invariantExtension D ⟶ D.A :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).homEquiv _ _).symm
    (ModuleCat.ofHom (X := invariantModuleCat D)
      (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj D.A) (invariantModule D).subtype)

@[simp]
theorem evaluationMap_apply_one_tmul (D : DescentDatum A B)
    (m : invariantModule D) :
    evaluationMap D ((1 : B) ⊗ₜ[A, algebraMap A B] m) =
      (m.1 : D.A) := by
  change (1 : B) • (m.1 : D.A) = _
  simp

theorem evaluationMap_apply_tmul (D : DescentDatum A B) (b : B)
    (m : invariantModule D) :
    evaluationMap D (b ⊗ₜ[A, algebraMap A B] m) =
      b • (m.1 : D.A) := by
  change b • (m.1 : D.A) = _
  rfl

theorem evaluationMap_is_B_linear (D : DescentDatum A B) :
    ∀ (b : B) (x : invariantExtension D),
      evaluationMap D (b • x) = b • evaluationMap D x := by
  intro b x
  exact (evaluationMap D).hom.map_smul b x

end Invariant

section ExplicitOverlapInterface

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

abbrev firstOverlap (N : ModuleCat B) : ModuleCat (CechRing A B) :=
  letI : SMul B (CechRing A B) := (cech_d1 A B).toRingHom.toModule.toSMul
  letI : Module B (CechRing A B) := (cech_d1 A B).toRingHom.toModule
  letI : SMulCommClass B (CechRing A B) (CechRing A B) := by
    constructor
    intro b x y
    simp [RingHom.toModule_smul, mul_assoc, mul_comm]
  letI : Module (CechRing A B) (firstOverlapModule (A := A) (B := B) N) :=
    TensorProduct.leftModule
  ModuleCat.of (CechRing A B) (firstOverlapModule (A := A) (B := B) N)

abbrev secondOverlap (N : ModuleCat B) : ModuleCat (CechRing A B) :=
  letI : SMul B (CechRing A B) := (cech_d0 A B).toRingHom.toModule.toSMul
  letI : Module B (CechRing A B) := (cech_d0 A B).toRingHom.toModule
  letI : SMulCommClass B (CechRing A B) (CechRing A B) := by
    constructor
    intro b x y
    simp [RingHom.toModule_smul, mul_assoc, mul_comm]
  letI : Module (CechRing A B) (secondOverlapModule (A := A) (B := B) N) :=
    TensorProduct.leftModule
  ModuleCat.of (CechRing A B) (secondOverlapModule (A := A) (B := B) N)

/-- The book-facing `θ : N₁ ≃ N₂`.  Its cocycle is represented canonically by the coassociativity
field of the corresponding `Comonad.Coalgebra`; `descentTheta` is the transport interface between
the two presentations. -/
noncomputable def descentTheta (D : DescentDatum A B) :
    firstOverlap (A := A) (B := B) D.A ≅ secondOverlap (A := A) (B := B) D.A := by
  sorry

theorem descentTheta_cocycle (D : DescentDatum A B) :
    D.a ≫ (descentComonad A B).δ.app D.A =
      D.a ≫ (descentComonad A B).map D.a := by
  exact D.coassoc

theorem descentTheta_normalized (D : DescentDatum A B) :
    D.a ≫ (descentComonad A B).ε.app D.A = 𝟙 D.A := by
  exact D.counit

theorem descentTheta_invariant_formula (D : DescentDatum A B)
    (n : (ModuleCat.restrictScalars (algebraMap A B)).obj D.A) :
    n ∈ invariantModule D ↔
      ((ModuleCat.restrictScalars (algebraMap A B)).map D.a).hom n =
        canonicalCechMap (A := A) (B := B) D.A n := by
  exact mem_invariantModule_iff D n

end ExplicitOverlapInterface

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05
