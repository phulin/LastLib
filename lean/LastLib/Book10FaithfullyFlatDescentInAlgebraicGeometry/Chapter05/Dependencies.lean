import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Chapter 5 shared interfaces

The source chapter is algebraic, so the shared layer uses the pinned commutative-ring and
`ModuleCat` APIs directly.  The raw comonad below is the canonical categorical encoding of the
Čech descent datum; faithful flatness is imposed only at the effectivity statements.
-/

open CategoryTheory
open TensorProduct
open scoped TensorProduct

universe u v w

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05

noncomputable section

section ModuleCatMapCompatibility

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The underlying function of extension of scalars is the one-sided tensor map.  The first
factor is written through `restrictScalars` so that its bundled `R`-module instance is exactly the
one used by `ModuleCat.extendScalars`. -/
theorem ModuleCat.extendScalars_map_hom_toFun_eq_lTensor
    {M N : ModuleCat.{w} R} (f : R →+* S) (g : M ⟶ N) :
    ((ModuleCat.extendScalars f).map g).hom.toFun =
      (LinearMap.lTensor
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) g.hom).toFun := by
  rfl

end ModuleCatMapCompatibility

section FaithfullyFlatRestrictedScalar

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The restricted `A`-module structure on `B` is faithfully flat whenever the usual one is. -/
theorem faithfullyFlat_restrictScalars_self [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat A
      (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)) := by
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
  exact Module.FaithfullyFlat.of_linearEquiv (R := A) (M := B) eB

end FaithfullyFlatRestrictedScalar

section CechRing

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

abbrev CechRing : Type u := B ⊗[A] B

abbrev TripleCechRing : Type u := (B ⊗[A] B) ⊗[A] B

/-- The two structural maps of the affine Čech nerve.  The superscripts follow the source:
`d^0` inserts on the right and `d^1` inserts on the left. -/
def cech_d0 : B →ₐ[A] CechRing A B :=
  Algebra.TensorProduct.includeRight

def cech_d1 : B →ₐ[A] CechRing A B :=
  Algebra.TensorProduct.includeLeft

@[simp]
theorem cech_d0_apply (b : B) : cech_d0 A B b = 1 ⊗ₜ[A] b :=
  rfl

@[simp]
theorem cech_d1_apply (b : B) : cech_d1 A B b = b ⊗ₜ[A] 1 :=
  rfl

/-- Multiplication is a retraction of either Čech structural map. -/
def cech_multiplication : CechRing A B →ₐ[A] B :=
  Algebra.TensorProduct.lmul' A

@[simp]
theorem cech_multiplication_d0 :
    (cech_multiplication A B).comp (cech_d0 A B) = AlgHom.id A B := by
  exact Algebra.TensorProduct.lmul'_comp_includeRight (R := A) (S := B)

@[simp]
theorem cech_multiplication_d1 :
    (cech_multiplication A B).comp (cech_d1 A B) = AlgHom.id A B := by
  exact Algebra.TensorProduct.lmul'_comp_includeLeft (R := A) (S := B)

end CechRing

section OverlapModules

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A scalar extension along an explicitly chosen structural map `d : B →ₐ[A] B ⊗[A] B`.

Mathlib presents this as `(B ⊗[A] B) ⊗[B] N`, with the structural map acting on the first
factor.  This is canonically the source convention `N ⊗_{B,d} (B ⊗[A] B)` because the rings are
commutative; keeping the Mathlib orientation makes the induced overlap module and its linear maps
available without ad hoc module instances. -/
noncomputable abbrev overlapModule (d : B →ₐ[A] CechRing A B) (N : Type u)
    [AddCommGroup N] [Module B N] : Type u :=
  letI : Module B (CechRing A B) := d.toRingHom.toModule
  CechRing A B ⊗[B] N

abbrev firstOverlapModule (N : Type u) [AddCommGroup N] [Module B N] : Type u :=
  overlapModule (cech_d1 A B) N

abbrev secondOverlapModule (N : Type u) [AddCommGroup N] [Module B N] : Type u :=
  overlapModule (cech_d0 A B) N

theorem overlapModule_commutes_with_source_order (d : B →ₐ[A] CechRing A B)
    (N : Type u) [AddCommGroup N] [Module B N] :
    letI : Module B (CechRing A B) := d.toRingHom.toModule
    Nonempty (N ⊗[B] CechRing A B ≃ₗ[B] overlapModule d N) := by
  exact ⟨@TensorProduct.comm B _ N (CechRing A B) _ _ _ d.toRingHom.toModule⟩

end OverlapModules

section CanonicalComonad

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The comonad on `B`-modules induced by extension and restriction of scalars along `A → B`.
Its coalgebras are the canonical categorical form of `B`-modules equipped with descent data. -/
noncomputable abbrev descentComonad : Comonad (ModuleCat B) :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad

abbrev DescentDatum : Type _ := (descentComonad A B).Coalgebra

abbrev DescentDatumHom (D E : DescentDatum A B) := D ⟶ E

/-- Constructor for the normalized form of a descent datum. -/
def mkDescentDatum (N : ModuleCat B) (a : N ⟶ (descentComonad A B).obj N)
    (hcounit : a ≫ (descentComonad A B).ε.app N = 𝟙 N)
    (hcoassoc : a ≫ (descentComonad A B).δ.app N = a ≫ (descentComonad A B).map a) :
    DescentDatum A B :=
  { A := N
    a := a
    counit := hcounit
    coassoc := hcoassoc }

@[simp]
theorem mkDescentDatum_a (N : ModuleCat B) (a : N ⟶ (descentComonad A B).obj N)
    (hcounit : a ≫ (descentComonad A B).ε.app N = 𝟙 N)
    (hcoassoc : a ≫ (descentComonad A B).δ.app N = a ≫ (descentComonad A B).map a) :
    (mkDescentDatum A B N a hcounit hcoassoc).a = a :=
  rfl

/-- The canonical comparison functor sends an `A`-module to its scalar extension with its
canonical Čech datum. -/
noncomputable def descentComparison : ModuleCat A ⥤ DescentDatum A B :=
  Comonad.comparison (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))

@[simp]
theorem descentComparison_underlying (M : ModuleCat A) :
    ((descentComparison A B).obj M).A = (ModuleCat.extendScalars (algebraMap A B)).obj M :=
  rfl

/-- Faithfully flatness makes the scalar-extension adjunction comonadic, with no restriction on
the universe used for bundled module objects. -/
theorem faithfullyFlat_comonadic_comparison_is_equivalence
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : RingHom.FaithfullyFlat (algebraMap A B)) :
    (Comonad.comparison
      (ModuleCat.extendRestrictScalarsAdj.{v, u, u} (algebraMap A B))).IsEquivalence := by
  sorry

end CanonicalComonad

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05
