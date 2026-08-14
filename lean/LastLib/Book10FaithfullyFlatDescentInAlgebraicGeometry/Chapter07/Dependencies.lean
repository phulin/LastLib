import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

universe u

/-- The three conditions in the fpqc hypothesis used in §7.3. -/
structure Chapter07FpqcMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop where
  surjective : Surjective p
  flat : Flat p
  quasiCompact : QuasiCompact p

theorem chapter07_fpqc_morphism_iff {T S : Scheme.{u}} (p : T ⟶ S) :
    Chapter07FpqcMorphism p ↔ Surjective p ∧ Flat p ∧ QuasiCompact p := by
  constructor
  · intro h
    exact ⟨h.surjective, h.flat, h.quasiCompact⟩
  · rintro ⟨hs, hf, hqc⟩
    exact ⟨hs, hf, hqc⟩

theorem chapter07_fpqc_morphism_stable_under_base_change
    {T S X : Scheme.{u}} (p : T ⟶ S) (g : X ⟶ S)
    (hp : Chapter07FpqcMorphism p) :
    Chapter07FpqcMorphism (pullback.fst p g) := by
  sorry

/-- On an affine scheme, finite locally free is recorded by finite and flat module data.

This is the affine-module formulation used by the finite descent statements below; the
constant-rank refinement is kept separate because it is a fiberwise condition. -/
def Chapter07FiniteLocallyFreeModule (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] : Prop :=
  Module.Finite A M ∧ Module.Flat A M

theorem chapter07_finite_locally_free_module_iff (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] :
    Chapter07FiniteLocallyFreeModule A M ↔ Module.Finite A M ∧ Module.Flat A M := by
  rfl

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
