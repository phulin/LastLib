import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Section03GeometricMeaning
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
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

universe u

/-- The fpqc predicate from Chapter 1, reused for the affine descent results. -/
abbrev Chapter07FpqcMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Chapter01FpqcMorphism p

theorem chapter07_fpqc_morphism_iff {T S : Scheme.{u}} (p : T ⟶ S) :
    Chapter07FpqcMorphism p ↔ Surjective p ∧ Flat p ∧ QuasiCompact p := by
  constructor
  · intro h
    exact ⟨h.1.2, h.1.1, h.2⟩
  · rintro ⟨hs, hf, hqc⟩
    exact ⟨⟨hf, hs⟩, hqc⟩

theorem chapter07_fpqc_morphism_stable_under_base_change
    {T S X : Scheme.{u}} (p : T ⟶ S) (g : X ⟶ S)
    (hp : Chapter07FpqcMorphism p) :
    Chapter07FpqcMorphism (pullback.snd p g) := by
  rw [chapter07_fpqc_morphism_iff] at hp ⊢
  let _ : Surjective p := hp.1
  let _ : Flat p := hp.2.1
  let _ : QuasiCompact p := hp.2.2
  exact ⟨by infer_instance, by infer_instance, by infer_instance⟩

/-- On an affine scheme, finite locally free is recorded by finite-presentation and flat module data.

This is the affine-module formulation used by the finite descent statements below; the
constant-rank refinement is kept separate because it is a fiberwise condition. -/
def Chapter07FiniteLocallyFreeModule (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] : Prop :=
  Module.FinitePresentation A M ∧ Module.Flat A M

theorem chapter07_finite_locally_free_module_iff (A M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] :
    Chapter07FiniteLocallyFreeModule A M ↔
      Module.FinitePresentation A M ∧ Module.Flat A M := by
  rfl

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
