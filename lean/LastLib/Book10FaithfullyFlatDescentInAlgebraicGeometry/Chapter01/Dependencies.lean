import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat

/-!
# Chapter 1: Why descent is possible

This file contains only the shared vocabulary used by the four source-order sections.  The
section files deliberately import this interface rather than one another, so that the chapter
does not acquire an accidental dependency on a later section.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01

noncomputable section

/- The affine spectrum map is used both in the double-overlap discussion and in the geometric
   faithful-flatness criterion. -/
def chapter01SpecMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom f)

/- The two canonical scalar views on a tensor-product overlap. -/
abbrev Chapter01TensorProduct (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  B ⊗[A] B

/- The finite-control witness is shared by the geometric-definition and warning sections. -/
structure Chapter01FpqcFamilyRefinement {T S : Scheme.{u}} (p : T ⟶ S) where
  index : Type u
  source : index → Scheme.{u}
  lift : ∀ i, source i ⟶ T
  map : ∀ i, source i ⟶ S
  factor : ∀ i, lift i ≫ p = map i
  flat : ∀ i, Flat (map i)
  finite_reduction :
    ∀ (U : S.Opens), IsQuasiCompact (U : Set S) →
      ∃ (J : Finset index) (V : ∀ i : J, (source i).Opens),
        (∀ i : J, IsQuasiCompact (V i : Set (source i))) ∧
          (∀ x : U, ∃ i : J, ∃ y : V i, (map i y : S) = x.1)

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
