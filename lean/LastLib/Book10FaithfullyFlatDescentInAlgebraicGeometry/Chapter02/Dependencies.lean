import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Basic

/-!
Shared imports for Chapter 2.  The chapter deliberately keeps its covering-family interface
separate from Mathlib's single-morphism properties: an fpqc family is allowed to have infinitely
many members, whereas `QuasiCompact` is a property of one morphism.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v w

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
