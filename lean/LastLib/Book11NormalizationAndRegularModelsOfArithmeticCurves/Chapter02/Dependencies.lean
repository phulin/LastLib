import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

noncomputable section

/-!
Shared interfaces for Chapter 2.  The ring-level constructions below use the
canonical `integralClosure` and `IsIntegralClosure` APIs; the scheme-level
normality marker records the stalkwise condition used by the universal
property.
-/

/-- A finite field extension in the convention of this chapter. -/
abbrev Chapter02FiniteFieldExtension (F L : Type u) [Field F] [Field L]
    [Algebra F L] : Prop :=
  FiniteDimensional F L

theorem chapter02_finiteFieldExtension_iff (F L : Type u) [Field F] [Field L]
    [Algebra F L] :
    Chapter02FiniteFieldExtension F L ↔ FiniteDimensional F L :=
  Iff.rfl

/-- Normality for an integral noetherian scheme, stated stalkwise. -/
class Chapter02Normal (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Prop where
  integrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

theorem chapter02_normal_is_reduced (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter02Normal X] : IsReduced X := by
  infer_instance

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
