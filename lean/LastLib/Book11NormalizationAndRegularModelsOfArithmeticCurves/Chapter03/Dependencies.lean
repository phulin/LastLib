import Mathlib.Algebra.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section01FromOneLocalRingToSeveral
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section02DimensionOneAsAMeetingPoint

/-!
# Book 11, Chapter 3: shared imports

The source-order declarations live in `Core.lean`.  The Chapter 1 and 2 files of Book 11 are not
present in this drafting workspace, so the normalization boundary used there is recorded locally
in the core file and can be replaced by the earlier chapter's canonical construction in fixup.
-/

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
open scoped AlgebraicGeometry BigOperators TensorProduct

noncomputable section

universe u v

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
