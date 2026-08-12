import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Interval.Set.Basic

import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section03ExactEvaluationOfTheArchimedeanTerms
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Section01UniversalOdlyzkoPoitouInequalities

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-!
Shared imports for the certified-numerics chapter.

The exact archimedean expressions are taken from Chapter 8, while the fixed-test-function
logarithmic bound and its monotonicity API are taken from Chapter 9.  No numerical theorem is
assumed here: the declarations in the four section files below record the finite certificates.
-/

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
