import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section03ExactEvaluationOfTheArchimedeanTerms
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Section01UniversalOdlyzkoPoitouInequalities
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section05TotallyRealCertificates

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open Filter
open MeasureTheory
open NumberField
open scoped BigOperators

/-!
Shared interfaces for the reusable theorem package.

The source chapter is a synthesis chapter.  These names retain its notation
while reducing degree, signature, root discriminant, test functions, and the
three archimedean integrals to the focused interfaces from Chapters 8 and 9.
-/

abbrev Chapter15TestFunction := ℝ → ℝ

abbrev chapter15Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Chapter08Degree K

abbrev chapter15RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Chapter08RootDiscriminant K

abbrev chapter15RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  Chapter08RealPlaceCount K

abbrev chapter15ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  Chapter08ComplexPlaceCount K

def chapter15RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter08SignatureProportion K

abbrev chapter15EulerMascheroni : ℝ := Real.eulerMascheroniConstant

def chapter15FT (T : ℝ) : Chapter15TestFunction :=
  fun x => max (1 - |x| / T) 0 / Real.cosh (x / 2)

def chapter15GT (T : ℝ) : Chapter15TestFunction :=
  fun x => max (1 - |x| / T) 0

def chapter15A (F : Chapter15TestFunction) : ℝ :=
  chapter08A F

def chapter15B (F : Chapter15TestFunction) : ℝ :=
  chapter08B F

def chapter15C (F : Chapter15TestFunction) : ℝ :=
  chapter08C F

def chapter15BT (T : ℝ) : ℝ :=
  chapter15B (chapter15FT T)

def chapter15CT (T : ℝ) : ℝ :=
  chapter15C (chapter15FT T)

def chapter15GRHBT (T : ℝ) : ℝ :=
  chapter15B (chapter15GT T)

def chapter15GRHCT (T : ℝ) : ℝ :=
  chapter15C (chapter15GT T)

def chapter15LogLowerBound
    (F : Chapter15TestFunction) (n : ℕ) (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
    4 * chapter15A F / (n : ℝ) - chapter15B F - α * chapter15C F

def chapter15GRHPoleCost (n : ℕ) (T : ℝ) : ℝ :=
  4 * chapter15A (chapter15GT T) / (n : ℝ)

abbrev chapter15GRHFor
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] : Prop :=
  chapter09GRH K

theorem chapter15_degree_pos
    (K : Type*) [Field K] [NumberField K] : 0 < chapter15Degree K := by
  exact Module.finrank_pos

theorem chapter15_rootDiscriminant_pos
    (K : Type*) [Field K] [NumberField K] : 0 < chapter15RootDiscriminant K := by
  sorry

theorem chapter15_realProportion_nonneg
    (K : Type*) [Field K] [NumberField K] : 0 ≤ chapter15RealProportion K := by
  sorry

theorem chapter15_realProportion_le_one
    (K : Type*) [Field K] [NumberField K] : chapter15RealProportion K ≤ 1 := by
  sorry

@[simp]
theorem chapter15_rootDiscriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter15RootDiscriminant K = NumberField.rootDiscr K :=
  rfl

theorem chapter15_degree_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter15Degree K = chapter09Degree K :=
  rfl

theorem chapter15_realProportion_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter15RealProportion K = chapter09RealProportion K := by
  rfl

theorem chapter15_FT_eq_chapter09
    (T : ℝ) : chapter15FT T = chapter09UnconditionalTestFunction T := by
  rfl

theorem chapter15_GT_eq_chapter09
    (T : ℝ) : chapter15GT T = chapter09GRHTestFunction T := by
  rfl

theorem chapter15_A_eq_chapter09
    (F : Chapter15TestFunction) : chapter15A F = chapter09A F := by
  rfl

theorem chapter15_B_eq_chapter09
    (F : Chapter15TestFunction) : chapter15B F = chapter09B F := by
  rfl

theorem chapter15_C_eq_chapter09
    (F : Chapter15TestFunction) : chapter15C F = chapter09C F := by
  rfl

theorem chapter15_BT_eq_chapter09
    (T : ℝ) : chapter15BT T = chapter09BT T := by
  rfl

theorem chapter15_CT_eq_chapter09
    (T : ℝ) : chapter15CT T = chapter09CT T := by
  rfl

theorem chapter15_GRHBT_eq_chapter09
    (T : ℝ) : chapter15GRHBT T = chapter09GRHBT T := by
  rfl

theorem chapter15_GRHCT_eq_chapter09
    (T : ℝ) : chapter15GRHCT T = chapter09GRHCT T := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: the Chapter 9 wrapper for the root discriminant
is the same canonical number-field quantity used by Chapters 8 and 11. -/
theorem chapter15_rootDiscriminant_eq_chapter09
    (K : Type*) [Field K] [NumberField K] :
    chapter15RootDiscriminant K = chapter09RootDiscriminant K := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter15
