import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set

noncomputable section

/-! ## 8.2 The triangular autocorrelation -/

def chapter08Convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f y * g (x - y)

def chapter08NormalizedAutocorrelation (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  let G := chapter08Convolution h (fun y => h (-y))
  G x / G 0

def chapter08Sinc (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.sin u / u

/-!
The source uses `T > 0` implicitly whenever it writes the interval, divides by `T`, or expands
the tail.  The declarations make that necessary hypothesis explicit.
-/
/- SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§8.2--§8.3):
  “Put ... [-T/2,T/2]” and all formulas containing `1/T` do not state `T > 0` (nor the
  nonnegative truncation index in (8.6)).  The minimal correction is to quantify the formulas
  with `0 < T` and `m : ℕ`, as done below. -/

def chapter08IntervalIndicator (T : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (-T / 2) (T / 2)) (fun _ => 1)

def chapter08TriangularAutocorrelation (T : ℝ) (x : ℝ) : ℝ :=
  max (1 - |x| / T) 0

def chapter08FUnconditionalTriangle (T : ℝ) : ℝ → ℝ :=
  fun x => chapter08TriangularAutocorrelation T x / Real.cosh (x / 2)

def chapter08FGRHTriangle (T : ℝ) : ℝ → ℝ :=
  chapter08TriangularAutocorrelation T

theorem chapter08_normalized_autocorrelation_zero
    {h : ℝ → ℝ}
    (h0 : chapter08Convolution h (fun y => h (-y)) 0 ≠ 0) :
    chapter08NormalizedAutocorrelation h 0 = 1 := by
  sorry

theorem chapter08_sinc_zero :
    chapter08Sinc 0 = 1 := by
  sorry

theorem chapter08_triangular_even {T : ℝ} :
    Chapter08Even (chapter08TriangularAutocorrelation T) := by
  sorry

theorem chapter08_triangular_zero {T : ℝ} (hT : 0 < T) :
    chapter08TriangularAutocorrelation T 0 = 1 := by
  sorry

theorem chapter08_interval_indicator_even {T : ℝ} (hT : 0 < T) :
    Chapter08Even (chapter08IntervalIndicator T) := by
  sorry

theorem chapter08_triangular_is_normalized_autocorrelation
    {T : ℝ} (hT : 0 < T) :
    chapter08TriangularAutocorrelation T =
      chapter08NormalizedAutocorrelation (chapter08IntervalIndicator T) := by
  sorry

/- SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:(8.3)):
  the quotient `sin(Tt/2)/(Tt/2)` is written without specifying its value at `t = 0`.
  The minimal correction is the removable-value convention `sinc 0 = 1`, represented by
  `chapter08Sinc` above. -/
theorem chapter08_triangular_fourier_transform
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    chapter08CosineTransform (chapter08TriangularAutocorrelation T) t =
      T * (chapter08Sinc (T * t / 2)) ^ 2 := by
  sorry

theorem chapter08_triangular_angular_fourier_transform
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    chapter08FourierTransform (chapter08TriangularAutocorrelation T) t =
      (T * (chapter08Sinc (T * t / 2)) ^ 2 : ℂ) := by
  sorry

theorem chapter08_triangular_fourier_nonnegative
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    0 ≤ chapter08CosineTransform (chapter08TriangularAutocorrelation T) t := by
  sorry

theorem chapter08_triangular_nonnegative {T x : ℝ} :
    0 ≤ chapter08TriangularAutocorrelation T x := by
  exact le_max_right _ _

theorem chapter08_triangular_has_compact_support {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (chapter08TriangularAutocorrelation T) := by
  sorry

theorem chapter08_triangular_positive_type {T : ℝ} (hT : 0 < T) :
    Chapter08PositiveType (chapter08TriangularAutocorrelation T) := by
  sorry

theorem chapter08_unconditional_triangle_admissible {T : ℝ} (hT : 0 < T) :
    Chapter08UnconditionallyAdmissible (chapter08FUnconditionalTriangle T) := by
  sorry

theorem chapter08_grh_triangle_admissible {T : ℝ} (hT : 0 < T) :
    Chapter08GRHAdmissible (chapter08FGRHTriangle T) := by
  sorry

theorem chapter08_unconditional_triangle_A {T : ℝ} (hT : 0 < T) :
    chapter08A (chapter08FUnconditionalTriangle T) = T / 2 := by
  sorry

theorem chapter08_grh_triangle_A {T : ℝ} (hT : 0 < T) :
    chapter08A (chapter08FGRHTriangle T) =
      4 / T * (Real.cosh (T / 2) - 1) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
