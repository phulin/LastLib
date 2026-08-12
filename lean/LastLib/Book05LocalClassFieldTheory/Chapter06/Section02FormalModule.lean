import LastLib.Book05LocalClassFieldTheory.Chapter06.Section01WhyASeparateExistenceConstructionIsNecessary

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators

/-!
### 6.2. A formal module attached to a uniformizer
-/

abbrev Chapter06UnivariateSeries (O : Type*) := PowerSeries O
abbrev Chapter06BivariateSeries (O : Type*) := MvPowerSeries (Fin 2) O

/-- The total degree of a bivariate monomial. -/
def chapter06TotalDegree (d : Fin 2 →₀ ℕ) : ℕ :=
  d.sum (fun _ n => n)

/-- The linear series `aX+bY`, used to state linear-part conditions without
identifying coefficients by a noncanonical coordinate convention. -/
def chapter06LinearSeries {O : Type*} [CommRing O] (a b : O) :
    Chapter06BivariateSeries O :=
  a • MvPowerSeries.X (0 : Fin 2) + b • MvPowerSeries.X (1 : Fin 2)

/-- A bivariate series has the displayed linear part. -/
def chapter06HasLinearPart {O : Type*} [CommRing O]
    (H : Chapter06BivariateSeries O) (a b : O) : Prop :=
  ∀ d : Fin 2 →₀ ℕ, chapter06TotalDegree d < 2 →
    MvPowerSeries.coeff d H = MvPowerSeries.coeff d (chapter06LinearSeries a b)

/-- A univariate series has the displayed congruence modulo `T²`. -/
def chapter06HasLinearCoefficient {O : Type*} [CommRing O]
    (h : Chapter06UnivariateSeries O) (a : O) : Prop :=
  ∀ n : ℕ, n < 2 →
    PowerSeries.coeff n h = PowerSeries.coeff n (a • PowerSeries.X)

/-- Congruence of power series modulo an ideal of coefficients. -/
def chapter06CongruentModIdeal {O : Type*} [CommRing O]
    (I : Ideal O) (f g : Chapter06UnivariateSeries O) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n (f - g) ∈ I

/-- The two Lubin--Tate congruences imposed on a series attached to `D`. -/
def chapter06LubinTateCondition
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D)) : Prop :=
  chapter06HasLinearCoefficient f D.uniformizer ∧
    chapter06CongruentModIdeal
      (Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))) f
      (PowerSeries.X ^ chapter06ResidueCardinality D)

/-- The explicit Lubin--Tate series used from Section 6.3 onwards. -/
def chapter06ExplicitLubinTateSeries
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    Chapter06UnivariateSeries (Chapter06ValuationRing D) :=
  PowerSeries.C D.uniformizer * PowerSeries.X +
    PowerSeries.X ^ chapter06ResidueCardinality D

theorem chapter06_explicitLubinTateSeries_satisfies
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    chapter06LubinTateCondition D (chapter06ExplicitLubinTateSeries D) := by
  sorry

/-- Substitute a family of formal series into a multivariate series. -/
noncomputable def chapter06FormalSubstitute
    {O : Type*} [CommRing O] {σ τ : Type*}
    (g : σ → MvPowerSeries τ O) (F : MvPowerSeries σ O) :
    MvPowerSeries τ O :=
  MvPowerSeries.subst g F

/-- The formal group operation obtained by substituting two series into `F`. -/
noncomputable def chapter06FormalGroupOperation
    {O : Type*} [CommRing O]
    (F : Chapter06BivariateSeries O)
    (x y : Chapter06UnivariateSeries O) :
    Chapter06UnivariateSeries O :=
  chapter06FormalSubstitute
    (fun i : Fin 2 => if i = (0 : Fin 2) then x else y) F

/-- Composition of univariate formal series: the first argument is substituted
into the second. -/
noncomputable def chapter06PowerSeriesCompose
    {O : Type*} [CommRing O]
    (g f : Chapter06UnivariateSeries O) :
    Chapter06UnivariateSeries O :=
  PowerSeries.subst g f

/-- The bivariate image of a univariate series in the first coordinate. -/
noncomputable def chapter06BivariateSeriesInFirstCoordinate
    {O : Type*} [CommRing O] (f : Chapter06UnivariateSeries O) :
    Chapter06BivariateSeries O :=
  chapter06FormalSubstitute
    (fun _ : Unit => MvPowerSeries.X (0 : Fin 2)) f

/-- The bivariate image of a univariate series in the second coordinate. -/
noncomputable def chapter06BivariateSeriesInSecondCoordinate
    {O : Type*} [CommRing O] (f : Chapter06UnivariateSeries O) :
    Chapter06BivariateSeries O :=
  chapter06FormalSubstitute
    (fun _ : Unit => MvPowerSeries.X (1 : Fin 2)) f

/-- The equation `H(f(X),f(Y)) = f(H(X,Y))`. -/
def chapter06BivariateIntertwines
    {O : Type*} [CommRing O]
    (f : Chapter06UnivariateSeries O) (H : Chapter06BivariateSeries O) : Prop :=
  chapter06FormalSubstitute
      (fun i : Fin 2 =>
        if i = (0 : Fin 2) then
          chapter06BivariateSeriesInFirstCoordinate f
        else chapter06BivariateSeriesInSecondCoordinate f) H =
    chapter06FormalSubstitute (fun _ : Unit => H) f

/-- A commutative formal group law written in the substitution API. -/
structure Chapter06FormalGroupLaw (O : Type*) [CommRing O] where
  series : Chapter06BivariateSeries O
  linear_part : chapter06HasLinearPart series 1 1
  zero_left :
    ∀ x : Chapter06UnivariateSeries O,
      MvPowerSeries.constantCoeff x = 0 →
        chapter06FormalGroupOperation series 0 x = x
  zero_right :
    ∀ x : Chapter06UnivariateSeries O,
      MvPowerSeries.constantCoeff x = 0 →
        chapter06FormalGroupOperation series x 0 = x
  commutative :
    ∀ x y : Chapter06UnivariateSeries O,
      MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff y = 0 →
        chapter06FormalGroupOperation series x y =
          chapter06FormalGroupOperation series y x
  associative :
    ∀ x y z : Chapter06UnivariateSeries O,
      MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff y = 0 →
      MvPowerSeries.constantCoeff z = 0 →
        chapter06FormalGroupOperation series
            (chapter06FormalGroupOperation series x y) z =
          chapter06FormalGroupOperation series x
            (chapter06FormalGroupOperation series y z)
  inverse : Chapter06UnivariateSeries O
  inverse_const : MvPowerSeries.constantCoeff inverse = 0
  inverse_left : ∀ x : Chapter06UnivariateSeries O,
    MvPowerSeries.constantCoeff x = 0 →
      chapter06FormalGroupOperation series inverse x = 0
  inverse_right : ∀ x : Chapter06UnivariateSeries O,
    MvPowerSeries.constantCoeff x = 0 →
      chapter06FormalGroupOperation series x inverse = 0

/-- The property that a series is an endomorphism of a formal group law. -/
def chapter06IsFormalEndomorphism
    {O : Type*} [CommRing O]
    (F : Chapter06FormalGroupLaw O)
    (h : Chapter06UnivariateSeries O) : Prop :=
  ∀ x y : Chapter06UnivariateSeries O,
    MvPowerSeries.constantCoeff x = 0 →
    MvPowerSeries.constantCoeff y = 0 →
      chapter06PowerSeriesCompose
          (chapter06FormalGroupOperation F.series x y) h =
        chapter06FormalGroupOperation F.series
          (chapter06PowerSeriesCompose x h)
          (chapter06PowerSeriesCompose y h)

/-- The formal module data produced by a Lubin--Tate series. -/
structure Chapter06FormalModuleData
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D)) where
  formalGroup : Chapter06FormalGroupLaw (Chapter06ValuationRing D)
  scalar : Chapter06ValuationRing D →
    Chapter06UnivariateSeries (Chapter06ValuationRing D)
  scalar_zero : scalar 0 = 0
  scalar_one : scalar 1 = PowerSeries.X
  scalar_pi : scalar D.uniformizer = f
  scalar_linear : ∀ a, chapter06HasLinearCoefficient (scalar a) a
  scalar_endomorphism : ∀ a,
    chapter06IsFormalEndomorphism formalGroup (scalar a)
  scalar_add : ∀ (a b : Chapter06ValuationRing D),
      chapter06FormalGroupOperation formalGroup.series (scalar a) (scalar b) =
        scalar (a + b)
  scalar_mul : ∀ (a b : Chapter06ValuationRing D),
    chapter06PowerSeriesCompose (scalar b) (scalar a) = scalar (a * b)
  scalar_commutes : ∀ a,
    chapter06PowerSeriesCompose f (scalar a) =
      chapter06PowerSeriesCompose (scalar a) f

/-- Existence of the unique formal module attached to a Lubin--Tate series.
The uniqueness conclusion is stated on the actual series and scalar maps, so
proof fields in the package do not create a spurious notion of equality. -/
theorem chapter06_formal_module_construction_exists
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f) :
    ∃ M : Chapter06FormalModuleData D f,
      M.scalar D.uniformizer = f := by
  sorry

/- The existential package above is intentionally accompanied by the genuine
uniqueness interface on the formal group and scalar series. -/
theorem chapter06_formal_module_construction_unique
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (M₁ M₂ : Chapter06FormalModuleData D f) :
    M₁.formalGroup.series = M₂.formalGroup.series ∧
      ∀ a, M₁.scalar a = M₂.scalar a := by
  sorry

theorem chapter06_theorem_6_1
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f) :
    ∃ M : Chapter06FormalModuleData D f,
      M.scalar D.uniformizer = f ∧
        ∀ N : Chapter06FormalModuleData D f,
          N.scalar D.uniformizer = f →
            M.formalGroup.series = N.formalGroup.series ∧
              ∀ a, M.scalar a = N.scalar a := by
  sorry

/-- A chosen representative of the unique formal module. -/
noncomputable def chapter06FormalModuleOf
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f) :
    Chapter06FormalModuleData D f :=
  Classical.choose (chapter06_formal_module_construction_exists D f hf)

theorem chapter06FormalModuleOf_spec
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f) :
    (chapter06FormalModuleOf D f hf).scalar D.uniformizer = f := by
  exact Classical.choose_spec
    (chapter06_formal_module_construction_exists D f hf)

/-- The one-variable intertwining condition in Lemma 6.2. -/
def chapter06IntertwinerCondition
    {O : Type*} [CommRing O]
    (f g h : Chapter06UnivariateSeries O) (a : O) : Prop :=
  chapter06HasLinearCoefficient h a ∧
    chapter06PowerSeriesCompose f h = chapter06PowerSeriesCompose h g

/-- Lemma 6.2: integral one-variable intertwining recursion. -/
theorem chapter06_integral_intertwining_recursion
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g)
    (a : Chapter06ValuationRing D) :
    ∃! h : Chapter06UnivariateSeries (Chapter06ValuationRing D),
      chapter06IntertwinerCondition f g h a := by
  sorry

/-- Lemma 6.2 in two variables. -/
theorem chapter06_integral_two_variable_intertwining_recursion
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f) :
    ∃! H : Chapter06BivariateSeries (Chapter06ValuationRing D),
      chapter06HasLinearPart H 1 1 ∧ chapter06BivariateIntertwines f H := by
  sorry

theorem chapter06_lemma_6_2
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) (a : Chapter06ValuationRing D) :
    (∃! h, chapter06IntertwinerCondition f g h a) ∧
      (∃! H, chapter06HasLinearPart H 1 1 ∧
        chapter06BivariateIntertwines f H) := by
  exact ⟨chapter06_integral_intertwining_recursion D f g hf hg a,
    chapter06_integral_two_variable_intertwining_recursion D f hf⟩

/-- The coefficient step in the recursion: changing the degree-`r`
coefficient changes the error by `π^r-π`. -/
theorem chapter06_intertwining_recursion_coefficient_step
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (r : ℕ) (hr : 2 ≤ r) :
    (D.uniformizer : Chapter06ValuationRing D) ^ r - D.uniformizer =
      D.uniformizer *
        ((D.uniformizer : Chapter06ValuationRing D) ^ (r - 1) - 1) := by
  sorry

theorem chapter06_uniformizer_power_sub_one_is_unit
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (r : ℕ) (hr : 2 ≤ r) :
    IsUnit ((D.uniformizer : Chapter06ValuationRing D) ^ (r - 1) - 1) := by
  sorry

theorem chapter06_intertwining_error_coefficient_change
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (r : ℕ) (b c : Chapter06ValuationRing D) :
    (c + b * (D.uniformizer : Chapter06ValuationRing D) ^ r) -
        (c + b * D.uniformizer) =
      b * ((D.uniformizer : Chapter06ValuationRing D) ^ r - D.uniformizer) := by
  ring

/-- The reduction step used to show that the recursion error is divisible by
the uniformizer. -/
theorem chapter06_intertwining_error_is_uniformizer_divisible
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : Chapter06ValuationRing D,
      PowerSeries.coeff r (f - g) = (D.uniformizer : _) * c := by
  sorry

/-- The positive-valuation domain on which the formal series are evaluated. -/
def chapter06PositiveValuationPoint
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    {D : Chapter06LocalFieldData K}
    (V : Chapter06ValuedFiniteExtension D E) (x : E) : Prop :=
  V.valuation x > 0

noncomputable def chapter06FormalModuleScalarEvaluation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    {f : Chapter06UnivariateSeries (Chapter06ValuationRing D)}
    (M : Chapter06FormalModuleData D f)
    (a : Chapter06ValuationRing D) (x : E) : E :=
  PowerSeries.eval₂ (algebraMap (Chapter06ValuationRing D) E) x
    (M.scalar a)

noncomputable def chapter06FormalIntertwinerEvaluation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (h : Chapter06UnivariateSeries (Chapter06ValuationRing D)) (x : E) : E :=
  PowerSeries.eval₂ (algebraMap (Chapter06ValuationRing D) E) x h

def chapter06FormalModuleTorsionSet
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    {f : Chapter06UnivariateSeries (Chapter06ValuationRing D)}
    (V : Chapter06ValuedFiniteExtension D E)
    (M : Chapter06FormalModuleData D f) (n : ℕ) : Set E :=
  {x | chapter06PositiveValuationPoint V x ∧
    chapter06FormalModuleScalarEvaluation M
      ((D.uniformizer : Chapter06ValuationRing D) ^ n) x = 0}

def chapter06FormalModulePrimitiveTorsionSet
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    {f : Chapter06UnivariateSeries (Chapter06ValuationRing D)}
    (V : Chapter06ValuedFiniteExtension D E)
    (M : Chapter06FormalModuleData D f) (n : ℕ) : Set E :=
  {x | x ∈ chapter06FormalModuleTorsionSet V M n ∧
    chapter06FormalModuleScalarEvaluation M
      ((D.uniformizer : Chapter06ValuationRing D) ^ (n - 1)) x ≠ 0}

/-- Formal series converge on the maximal ideal of every complete finite
extension. -/
theorem chapter06_formal_series_converges_on_positive_valuation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    [UniformSpace E] [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    (D : Chapter06LocalFieldData K)
    (V : Chapter06ValuedFiniteExtension D E)
    (x : E) (hx : chapter06PositiveValuationPoint V x)
    (F : PowerSeries (Chapter06ValuationRing D)) :
    PowerSeries.HasEval x := by
  sorry

/-- The formal group operation evaluated on positive-valuation points. -/
noncomputable def chapter06EvaluatedFormalGroupOperation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (F : Chapter06FormalGroupLaw (Chapter06ValuationRing D)) (x y : E) : E :=
  MvPowerSeries.eval₂ (algebraMap (Chapter06ValuationRing D) E)
    (fun i : Fin 2 => if i = (0 : Fin 2) then x else y) F.series

theorem chapter06_formal_group_points_closed
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (F : Chapter06FormalGroupLaw (Chapter06ValuationRing D))
    (x y : E) (hx : chapter06PositiveValuationPoint V x)
    (hy : chapter06PositiveValuationPoint V y) :
    chapter06PositiveValuationPoint V
      (chapter06EvaluatedFormalGroupOperation F x y) := by
  sorry

/-- Changing the Lubin--Tate series gives an integral formal-module
isomorphism, not a literal equality of coordinates. -/
noncomputable def chapter06FormalModuleIntertwiner
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) :
    Chapter06UnivariateSeries (Chapter06ValuationRing D) :=
  Classical.choose
    (chapter06_integral_intertwining_recursion D f g hf hg 1)

theorem chapter06FormalModuleIntertwiner_spec
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) :
    chapter06IntertwinerCondition f g
      (chapter06FormalModuleIntertwiner D f g hf hg) 1 := by
  exact (Classical.choose_spec
    (chapter06_integral_intertwining_recursion D f g hf hg 1)).1

theorem chapter06FormalModuleIntertwiner_inverse
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) :
    chapter06PowerSeriesCompose
        (chapter06FormalModuleIntertwiner D f g hf hg)
        (chapter06FormalModuleIntertwiner D g f hg hf) =
      PowerSeries.X := by
  sorry

theorem chapter06FormalModuleIntertwiner_inverse_reverse
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) :
    chapter06PowerSeriesCompose
        (chapter06FormalModuleIntertwiner D g f hg hf)
        (chapter06FormalModuleIntertwiner D f g hf hg) =
      PowerSeries.X := by
  sorry

theorem chapter06FormalModuleIntertwiner_conjugates_scalars
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) (a : Chapter06ValuationRing D) :
    chapter06PowerSeriesCompose
        ((chapter06FormalModuleOf D f hf).scalar a)
        (chapter06FormalModuleIntertwiner D f g hf hg) =
      chapter06PowerSeriesCompose
        (chapter06FormalModuleIntertwiner D f g hf hg)
        ((chapter06FormalModuleOf D g hg).scalar a) := by
  sorry

theorem chapter06_formal_module_intertwiner_maps_positive_valuation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g)
    (x : E) (hx : chapter06PositiveValuationPoint V x) :
    chapter06PositiveValuationPoint V
      (chapter06FormalIntertwinerEvaluation
        (chapter06FormalModuleIntertwiner D f g hf hg) x) := by
  sorry

theorem chapter06_formal_module_intertwiner_maps_torsion
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g)
    (x : E) (hx : chapter06PositiveValuationPoint V x) (n : ℕ) :
    chapter06FormalModuleScalarEvaluation
        (chapter06FormalModuleOf D f hf)
        ((D.uniformizer : Chapter06ValuationRing D) ^ n) x = 0 ↔
      chapter06FormalModuleScalarEvaluation
        (chapter06FormalModuleOf D g hg)
        ((D.uniformizer : Chapter06ValuationRing D) ^ n)
        (chapter06FormalIntertwinerEvaluation
          (chapter06FormalModuleIntertwiner D f g hf hg) x) = 0 := by
  sorry

theorem chapter06_formal_module_intertwiner_torsion_bijective
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g)
    (n : ℕ) :
    Function.Bijective
      (fun x : {x : E // x ∈ chapter06FormalModuleTorsionSet V
          (chapter06FormalModuleOf D f hf) n} =>
        (⟨chapter06FormalIntertwinerEvaluation
            (chapter06FormalModuleIntertwiner D f g hf hg) x,
          by sorry⟩ :
          {x : E // x ∈ chapter06FormalModuleTorsionSet V
            (chapter06FormalModuleOf D g hg) n})) := by
  sorry

theorem chapter06_formal_module_intertwiner_preserves_primitive_torsion
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g)
    (n : ℕ) (hn : 0 < n) (x : E)
    (hx : x ∈ chapter06FormalModulePrimitiveTorsionSet V
      (chapter06FormalModuleOf D f hf) n) :
    chapter06FormalIntertwinerEvaluation
        (chapter06FormalModuleIntertwiner D f g hf hg) x ∈
      chapter06FormalModulePrimitiveTorsionSet V
        (chapter06FormalModuleOf D g hg) n := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
