import LastLib.Book05LocalClassFieldTheory.Chapter06.Section01WhyASeparateExistenceConstructionIsNecessary
import Mathlib.RingTheory.FormalGroup.Basic

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
  let _ := D.residue_finite
  let _ : Fintype (Chapter06ResidueField D) := Fintype.ofFinite _
  have hq : 1 < chapter06ResidueCardinality D := by
    simpa [chapter06ResidueCardinality, Nat.card_eq_fintype_card] using
      (Fintype.one_lt_card : 1 < Fintype.card (Chapter06ResidueField D))
  have hq0 : chapter06ResidueCardinality D ≠ 0 := by omega
  have hqne1 : 1 ≠ chapter06ResidueCardinality D := by omega
  constructor
  · intro n hn
    interval_cases n <;>
      simp [chapter06ExplicitLubinTateSeries, hq0, hqne1]
  · intro n
    refine Ideal.mem_span_singleton'.2 ⟨PowerSeries.coeff n PowerSeries.X, ?_⟩
    simp [chapter06ExplicitLubinTateSeries, mul_comm]

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

/-- The source-facing formal-group package.

The formal-group law itself is Mathlib's canonical `FormalGroup`.  The
chapter adds the inverse series because the current Mathlib API exposes the
formal addition monoid but does not bundle a chosen inverse power series. -/
structure Chapter06FormalGroupLaw (O : Type*) [CommRing O] where
  formalGroup : FormalGroup O
  commutative : FormalGroup.IsComm formalGroup
  inverse : Chapter06UnivariateSeries O
  inverse_const : MvPowerSeries.constantCoeff inverse = 0
  inverse_left : ∀ x : Chapter06UnivariateSeries O,
    MvPowerSeries.constantCoeff x = 0 →
      chapter06FormalGroupOperation formalGroup.toPowerSeries inverse x = 0
  inverse_right : ∀ x : Chapter06UnivariateSeries O,
    MvPowerSeries.constantCoeff x = 0 →
      chapter06FormalGroupOperation formalGroup.toPowerSeries x inverse = 0

/-- The underlying two-variable series in the notation used by Chapter 6. -/
def Chapter06FormalGroupLaw.series
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O) :
    Chapter06BivariateSeries O :=
  F.formalGroup.toPowerSeries

instance Chapter06FormalGroupLaw.formalGroupIsComm
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O) :
    FormalGroup.IsComm F.formalGroup := F.commutative

theorem chapter06FormalGroupLaw_hasLinearPart
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O) :
    chapter06HasLinearPart F.series 1 1 := by
  intro d hd
  classical
  by_cases hzero : d = 0
  · subst d
    change MvPowerSeries.constantCoeff F.formalGroup.toPowerSeries =
      MvPowerSeries.constantCoeff (chapter06LinearSeries 1 1)
    simpa [chapter06LinearSeries] using F.formalGroup.zero_constantCoeff
  have htest : d.sum (fun _ n => n) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype d (fun _ n => n) (fun _ => rfl)]
    simp
  have hsum : d 0 + d 1 < 2 := by
    rw [← htest]
    exact hd
  have hnonzero : d 0 + d 1 ≠ 0 := by
    intro hsumzero
    have hd0 : d 0 = 0 := by omega
    have hd1 : d 1 = 0 := by omega
    apply hzero
    ext i
    fin_cases i <;> simp [hd0, hd1]
  have hdegree : d.sum (fun _ n => n) = 1 := by
    rw [htest]
    omega
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d).mp hdegree
  fin_cases i
  · rw [hi]
    change F.formalGroup.toPowerSeries.coeff (Finsupp.single 0 1) =
      MvPowerSeries.coeff (Finsupp.single 0 1) (chapter06LinearSeries 1 1)
    rw [F.formalGroup.lin_coeff_X]
    simp [chapter06LinearSeries, MvPowerSeries.coeff_X, Finsupp.single_left_inj]
  · rw [hi]
    change F.formalGroup.toPowerSeries.coeff (Finsupp.single 1 1) =
      MvPowerSeries.coeff (Finsupp.single 1 1) (chapter06LinearSeries 1 1)
    rw [F.formalGroup.lin_coeff_Y]
    simp [chapter06LinearSeries, MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem chapter06FormalGroupLaw_zero_left
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O)
    (x : Chapter06UnivariateSeries O)
    (hx : MvPowerSeries.constantCoeff x = 0) :
    chapter06FormalGroupOperation F.series 0 x = x := by
  change MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then 0 else x) F.series = x
  have hfun : (fun i : Fin 2 => if i = 0 then 0 else x) = ![0, x] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]
  exact F.formalGroup.zero_add
    (PowerSeries.HasSubst.of_constantCoeff_zero' hx)

theorem chapter06FormalGroupLaw_zero_right
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O)
    (x : Chapter06UnivariateSeries O)
    (hx : MvPowerSeries.constantCoeff x = 0) :
    chapter06FormalGroupOperation F.series x 0 = x := by
  change MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then x else 0) F.series = x
  have hfun : (fun i : Fin 2 => if i = 0 then x else 0) = ![x, 0] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]
  exact F.formalGroup.add_zero
    (PowerSeries.HasSubst.of_constantCoeff_zero' hx)

theorem chapter06FormalGroupLaw_associative
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O)
    (x y z : Chapter06UnivariateSeries O)
    (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0)
    (hz : MvPowerSeries.constantCoeff z = 0) :
    chapter06FormalGroupOperation F.series
        (chapter06FormalGroupOperation F.series x y) z =
      chapter06FormalGroupOperation F.series x
        (chapter06FormalGroupOperation F.series y z) := by
  change MvPowerSeries.subst
      (fun i : Fin 2 => if i = 0 then
        MvPowerSeries.subst (fun j : Fin 2 => if j = 0 then x else y) F.series
        else z) F.series =
    MvPowerSeries.subst
      (fun i : Fin 2 => if i = 0 then x else
        MvPowerSeries.subst (fun j : Fin 2 => if j = 0 then y else z) F.series) F.series
  have hxy : (fun j : Fin 2 => if j = 0 then x else y) = ![x, y] := by
    funext j
    fin_cases j <;> simp
  have hyz : (fun j : Fin 2 => if j = 0 then y else z) = ![y, z] := by
    funext j
    fin_cases j <;> simp
  rw [hxy, hyz]
  have hleft : (fun i : Fin 2 => if i = 0 then
      MvPowerSeries.subst ![x, y] F.series else z) =
      ![MvPowerSeries.subst ![x, y] F.series, z] := by
    funext i
    fin_cases i <;> simp
  have hright : (fun i : Fin 2 => if i = 0 then x else
      MvPowerSeries.subst ![y, z] F.series) =
      ![x, MvPowerSeries.subst ![y, z] F.series] := by
    funext i
    fin_cases i <;> simp
  rw [hleft, hright]
  exact F.formalGroup.assoc'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hx)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hy)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hz)

theorem chapter06FormalGroupLaw_commutative
    {O : Type*} [CommRing O] (F : Chapter06FormalGroupLaw O)
    (x y : Chapter06UnivariateSeries O)
    (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
      chapter06FormalGroupOperation F.series x y =
      chapter06FormalGroupOperation F.series y x := by
  change MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then x else y) F.series =
    MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then y else x) F.series
  have hxy : (fun i : Fin 2 => if i = 0 then x else y) = ![x, y] := by
    funext i
    fin_cases i <;> simp
  have hyx : (fun i : Fin 2 => if i = 0 then y else x) = ![y, x] := by
    funext i
    fin_cases i <;> simp
  rw [hxy, hyx]
  exact F.formalGroup.comm'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hx)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hy)

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
  obtain ⟨M, hM⟩ := chapter06_formal_module_construction_exists D f hf
  refine ⟨M, hM, ?_⟩
  intro N _hN
  exact chapter06_formal_module_construction_unique D f hf M N

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
  calc
    (D.uniformizer : Chapter06ValuationRing D) ^ r - D.uniformizer =
        (D.uniformizer : Chapter06ValuationRing D) ^ ((r - 1) + 1) -
          D.uniformizer := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
    _ = D.uniformizer * (D.uniformizer : Chapter06ValuationRing D) ^ (r - 1) -
        D.uniformizer := by
      rw [pow_succ']
    _ = D.uniformizer *
        ((D.uniformizer : Chapter06ValuationRing D) ^ (r - 1) - 1) := by
      ring

theorem chapter06_uniformizer_power_sub_one_is_unit
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (r : ℕ) (hr : 2 ≤ r) :
    IsUnit ((D.uniformizer : Chapter06ValuationRing D) ^ (r - 1) - 1) := by
  have hmax :
      IsLocalRing.maximalIdeal (Chapter06ValuationRing D) =
        Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D)) :=
    D.uniformizer_spec.2
  have hπ : (D.uniformizer : Chapter06ValuationRing D) ∈
      IsLocalRing.maximalIdeal (Chapter06ValuationRing D) := by
    rw [hmax]
    exact Ideal.mem_span_singleton_self _
  have hpow : (D.uniformizer : Chapter06ValuationRing D) ^ (r - 1) ∈
      IsLocalRing.maximalIdeal (Chapter06ValuationRing D) := by
    apply (Ideal.pow_le_self (by omega : r - 1 ≠ 0))
    exact Ideal.pow_mem_pow hπ (r - 1)
  have hnonunit : ¬ IsUnit ((D.uniformizer : Chapter06ValuationRing D) ^ (r - 1)) := by
    intro hu
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hpow
  have hu : IsUnit (1 - (D.uniformizer : Chapter06ValuationRing D) ^ (r - 1)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hnonunit
  simpa [sub_eq_neg_add] using hu.neg

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
    (hg : chapter06LubinTateCondition D g) (r : ℕ) (_hr : 2 ≤ r) :
    ∃ c : Chapter06ValuationRing D,
      PowerSeries.coeff r (f - g) = (D.uniformizer : _) * c := by
  let I : Ideal (Chapter06ValuationRing D) :=
    Ideal.span ({D.uniformizer} : Set (Chapter06ValuationRing D))
  have hmem : PowerSeries.coeff r (f - g) ∈ I := by
    have hfmem := hf.2 r
    have hgmem := hg.2 r
    have hsub := I.sub_mem hfmem hgmem
    simpa only [map_sub, sub_sub_sub_cancel_right] using hsub
  rcases Ideal.mem_span_singleton'.mp hmem with ⟨c, hc⟩
  exact ⟨c, hc.symm.trans (mul_comm _ _)⟩

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

noncomputable def chapter06EvaluatedFormalGroupInverse
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    {D : Chapter06LocalFieldData K}
    [UniformSpace (Chapter06ValuationRing D)]
    (F : Chapter06FormalGroupLaw (Chapter06ValuationRing D)) (x : E) : E :=
  PowerSeries.eval₂ (algebraMap (Chapter06ValuationRing D) E) x F.inverse

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

theorem chapter06_formal_group_inverse_closed
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (F : Chapter06FormalGroupLaw (Chapter06ValuationRing D)) (x : E)
    (hx : chapter06PositiveValuationPoint V x) :
    chapter06PositiveValuationPoint V
      (chapter06EvaluatedFormalGroupInverse F x) := by
  sorry

abbrev Chapter06FormalGroupPoint
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    {D : Chapter06LocalFieldData K}
    (V : Chapter06ValuedFiniteExtension D E)
    (_F : Chapter06FormalGroupLaw (Chapter06ValuationRing D)) : Type _ :=
  {x : E // chapter06PositiveValuationPoint V x}

/-- Positive-valuation points form the additive group supplied by the formal
group law.  The operation and inverse are the evaluated series above; the
group laws are the corresponding formal identities. -/
noncomputable instance chapter06FormalGroupPointAddCommGroup
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [UniformSpace E]
    [FiniteDimensional K E]
    [CompleteSpace E]
    [IsTopologicalRing E] [IsLinearTopology E E]
    (D : Chapter06LocalFieldData K)
    [UniformSpace (Chapter06ValuationRing D)]
    (V : Chapter06ValuedFiniteExtension D E)
    (F : Chapter06FormalGroupLaw (Chapter06ValuationRing D)) :
    AddCommGroup (Chapter06FormalGroupPoint V F) := by
  let add : Chapter06FormalGroupPoint V F →
      Chapter06FormalGroupPoint V F → Chapter06FormalGroupPoint V F := fun x y =>
    ⟨chapter06EvaluatedFormalGroupOperation F x.1 y.1,
      chapter06_formal_group_points_closed D V F x.1 y.1 x.2 y.2⟩
  let zero : Chapter06FormalGroupPoint V F := ⟨0, by
    change V.valuation (0 : E) > 0
    rw [AddValuation.map_zero]
    simp⟩
  let neg : Chapter06FormalGroupPoint V F → Chapter06FormalGroupPoint V F := fun x =>
    ⟨chapter06EvaluatedFormalGroupInverse F x.1,
      chapter06_formal_group_inverse_closed D V F x.1 x.2⟩
  letI : Zero (Chapter06FormalGroupPoint V F) := ⟨zero⟩
  letI : Add (Chapter06FormalGroupPoint V F) := ⟨add⟩
  letI : Neg (Chapter06FormalGroupPoint V F) := ⟨neg⟩
  refine
    { add := add
      zero := zero
      neg := neg
      add_assoc := by sorry
      zero_add := by sorry
      add_zero := by sorry
      neg_add_cancel := by sorry
      add_comm := by sorry
      nsmul := nsmulRec
      zsmul := zsmulRec
      nsmul_zero := by intros; rfl
      nsmul_succ := by intros; rfl
      sub_eq_add_neg := by intros; rfl
      zsmul_zero' := by intros; rfl
      zsmul_succ' := by intros; rfl
      zsmul_neg' := by intros; rfl }

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
  let h := chapter06FormalModuleIntertwiner D f g hf hg
  let k := chapter06FormalModuleIntertwiner D g f hg hf
  have hh := chapter06FormalModuleIntertwiner_spec D f g hf hg
  have hk := chapter06FormalModuleIntertwiner_spec D g f hg hf
  have hh0 : PowerSeries.constantCoeff h = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hh.1 0 (by omega)]
    simp
  have hk0 : PowerSeries.constantCoeff k = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hk.1 0 (by omega)]
    simp
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hf.1 0 (by omega)]
    simp
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hg.1 0 (by omega)]
    simp
  have hhs : PowerSeries.HasSubst h :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hks : PowerSeries.HasSubst k :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hk0
  have hfs : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hgs : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hh1 : PowerSeries.coeff 1 h = 1 := by
    simpa [chapter06HasLinearCoefficient] using hh.1 1 (by omega)
  have hk1 : PowerSeries.coeff 1 k = 1 := by
    simpa [chapter06HasLinearCoefficient] using hk.1 1 (by omega)
  have hh_eq : PowerSeries.subst f h = PowerSeries.subst h g := by
    exact hh.2
  have hk_eq : PowerSeries.subst g k = PowerSeries.subst k f := by
    exact hk.2
  have hcomp : chapter06IntertwinerCondition f f
      (chapter06PowerSeriesCompose h k) 1 := by
    constructor
    · intro n hn
      interval_cases n
      · simpa [chapter06PowerSeriesCompose, PowerSeries.constantCoeff_eq] using
          (show MvPowerSeries.constantCoeff (PowerSeries.subst h k) = 0 from
            PowerSeries.constantCoeff_subst_eq_zero hh0 k hk0)
      · have hcoeff : PowerSeries.coeff 1 (PowerSeries.subst h k) = 1 := by
          rw [PowerSeries.coeff_subst' hhs, finsum_eq_single _ 1]
          · simp [hh1, hk1]
          · intro d hd
            by_cases hd0 : d = 0
            · subst d
              simp
            · by_cases hd1 : d = 1
              · exact (hd hd1).elim
              · have hd2 : 2 ≤ d := by omega
                rw [PowerSeries.coeff_one_pow]
                have hdpos : 0 < d - 1 := by omega
                rw [hh0, zero_pow (Nat.ne_of_gt hdpos)]
                simp
        simpa [chapter06PowerSeriesCompose] using hcoeff
    · change PowerSeries.subst f (PowerSeries.subst h k) =
        PowerSeries.subst (PowerSeries.subst h k) f
      calc
        PowerSeries.subst f (PowerSeries.subst h k) =
            PowerSeries.subst (PowerSeries.subst f h) k :=
          PowerSeries.subst_comp_subst_apply hhs hfs k
        _ = PowerSeries.subst (PowerSeries.subst h g) k := by rw [hh_eq]
        _ = PowerSeries.subst h (PowerSeries.subst g k) :=
          (PowerSeries.subst_comp_subst_apply hgs hhs k).symm
        _ = PowerSeries.subst h (PowerSeries.subst k f) := by rw [← hk_eq]
        _ = PowerSeries.subst (PowerSeries.subst h k) f :=
          PowerSeries.subst_comp_subst_apply hks hhs f
  have hX : chapter06IntertwinerCondition f f PowerSeries.X 1 := by
    constructor
    · intro n hn
      interval_cases n <;> simp
    · simpa [chapter06PowerSeriesCompose] using
        (PowerSeries.subst_X hfs).trans (PowerSeries.X_subst f).symm
  apply (chapter06_integral_intertwining_recursion D f f hf hf 1).unique
  · simpa [h, k] using hcomp
  · exact hX

theorem chapter06FormalModuleIntertwiner_inverse_reverse
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (f g : Chapter06UnivariateSeries (Chapter06ValuationRing D))
    (hf : chapter06LubinTateCondition D f)
    (hg : chapter06LubinTateCondition D g) :
    chapter06PowerSeriesCompose
        (chapter06FormalModuleIntertwiner D g f hg hf)
        (chapter06FormalModuleIntertwiner D f g hf hg) =
      PowerSeries.X := by
  exact chapter06FormalModuleIntertwiner_inverse D g f hg hf

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
  let Mf := chapter06FormalModuleOf D f hf
  let Mg := chapter06FormalModuleOf D g hg
  let h := chapter06FormalModuleIntertwiner D f g hf hg
  let sf := Mf.scalar a
  let sg := Mg.scalar a
  have hh := chapter06FormalModuleIntertwiner_spec D f g hf hg
  have hh0 : PowerSeries.constantCoeff h = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hh.1 0 (by omega)]
    simp
  have hsf_lin : chapter06HasLinearCoefficient sf a := Mf.scalar_linear a
  have hsg_lin : chapter06HasLinearCoefficient sg a := Mg.scalar_linear a
  have hsf0 : PowerSeries.constantCoeff sf = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hsf_lin 0 (by omega)]
    simp
  have hsg0 : PowerSeries.constantCoeff sg = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hsg_lin 0 (by omega)]
    simp
  have hcomp_linear :
      ∀ (p q : Chapter06UnivariateSeries (Chapter06ValuationRing D))
        (ap aq : Chapter06ValuationRing D),
        PowerSeries.constantCoeff p = 0 →
        PowerSeries.constantCoeff q = 0 →
        chapter06HasLinearCoefficient p ap →
        chapter06HasLinearCoefficient q aq →
        chapter06HasLinearCoefficient
          (chapter06PowerSeriesCompose p q) (ap * aq) := by
    intro p q ap aq hp0 hq0 hpl hql n hn
    interval_cases n
    · simpa [chapter06PowerSeriesCompose, PowerSeries.constantCoeff_eq] using
        (PowerSeries.constantCoeff_subst_eq_zero hp0 q hq0)
    · have hpl1 : PowerSeries.coeff 1 p = ap := by
        simpa [chapter06HasLinearCoefficient] using hpl 1 (by omega)
      have hql1 : PowerSeries.coeff 1 q = aq := by
        simpa [chapter06HasLinearCoefficient] using hql 1 (by omega)
      have hcoeff : PowerSeries.coeff 1 (PowerSeries.subst p q) = aq * ap := by
        rw [PowerSeries.coeff_subst'
          (PowerSeries.HasSubst.of_constantCoeff_zero' hp0),
          finsum_eq_single _ 1]
        · simp [hpl1, hql1]
        · intro d hd
          by_cases hd0 : d = 0
          · subst d
            simp
          · by_cases hd1 : d = 1
            · exact (hd hd1).elim
            · have hd2 : 2 ≤ d := by omega
              rw [PowerSeries.coeff_one_pow]
              have hdpos : 0 < d - 1 := by omega
              rw [hp0, zero_pow (Nat.ne_of_gt hdpos)]
              simp
      simpa [chapter06PowerSeriesCompose, mul_comm] using hcoeff
  have hhs : PowerSeries.HasSubst h :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hsf_sub : PowerSeries.HasSubst sf :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hsf0
  have hsg_sub : PowerSeries.HasSubst sg :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hsg0
  have hA_linear :
      chapter06HasLinearCoefficient
        (chapter06PowerSeriesCompose sf h) a := by
    simpa using hcomp_linear sf h a 1 hsf0 hh0 hsf_lin
      (by simpa using hh.1)
  have hB_linear :
      chapter06HasLinearCoefficient
        (chapter06PowerSeriesCompose h sg) a := by
    simpa [mul_comm] using hcomp_linear h sg 1 a hh0 hsg0
      (by simpa using hh.1) hsg_lin
  have hh_eq :
      PowerSeries.subst f h = PowerSeries.subst h g := hh.2
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hf.1 0 (by omega)]
    simp
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hg.1 0 (by omega)]
    simp
  have hfs : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hgs : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hA_eq :
      chapter06PowerSeriesCompose f
          (chapter06PowerSeriesCompose sf h) =
        chapter06PowerSeriesCompose
          (chapter06PowerSeriesCompose sf h) g := by
    change PowerSeries.subst f (PowerSeries.subst sf h) =
      PowerSeries.subst (PowerSeries.subst sf h) g
    calc
      PowerSeries.subst f (PowerSeries.subst sf h) =
          PowerSeries.subst (PowerSeries.subst f sf) h :=
        PowerSeries.subst_comp_subst_apply hsf_sub hfs h
      _ = PowerSeries.subst (PowerSeries.subst sf f) h := by
        have hcomm : PowerSeries.subst f sf = PowerSeries.subst sf f := by
          simpa [chapter06PowerSeriesCompose, sf] using Mf.scalar_commutes a
        rw [hcomm]
      _ = PowerSeries.subst sf (PowerSeries.subst f h) :=
        (PowerSeries.subst_comp_subst_apply hfs hsf_sub h).symm
      _ = PowerSeries.subst sf (PowerSeries.subst h g) := by rw [hh_eq]
      _ = PowerSeries.subst (PowerSeries.subst sf h) g :=
        PowerSeries.subst_comp_subst_apply hhs hsf_sub g
  have hB_eq :
      chapter06PowerSeriesCompose f
          (chapter06PowerSeriesCompose h sg) =
        chapter06PowerSeriesCompose
          (chapter06PowerSeriesCompose h sg) g := by
    change PowerSeries.subst f (PowerSeries.subst h sg) =
      PowerSeries.subst (PowerSeries.subst h sg) g
    calc
      PowerSeries.subst f (PowerSeries.subst h sg) =
          PowerSeries.subst (PowerSeries.subst f h) sg :=
        PowerSeries.subst_comp_subst_apply hhs hfs sg
      _ = PowerSeries.subst (PowerSeries.subst h g) sg := by rw [hh_eq]
      _ = PowerSeries.subst h (PowerSeries.subst g sg) :=
        (PowerSeries.subst_comp_subst_apply hgs hhs sg).symm
      _ = PowerSeries.subst h (PowerSeries.subst sg g) := by
        have hcomm : PowerSeries.subst g sg = PowerSeries.subst sg g := by
          simpa [chapter06PowerSeriesCompose, sg] using Mg.scalar_commutes a
        rw [hcomm]
      _ = PowerSeries.subst (PowerSeries.subst h sg) g :=
        PowerSeries.subst_comp_subst_apply hsg_sub hhs g
  have hAcond :
      chapter06IntertwinerCondition f g
        (chapter06PowerSeriesCompose sf h) a :=
    ⟨hA_linear, hA_eq⟩
  have hBcond :
      chapter06IntertwinerCondition f g
        (chapter06PowerSeriesCompose h sg) a :=
    ⟨hB_linear, hB_eq⟩
  have hAB : chapter06PowerSeriesCompose sf h =
      chapter06PowerSeriesCompose h sg := by
    apply (chapter06_integral_intertwining_recursion D f g hf hg a).unique
    · exact hAcond
    · exact hBcond
  simpa [Mf, Mg, h, sf, sg] using hAB

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
  rcases hx with ⟨⟨hxpos, hxn⟩, hxprev⟩
  let h := chapter06FormalModuleIntertwiner D f g hf hg
  let y := chapter06FormalIntertwinerEvaluation h x
  have hypos : chapter06PositiveValuationPoint V y := by
    exact chapter06_formal_module_intertwiner_maps_positive_valuation
      V f g hf hg x hxpos
  have hyn :
      chapter06FormalModuleScalarEvaluation
          (chapter06FormalModuleOf D g hg)
          ((D.uniformizer : Chapter06ValuationRing D) ^ n) y = 0 := by
    exact (chapter06_formal_module_intertwiner_maps_torsion
      V f g hf hg x hxpos n).mp hxn
  have hyprev :
      chapter06FormalModuleScalarEvaluation
          (chapter06FormalModuleOf D g hg)
          ((D.uniformizer : Chapter06ValuationRing D) ^ (n - 1)) y ≠ 0 := by
    intro hzero
    have hzero' :
        chapter06FormalModuleScalarEvaluation
            (chapter06FormalModuleOf D f hf)
            ((D.uniformizer : Chapter06ValuationRing D) ^ (n - 1)) x = 0 := by
      exact (chapter06_formal_module_intertwiner_maps_torsion
        V f g hf hg x hxpos (n - 1)).mpr hzero
    exact hxprev hzero'
  change y ∈ chapter06FormalModulePrimitiveTorsionSet V
    (chapter06FormalModuleOf D g hg) n
  exact ⟨⟨hypos, hyn⟩, hyprev⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
