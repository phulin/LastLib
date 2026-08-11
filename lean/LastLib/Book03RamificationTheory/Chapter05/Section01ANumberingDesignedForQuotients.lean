import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.1. A numbering designed for quotients -/

/--
 A finite lower ramification filtration in the real-index convention used in
 Book 3.  The `lowerGroup` field is the real extension of the integer lower
 groups from Chapter 4.  In particular, on `(m,m+1]` it has the value of the
 `(m+1)`st integer group; this is the convention for which the Herbrand slope
 on that interval is `|G_(m+1)| / |G_0|`.

 The displacement field deliberately uses the Chapter 4 normalization
 `G_m = {σ | i_G(σ) ≥ m+1}`.  It is only constrained away from the identity,
 whose displacement is recorded separately as zero because the finite value
 `i_G(1)=+∞` is not needed by any quotient identity.
-/
structure Chapter05RamificationFiltration
    (G : Type*) [Group G] [Finite G] where
  lowerGroup : ℝ → Subgroup G
  lower_antitone : Antitone lowerGroup
  lower_normal : ∀ u : ℝ, (lowerGroup u).Normal
  lower_neg : ∀ u : ℝ, (-1 : ℝ) ≤ u → u < 0 → lowerGroup u = ⊤
  lower_real_convention :
    ∀ (m : ℕ) (u : ℝ), (m : ℝ) < u → u ≤ (m + 1 : ℕ) →
      lowerGroup u = lowerGroup (m + 1 : ℕ)
  lower_eventually_trivial : ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
    lowerGroup (m : ℝ) = ⊥
  displacement : G → ℕ
  displacement_one : displacement 1 = 0
  lower_nat_mem_iff :
    ∀ {σ : G}, σ ≠ 1 → ∀ n : ℕ,
      σ ∈ lowerGroup (n : ℝ) ↔ n + 1 ≤ displacement σ

namespace Chapter05RamificationFiltration

variable {G : Type*} [Group G] [Finite G]

instance :
    CoeFun (Chapter05RamificationFiltration G) (fun _ => ℝ → Subgroup G) :=
  ⟨Chapter05RamificationFiltration.lowerGroup⟩

@[simp] theorem lowerGroup_apply (D : Chapter05RamificationFiltration G)
    (u : ℝ) : D u = D.lowerGroup u := rfl

end Chapter05RamificationFiltration

/-- The right-hand limit of a decreasing subgroup-valued filtration. -/
noncomputable def chapter05RightLimit
    {G : Type*} [Group G] [Finite G]
    (F : ℝ → Subgroup G) (u : ℝ) : Subgroup G :=
  sSup (F '' Set.Ioi u)

/-- Left continuity away from the deliberately separated jump at zero. -/
def chapter05LeftContinuousOnPositive
    {G : Type*} [Group G] [Finite G]
    (F : ℝ → Subgroup G) : Prop :=
  ∀ u : ℝ, 0 < u → F u = sInf (F '' Set.Ioo (-1 : ℝ) u)

/-- The integer lower breaks, with the Chapter 4 shift by one. -/
def chapter05LowerBreak
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (m : ℕ) : Prop :=
  D.lowerGroup (m : ℝ) ≠ D.lowerGroup (m + 1 : ℕ)

/-- The slope of the Herbrand clock at a positive lower depth. -/
noncomputable def chapter05HerbrandSlope
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) : ℝ :=
  if u ≤ 0 then 1 else
    (Nat.card (D.lowerGroup u) : ℝ) /
      (Nat.card (D.lowerGroup 0) : ℝ)

/--
 The Herbrand function, extended by the identity on the negative interval.
 The interval integral is the canonical construction; the filtration fields
 ensure that its integrand is the required positive piecewise-constant slope.
-/
noncomputable def chapter05HerbrandFunction
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) : ℝ :=
  if u ≤ 0 then u else
    ∫ t in (0 : ℝ)..u, chapter05HerbrandSlope D t

theorem chapter05_herbrand_function_neg_one
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter05HerbrandFunction D (-1 : ℝ) = -1 := by
  sorry

theorem chapter05_herbrand_function_zero
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter05HerbrandFunction D 0 = 0 := by
  sorry

/-- The inverse of the Herbrand function, using `invFun` before bijectivity is proved. -/
noncomputable def chapter05HerbrandInverse
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : ℝ :=
  Function.invFun (chapter05HerbrandFunction D) v

/-- The upper-numbered group `G^v = G_{ψ(v)}`. -/
def chapter05UpperRamificationGroup
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Subgroup G :=
  if (-1 : ℝ) ≤ v then D.lowerGroup (chapter05HerbrandInverse D v) else ⊥

/-- The upper filtration immediately to the right of an index. -/
noncomputable def chapter05UpperRightLimit
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Subgroup G :=
  chapter05RightLimit (chapter05UpperRamificationGroup D) v

/-- The stable group immediately to the right of zero. -/
noncomputable def chapter05UpperZeroPlus
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Subgroup G :=
  chapter05UpperRightLimit D 0

/-- An upper ramification break is a strict drop at the chosen upper index. -/
def chapter05UpperBreak
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Prop :=
  (-1 : ℝ) ≤ v ∧
    chapter05UpperRamificationGroup D v ≠ chapter05UpperRightLimit D v

/-- The set of all upper breaks of a filtration. -/
def chapter05UpperBreakSet
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Set ℝ :=
  {v | chapter05UpperBreak D v}

/-- The book's rationality predicate for an upper break. -/
def chapter05UpperBreakIsRational (v : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = v

/-- The book's integrality predicate for an upper break. -/
def chapter05UpperBreakIsInteger (v : ℝ) : Prop :=
  ∃ z : ℤ, (z : ℝ) = v

/--
 The canonical integer congruence groups from Book 2, embedded in the ambient
 Galois group.  This is the bridge used when a Chapter 4 profile is realized
 by a chosen valuation branch.
-/
def chapter05RamificationGroupInG
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ) : Subgroup (Gal(E / F)) :=
  (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
    F A n).map (Subgroup.subtype _)

/- SOURCE_ISSUE: With the convention `G_u = G_(ceil u)` for `u > 0` and
   `G_i = {σ | i_G(σ) ≥ i+1}`, the indicator of membership in `G_t` has
   integral `i_G(γ)-1` for an inertial nonidentity element, not `i_G(γ)`.
   The corrected bridge below uses the shifted quantity explicitly. -/
noncomputable def chapter05DisplacementIndicatorIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (σ : G) : ℝ :=
  by
    classical
    exact ∫ t in Set.Ioi (0 : ℝ), (if σ ∈ D.lowerGroup t then (1 : ℝ) else 0)

theorem chapter05_displacement_integral_identity
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (σ : G) (hσ : σ ≠ 1)
    (hinertial : 1 ≤ D.displacement σ) :
    ((D.displacement σ - 1 : ℕ) : ℝ) =
      chapter05DisplacementIndicatorIntegral D σ := by
  sorry

theorem chapter05_displacement_integral_identity_noninertial
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (σ : G) (hσ : σ ≠ 1)
    (hnoninertial : ¬1 ≤ D.displacement σ) :
    (0 : ℝ) = chapter05DisplacementIndicatorIntegral D σ := by
  sorry

/- The real convention has a separate, prescribed jump at zero: the negative
   interval is the full group while the value at zero is inertia. -/
theorem chapter05_lower_group_neg_one_eq_top
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    D.lowerGroup (-1 : ℝ) = ⊤ := by
  sorry

theorem chapter05_lower_filtration_left_continuous_on_positive
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter05LeftContinuousOnPositive D.lowerGroup := by
  sorry

/-- The Herbrand integrand is the reciprocal of the corresponding subgroup index. -/
theorem chapter05_herbrand_slope_eq_reciprocal_index
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) (hu : 0 < u)
    (n : ℕ)
    (hindex : Nat.card (D.lowerGroup 0) =
      n * Nat.card (D.lowerGroup u)) :
    chapter05HerbrandSlope D u = (n : ℝ)⁻¹ := by
  sorry

/-- The Herbrand function is a strictly increasing homeomorphism of the index line. -/
theorem chapter05_herbrand_bijective
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D) volume a b) :
    Function.Bijective (chapter05HerbrandFunction D) := by
  sorry

/-- Under bijectivity, the inverse really is a two-sided inverse. -/
theorem chapter05_herbrand_inverse_spec
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) (v : ℝ) :
    chapter05HerbrandFunction D (chapter05HerbrandInverse D v) = v := by
  sorry

/-!
 The defining upper-numbering identities.  The `hbij` argument is kept
 explicit because `chapter05HerbrandInverse` is defined with `Function.invFun`
 so that statements can be drafted before the analytic bijectivity proof.
-/
theorem chapter05_upper_group_eq_lower_at_inverse
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup D v =
      D.lowerGroup (chapter05HerbrandInverse D v) := by
  sorry

theorem chapter05_upper_group_neg_one_eq_top
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperRamificationGroup D (-1 : ℝ) = ⊤ := by
  sorry

theorem chapter05_upper_group_zero_eq_lower_zero
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperRamificationGroup D 0 = D.lowerGroup 0 := by
  sorry

theorem chapter05_upper_zero_plus_eq_lower_one
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperZeroPlus D = D.lowerGroup 1 := by
  sorry

theorem chapter05_upper_filtration_left_continuous_on_positive
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05LeftContinuousOnPositive (chapter05UpperRamificationGroup D) := by
  sorry

theorem chapter05_upper_filtration_antitone
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    Antitone (chapter05UpperRamificationGroup D) := by
  sorry

theorem chapter05_upper_group_normal
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) (v : ℝ) :
    (chapter05UpperRamificationGroup D v).Normal := by
  sorry

theorem chapter05_lower_break_maps_to_upper_break
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (m : ℕ) (hm : chapter05LowerBreak D m) :
    chapter05UpperBreak D (chapter05HerbrandFunction D (m : ℝ)) := by
  sorry

theorem chapter05_upper_breaks_finite
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    (chapter05UpperBreakSet D).Finite := by
  sorry

theorem chapter05_upper_break_is_rational
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    {v : ℝ} (hv : chapter05UpperBreak D v) :
    chapter05UpperBreakIsRational v := by
  sorry

theorem chapter05_first_positive_upper_break_exists
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hwild : D.lowerGroup 1 ≠ ⊥) :
    ∃ r : ℝ, 0 < r ∧ chapter05UpperBreak D r ∧
      ∀ s : ℝ, 0 < s → chapter05UpperBreak D s → r ≤ s := by
  sorry

/-- The first congruence group is inertia in the canonical Book 2 realization. -/
theorem chapter05_canonical_first_group_eq_inertia
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroupInG A 1 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG
        F A := by
  sorry

/-- The zeroth canonical group is the ambient decomposition group. -/
theorem chapter05_canonical_zero_group_eq_decomposition
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroupInG A 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F A := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter05
