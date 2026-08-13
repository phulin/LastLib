import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped BigOperators ComplexConjugate NumberField nonZeroDivisors Classical

/-! ### 4.2. Theta kernels and dual lattices -/

theorem chapter04_self_dual_covolume_pos
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    0 < chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K) := by
  sorry

theorem chapter04_ordinary_covolume_unchanged
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    ZLattice.covolume (E := chapter04MinkowskiSpace K)
      (chapter02FractionalIdealLattice K a) =
      chapter04FractionalIdealNorm K (a : Chapter04FractionalIdeal K) *
        (2 : ℝ)⁻¹ ^ chapter04ComplexPlaces K *
          Real.sqrt (chapter04AbsoluteDiscriminant K) := by
  exact chapter02_fractional_ideal_lattice_covolume K a

theorem chapter04_self_dual_covolume_eq_rescaled_ordinary
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K) =
      (2 : ℝ) ^ chapter04ComplexPlaces K *
        ZLattice.covolume (E := chapter04MinkowskiSpace K)
          (chapter02FractionalIdealLattice K a) := by
  sorry

/- The normalization is exposed as a lattice interface because the canonical
   mixed-space ideal lattice is a submodule, while its real scalar multiple is
   most naturally presented in the source as a set. -/
theorem chapter04_normalized_ideal_lattice_covolume_one
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    ∃ L : Submodule ℤ (chapter04MinkowskiSpace K),
        ∃ hL : DiscreteTopology L,
        @IsZLattice ℝ _ (chapter04MinkowskiSpace K) _ _ L hL ∧
          (L : Set (chapter04MinkowskiSpace K)) =
            chapter04NormalizedIdealLattice K (a : Chapter04FractionalIdeal K) ∧
          chapter04SelfDualLatticeCovolume K L = 1 := by
  sorry

theorem chapter04_normalized_lattice_dual_eq_coordinate_conjugate_dual_ideal
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) :
    chapter04LatticeDual K
        (chapter04NormalizedIdealLattice K (a : Chapter04FractionalIdeal K)) =
      chapter04CoordinateConjugation K ''
        chapter04NormalizedIdealLattice K
          (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) := by
  sorry

theorem chapter04_orbit_ideal_class
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) {x₀ : K}
    (hx₀ : x₀ ∈ (a : Set K)) (hx₀_ne : x₀ ≠ 0) :
    ∃ J : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 J = (ClassGroup.mk K a)⁻¹ ∧
        (J : Chapter04FractionalIdeal K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ *
            (a : Chapter04FractionalIdeal K)⁻¹ := by
  sorry

noncomputable def chapter04NormalizedArchimedeanProduct
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) (x₀ : K) : ℝ :=
  (chapter04SelfDualCovolume K (a : Chapter04FractionalIdeal K))⁻¹ *
    |Algebra.norm ℚ x₀|

theorem chapter04_normalized_archimedean_product_formula
    (K : Type*) [Field K] [NumberField K]
    (a : Chapter04NonzeroFractionalIdeal K) (x₀ : K) :
    chapter04NormalizedArchimedeanProduct K a x₀ =
      (Real.sqrt (chapter04AbsoluteDiscriminant K))⁻¹ *
        (chapter04FractionalIdealNorm K (a : Chapter04FractionalIdeal K))⁻¹ *
          |Algebra.norm ℚ x₀| := by
  sorry

theorem chapter04_theta_series_and_derivatives_locally_uniform
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    chapter04ThetaSeriesAndDerivativeLocallyUniform K a := by
  sorry

theorem chapter04_theta_poisson_summation
    (K : Type*) [Field K] [NumberField K]
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0)
    {t : ℝ} (ht : 0 < t) (y : chapter04Y K) :
    chapter04Theta K a t y =
      t⁻¹ * chapter04Theta K (chapter04DualFractionalIdeal K a) t⁻¹
        (chapter04YInv K y) := by
  sorry

theorem chapter04_unit_log_lattice_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter04UnitLogLattice K) := by
  sorry

attribute [instance] chapter04_unit_log_lattice_discrete

theorem chapter04_unit_log_lattice_is_full
    (K : Type*) [Field K] [NumberField K] :
    IsZLattice ℝ (chapter04UnitLogLattice K) := by
  sorry

theorem chapter04_unit_log_lattice_span_eq_top
    (K : Type*) [Field K] [NumberField K] :
    Submodule.span ℝ (chapter04UnitLogLattice K :
      Set (chapter04UnitLogHyperplane K)) = ⊤ := by
  sorry

theorem chapter04_exists_unit_fundamental_domain
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter04UnitFundamentalDomain K) := by
  sorry

theorem chapter04_unit_fundamental_domain_normalized
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    D.measure D.carrier = 1 := by
  exact D.normalized_volume

/- The source leaves the positive orbit constant dependent on the chosen Haar
   normalization.  Record its existence for the selected normalized domain,
   then choose it for the continuation. -/
theorem chapter04_theta_mellin_constant_exists
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (a : Chapter04NonzeroFractionalIdeal K) {s : ℂ}, 1 < s.re →
        chapter04ThetaMellinIntegral K D
            (a : Chapter04FractionalIdeal K) s =
          (c : ℂ) *
            (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
              chapter04ArchimedeanFactor K s *
                chapter04PartialZeta K (chapter04InverseIdealClass K a) s := by
  sorry

noncomputable def chapter04MellinConstant
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) : ℝ :=
  Classical.choose (chapter04_theta_mellin_constant_exists K D)

theorem chapter04_mellin_constant_pos
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    0 < chapter04MellinConstant K D := by
  exact (Classical.choose_spec (chapter04_theta_mellin_constant_exists K D)).1

theorem chapter04_mellin_constant_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) :
    chapter04MellinConstant K D ≠ 0 :=
  (chapter04_mellin_constant_pos K D).ne'

theorem chapter04_theta_mellin_eq_completed_partial_zeta
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K)
    {s : ℂ} (hs : 1 < s.re) :
    chapter04ThetaMellinIntegral K D (a : Chapter04FractionalIdeal K) s =
      (chapter04MellinConstant K D : ℂ) *
        (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
          chapter04ArchimedeanFactor K s *
            chapter04PartialZeta K (chapter04InverseIdealClass K a) s := by
  exact (Classical.choose_spec (chapter04_theta_mellin_constant_exists K D)).2 a hs

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
