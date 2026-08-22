import LastLib.Book05LocalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open scoped BigOperators Pointwise

/-! ## 8.3. Why higher unit groups require upper numbering -/

/- The source's uniformizer formula is stated for automorphisms in inertia.  The
  all-integral-elements minimum below is the canonical definition in general;
  the theorem that follows specializes to a totally ramified branch. -/

theorem chapter08_uniformizer_displacement_eq_integral_of_total_ramification
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (πL : L) (hπ : X.valuation πL = 1)
    (htr : X.residueDegree = 1)
    {σ : Gal(L / K)} (hσ : σ ≠ 1) :
    chapter08GaloisUniformizerDisplacementIndex X.valuation πL σ =
      chapter08IntegralDisplacementIndex X.valuation σ.toRingEquiv := by
  sorry

theorem chapter08_lower_group_neg_one
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) :
    chapter08LowerGroup F (-1 : ℝ) = ⊤ := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_lower_group_neg_one_eq_top F

theorem chapter08_lower_group_nonintegral_convention
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) (m : ℕ) {t : ℝ}
    (hm : (m : ℝ) < t) (hm' : t ≤ (m + 1 : ℕ)) :
    chapter08LowerGroup F t = chapter08LowerGroup F (m + 1 : ℕ) :=
  F.lower_real_convention m t hm hm'

theorem chapter08_lower_group_at_integer
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) (m : ℕ) :
    chapter08LowerGroup F (m : ℝ) = F.lowerGroup (m : ℝ) := by
  rfl

theorem chapter08_lower_numbering_restricts_to_subgroups
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : LastLib.Book03RamificationTheory.Chapter05.Chapter05HerbrandTowerSetup
      G H) {u : ℝ} (hu : (-1 : ℝ) ≤ u) :
    chapter08LowerGroup T.subextension u =
      (chapter08LowerGroup T.quotientSetup.upstairs u).comap
        (Subgroup.subtype H) := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_lower_subgroup_formula
    H T hu

theorem chapter08_lower_group_mem_iff
    {G : Type*} [Group G] [Finite G]
    (D : Chapter08LowerNumberingData G) {σ : G} (hσ : σ ≠ 1)
    (n : ℕ) :
    σ ∈ chapter08IntegerLowerGroup D n ↔
      (n : WithTop ℤ) + 1 ≤ D.displacementIndex σ :=
  D.lower_mem_iff hσ n

@[ext]
theorem Chapter08LowerNumberingData.ext
    {G : Type*} [Group G] [Finite G]
    {D D' : Chapter08LowerNumberingData G}
    (hfiltration : D.filtration = D'.filtration)
    (hdisplacement : D.displacementIndex = D'.displacementIndex) :
    D = D' := by
  cases D
  cases D'
  cases hfiltration
  cases hdisplacement
  rfl

theorem chapter08_lower_group_is_antitone
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) :
    Antitone (chapter08LowerGroup F) :=
  F.lower_antitone

theorem chapter08_lower_group_is_normal
    {G : Type*} [Group G] [Finite G] (F : Chapter08RamificationFiltration G)
    (t : ℝ) : (chapter08LowerGroup F t).Normal :=
  F.lower_normal t

theorem chapter08_lower_filtration_eventually_trivial
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      chapter08LowerGroup F (m : ℝ) = ⊥ := by
  exact F.lower_eventually_trivial

theorem chapter08_herbrand_function_integral_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) {u : ℝ} (hu : 0 ≤ u) :
    chapter08HerbrandFunction F u =
      ∫ t in (0 : ℝ)..u,
        ((chapter08LowerGroup F t).relIndex
          (chapter08LowerGroup F 0) : ℝ)⁻¹ := by
  sorry

theorem chapter08_herbrand_function_is_continuous_increasing_piecewise_linear
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) :
    ContinuousOn (chapter08HerbrandFunction F) (Set.Ici (-1 : ℝ)) ∧
      StrictMonoOn (chapter08HerbrandFunction F) (Set.Ici (-1 : ℝ)) ∧
      (∀ m : ℕ, ∀ {u v : ℝ},
        (m : ℝ) ≤ u → u ≤ (m + 1 : ℕ) →
        (m : ℝ) ≤ v → v ≤ (m + 1 : ℕ) →
        chapter08HerbrandFunction F u - chapter08HerbrandFunction F v =
          (u - v) *
            ((Nat.card (chapter08LowerGroup F (m + 1 : ℕ)) : ℝ) /
              Nat.card (chapter08LowerGroup F 0))) := by
  sorry

theorem chapter08_herbrand_function_bijective
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (_hintegrable : ∀ a b : ℝ,
      IntervalIntegrable
        (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandSlope F)
        MeasureTheory.volume a b) :
    Function.Bijective (chapter08HerbrandFunction F) := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_bijective
    F

theorem chapter08_herbrand_inverse_left_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F))
    {u : ℝ} (hu : -1 ≤ u) :
    chapter08HerbrandInverse F (chapter08HerbrandFunction F u) = u := by
  sorry

theorem chapter08_herbrand_inverse_right_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F))
    {u : ℝ} (hu : -1 ≤ u) :
    chapter08HerbrandFunction F (chapter08HerbrandInverse F u) = u := by
  sorry

theorem chapter08_upper_group_eq_lower_at_herbrand_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter08UpperGroup F v =
      chapter08LowerGroup F (chapter08HerbrandInverse F v) := by
  sorry

theorem chapter08_upper_group_neg_one_eq_group
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F)) :
    chapter08UpperGroup F (-1 : ℝ) = ⊤ := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_group_neg_one_eq_top
    F hbij

theorem chapter08_upper_group_zero_eq_inertia
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F)) :
    chapter08UpperGroup F 0 = chapter08InertiaGroup F := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_group_zero_eq_lower_zero
    F hbij

theorem chapter08_upper_zero_plus_eq_wild_inertia
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F)) :
    chapter08WildInertia F = chapter08LowerGroup F 1 := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_zero_plus_eq_lower_one
    F hbij

def chapter08UpperQuotientImage
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (F : Chapter08RamificationFiltration G) (v : ℝ) :
    Subgroup (G ⧸ H) :=
  (chapter08UpperGroup F v).map (QuotientGroup.mk' H)

theorem chapter08_upper_group_quotient_compatibility
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : LastLib.Book03RamificationTheory.Chapter05.Chapter05QuotientRamificationSetup
      G H)
    (_hup : Function.Bijective (chapter08HerbrandFunction S.upstairs))
    (_hdown : Function.Bijective (chapter08HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter08UpperGroup S.downstairs v =
      chapter08UpperQuotientImage H S.upstairs v := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_quotient_theorem
    H S hv

theorem chapter08_upper_group_quotient_membership_iff
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : LastLib.Book03RamificationTheory.Chapter05.Chapter05QuotientRamificationSetup
      G H)
    (_hup : Function.Bijective (chapter08HerbrandFunction S.upstairs))
    (_hdown : Function.Bijective (chapter08HerbrandFunction S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) (σ : G) :
    QuotientGroup.mk' H σ ∈ chapter08UpperGroup S.downstairs v ↔
      ∃ τ : H, σ * (τ : G) ∈ chapter08UpperGroup S.upstairs v := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_quotient_membership_iff
    H S hv σ

theorem chapter08_upper_filtration_is_antitone
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (hbij : Function.Bijective (chapter08HerbrandFunction F)) :
    Antitone (chapter08UpperGroup F) := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_filtration_antitone
    F hbij

theorem chapter08_upper_group_is_normal
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G)
    (_hbij : Function.Bijective (chapter08HerbrandFunction F)) (v : ℝ) :
    (chapter08UpperGroup F v).Normal := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_upper_group_normal
    F v

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
