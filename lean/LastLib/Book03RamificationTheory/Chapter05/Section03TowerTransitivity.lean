import LastLib.Book03RamificationTheory.Chapter05.Section02HerbrandsQuotientTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped Topology

/-! ## 5.3. Tower transitivity -/

/--
 A group-theoretic profile for a Galois tower.  The subgroup profile is the
 lower filtration on `L/M`; its lower groups are required to be the
 restrictions of the top profile.  The quotient setup supplies the
 displacement identity needed for the `M/K` stage.
-/
structure Chapter05HerbrandTowerSetup
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  quotientSetup : Chapter05QuotientRamificationSetup G H
  subextension : Chapter05RamificationFiltration H
  subgroup_lower_formula :
    ∀ u : ℝ, (-1 : ℝ) ≤ u →
      subextension.lowerGroup u =
        (quotientSetup.upstairs.lowerGroup u).comap (Subgroup.subtype H)

namespace Chapter05HerbrandTowerSetup

variable {G : Type*} [Group G] [Fintype G]
variable (H : Subgroup G) [H.Normal]

theorem lower_subgroup_formula
    (T : Chapter05HerbrandTowerSetup G H) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) :
    T.subextension.lowerGroup u =
      (T.quotientSetup.upstairs.lowerGroup u).comap (Subgroup.subtype H) := by
  exact T.subgroup_lower_formula u hu

end Chapter05HerbrandTowerSetup

/-- Lower numbering is functorial for the subgroup stage of the tower. -/
theorem chapter05_lower_subgroup_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) :
    T.subextension.lowerGroup u =
      (T.quotientSetup.upstairs.lowerGroup u).comap (Subgroup.subtype H) := by
  exact T.subgroup_lower_formula u hu

private theorem chapter05_comap_subtype_card
    {G : Type*} [Group G] [Fintype G]
    (H K : Subgroup G) :
    Nat.card (K.comap H.subtype) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [Subgroup.comap_subtype]
  exact Nat.card_congr
    { toFun := fun x =>
        ⟨(x : G), And.intro x.1.property x.property⟩
      invFun := fun y =>
        ⟨⟨(y : G), y.property.1⟩, y.property.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro y
        rfl }

private theorem chapter05_lower_mem_iff_real
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) {σ : G} (hσ : σ ≠ 1)
    {t : ℝ} (ht : 0 < t) :
    σ ∈ D.lowerGroup t ↔
      t ≤ ((D.displacement σ - 1 : ℕ) : ℝ) := by
  let d : ℕ := D.displacement σ
  by_cases hnat : ∃ n : ℕ, t = (n : ℝ)
  · obtain ⟨n, rfl⟩ := hnat
    rw [D.lower_nat_mem_iff hσ n]
    have hnpos : 0 < n := by exact_mod_cast ht
    constructor
    · intro h
      have hn : n ≤ d - 1 := by
        dsimp [d]
        omega
      exact_mod_cast hn
    · intro h
      have hn : n ≤ d - 1 := by
        exact_mod_cast h
      dsimp [d] at hn
      have hn' : n + 1 ≤ D.displacement σ := by omega
      simpa [d] using hn'
  · let n : ℕ := ⌊t⌋₊
    have ht_nonneg : 0 ≤ t := le_of_lt ht
    have hn_le : (n : ℝ) ≤ t := by
      exact Nat.floor_le ht_nonneg
    have hn_lt : (n : ℝ) < t := by
      exact lt_of_le_of_ne hn_le (Ne.symm (by
        intro h
        apply hnat
        exact ⟨n, h⟩))
    have ht_upper : t ≤ ((n + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, n] using
        (Nat.lt_floor_add_one t).le
    rw [D.lower_real_convention n t hn_lt ht_upper,
      D.lower_nat_mem_iff hσ (n + 1)]
    have ht_upper' : t ≤ (n : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using ht_upper
    constructor
    · intro h
      have hd : n + 2 ≤ d := by
        dsimp [d]
        exact h
      have hd_one : 1 ≤ d := by omega
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hd_one]
        norm_num
      have hd_real : (n : ℝ) + 2 ≤ (d : ℝ) := by
        exact_mod_cast hd
      rw [hcast]
      linarith
    · intro h
      by_contra hnot
      have hd : d ≤ n + 1 := by
        dsimp [d] at h ⊢
        omega
      have hd_real : (d : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast hd
      have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) hn_lt
      have h' : t ≤ ((d - 1 : ℕ) : ℝ) := by
        simpa [d] using h
      have hd_one : 1 ≤ d := by
        by_contra hd0
        have hdzero : d = 0 := Nat.eq_zero_of_not_pos hd0
        rw [hdzero] at h'
        norm_num at h'
        linarith
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hd_one]
        norm_num
      rw [hcast] at h
      linarith

private theorem chapter05_map_card_mul_inf_kernel
    {G G' : Type*} [Group G] [Group G'] [Fintype G]
    (f : G →* G') (K : Subgroup G) :
    Nat.card (K.map f) * Nat.card (K ⊓ f.ker : Subgroup G) = Nat.card K := by
  have hcard := Subgroup.card_mul_index
    ((K ⊓ f.ker).subgroupOf K)
  have hindex : ((K ⊓ f.ker).subgroupOf K).index =
      Nat.card (K.map f) := by
    change (K ⊓ f.ker).relIndex K = Nat.card (K.map f)
    rw [inf_comm K f.ker, Subgroup.inf_relIndex_right, Subgroup.relIndex_ker]
  have hker_card :
      Nat.card ((K ⊓ f.ker).subgroupOf K) =
        Nat.card (K ⊓ f.ker : Subgroup G) := by
    calc
      Nat.card ((K ⊓ f.ker).subgroupOf K) =
          Nat.card (((K ⊓ f.ker).subgroupOf K).map K.subtype) :=
        (Subgroup.card_subtype K ((K ⊓ f.ker).subgroupOf K)).symm
      _ = Nat.card (K ⊓ f.ker : Subgroup G) := by
        rw [Subgroup.subgroupOf_map_subtype]
        rw [inf_eq_left.mpr inf_le_left]
  rw [hindex] at hcard
  rw [hker_card] at hcard
  simpa [Nat.mul_comm] using hcard

private theorem chapter05_herbrand_slope_interval_integrable
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (a b : ℝ) :
    IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume a b := by
  have hpiece : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        (j : ℝ) ((j + 1 : ℕ) : ℝ) := by
    intro j
    have hconst : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ =>
          (Nat.card (D.lowerGroup (j + 1 : ℕ)) : ℝ) /
            Nat.card (D.lowerGroup 0))
        (Set.uIoo (j : ℝ) ((j + 1 : ℕ) : ℝ)) := by
      intro t ht
      have ht' : (j : ℝ) < t ∧ t < ((j + 1 : ℕ) : ℝ) := by
        simpa [Set.uIoo_of_le (by norm_num :
          (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ))] using ht
      have ht0 : ¬t ≤ 0 := by
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      rw [chapter05HerbrandSlope, if_neg ht0]
      rw [D.lower_real_convention j t ht'.1 ht'.2.le]
    exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hnat : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        0 (j : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have htrans := ih.trans (hpiece j)
        simpa [Nat.cast_add, Nat.cast_one] using htrans
  have hneg : ∀ x y : ℝ, x ≤ 0 → y ≤ 0 →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo x y) := by
        intro t ht
        have ht' : x < t ∧ t < y := by
          simpa [Set.uIoo_of_le hxy] using ht
        rw [chapter05HerbrandSlope, if_pos (le_trans ht'.2.le hy)]
      exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
    · have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo x y) := by
        intro t ht
        have ht' : y < t ∧ t < x := by
          simpa [Set.uIoo_of_ge hyx] using ht
        rw [chapter05HerbrandSlope, if_pos (le_trans ht'.2.le hx)]
      exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hpos : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume x y := by
    intro x y hx hxy
    obtain ⟨N, hN⟩ := exists_nat_ge y
    have h0N : (0 : ℝ) ≤ (N : ℝ) := le_trans hx (hxy.trans hN)
    apply (hnat N).mono_set
    intro t ht
    have htab : t ∈ Set.Icc x y := by
      simpa [Set.uIcc_of_le hxy] using ht
    have ht0N : t ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      exact ⟨le_trans hx htab.1, le_trans htab.2 hN⟩
    simpa [Set.uIcc_of_le h0N] using ht0N
  have hle : ∀ {x y : ℝ}, x ≤ y →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume x y := by
    intro x y hxy
    by_cases hy : y ≤ 0
    · exact hneg x y (hxy.trans hy) hy
    · have hy' : 0 ≤ y := le_of_not_ge hy
      by_cases hx : x ≤ 0
      · exact (hneg x 0 hx le_rfl).trans (hpos (x := 0) (y := y) le_rfl hy')
      · exact hpos (x := x) (y := y) (le_of_not_ge hx) hxy
  rcases le_total a b with hab | hba
  · exact hle hab
  · exact (hle hba).symm

private theorem chapter05_herbrand_function_sub_eq_integral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    chapter05HerbrandFunction D b - chapter05HerbrandFunction D a =
      ∫ t in a..b, chapter05HerbrandSlope D t := by
  have hFa : chapter05HerbrandFunction D a =
      ∫ t in (0 : ℝ)..a, chapter05HerbrandSlope D t := by
    by_cases ha0 : a = 0
    · subst a
      simp [chapter05HerbrandFunction]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      rw [chapter05HerbrandFunction, if_neg (not_le.mpr ha_pos)]
  have hFb : chapter05HerbrandFunction D b =
      ∫ t in (0 : ℝ)..b, chapter05HerbrandSlope D t := by
    by_cases hb0 : b = 0
    · subst b
      simp [chapter05HerbrandFunction]
    · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      rw [chapter05HerbrandFunction, if_neg (not_le.mpr hb_pos)]
  rw [hFb, hFa]
  exact intervalIntegral.integral_interval_sub_left
    (chapter05_herbrand_slope_interval_integrable D 0 b)
    (chapter05_herbrand_slope_interval_integrable D 0 a)

/-!
 The analytic transitivity formulas.  In the field interpretation the three
 profiles are attached to `L/K`, `L/M`, and `M/K`, respectively.
-/
theorem chapter05_herbrand_tower_transitivity
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H)
    (hLM : Function.Bijective
      (chapter05HerbrandFunction T.subextension))
    {u : ℝ} :
    chapter05HerbrandFunction T.quotientSetup.upstairs u =
      chapter05HerbrandFunction T.quotientSetup.downstairs
        (chapter05HerbrandFunction T.subextension u) := by
  classical
  have hsub_card (m : ℕ) :
      Nat.card (T.subextension.lowerGroup (m : ℝ)) =
        Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup (m : ℝ) :
          Subgroup G) := by
    calc
      Nat.card (T.subextension.lowerGroup (m : ℝ)) =
          Nat.card ((T.quotientSetup.upstairs.lowerGroup (m : ℝ)).comap
            H.subtype) := by
        rw [T.subgroup_lower_formula (m : ℝ) (by
          have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
          linarith)]
      _ = Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup (m : ℝ) :
          Subgroup G) := chapter05_comap_subtype_card H _
  have hsub_card0 : Nat.card (T.subextension.lowerGroup 0) =
      T.quotientSetup.eLM := by
    calc
      Nat.card (T.subextension.lowerGroup 0) =
          Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup 0 :
            Subgroup G) := by simpa using hsub_card 0
      _ = T.quotientSetup.eLM :=
        T.quotientSetup.eLM_eq_inertia_card.symm
  have hFsub_nat (m : ℕ) :
      chapter05HerbrandFunction T.subextension (m : ℝ) =
        (1 / (T.quotientSetup.eLM : ℝ)) *
          ∑ j ∈ Finset.Icc 1 m,
            (Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup (j : ℝ) :
              Subgroup G) : ℝ) := by
    rw [chapter05_herbrand_function_interval_formula T.subextension m
      le_rfl (by norm_num)]
    have hsum :
        (∑ j ∈ Finset.Icc 1 m,
          (Nat.card (T.subextension.lowerGroup (j : ℝ)) : ℝ)) =
          ∑ j ∈ Finset.Icc 1 m,
            (Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup (j : ℝ) :
              Subgroup G) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsub_card j]
    simp only [sub_self, hsum, hsub_card0]
    ring
  have hcoset_max (σ : G) :
      ∃ n : ℕ,
        (∀ τ : H,
          T.quotientSetup.upstairs.displacement (σ * (τ : G)) ≤ n) ∧
        (∃ τ : H,
          T.quotientSetup.upstairs.displacement (σ * (τ : G)) = n) := by
    let U : Finset ℕ := Finset.univ.image (fun τ : H =>
      T.quotientSetup.upstairs.displacement (σ * (τ : G)))
    have hUne : U.Nonempty := by
      refine ⟨T.quotientSetup.upstairs.displacement (σ * (1 : H)), ?_⟩
      exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    let n : ℕ := U.max' hUne
    have hnU : n ∈ U := Finset.max'_mem U hUne
    obtain ⟨τ₀, hτ₀, hτ₀eq⟩ := Finset.mem_image.mp hnU
    refine ⟨n, ?_, ⟨τ₀, hτ₀eq⟩⟩
    intro τ
    exact Finset.le_max' U _
      (Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, rfl⟩)
  have hmap_lower (σ : G) (t : ℝ) :
      chapter05QuotientMap H σ ∈
          (T.quotientSetup.upstairs.lowerGroup t).map
          (chapter05QuotientMap H) ↔
        ∃ τ : H, σ * (τ : G) ∈
          T.quotientSetup.upstairs.lowerGroup t := by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, hq⟩
      let τ : G := σ⁻¹ * g
      have hτ : τ ∈ H := by
        apply (QuotientGroup.eq_one_iff _).mp
        change chapter05QuotientMap H τ = 1
        dsimp [τ]
        rw [map_mul, map_inv]
        rw [← hq]
        simp
      refine ⟨⟨τ, hτ⟩, ?_⟩
      simpa [τ] using hg
    · rintro ⟨τ, hτ⟩
      refine ⟨σ * (τ : G), hτ, ?_⟩
      rw [map_mul]
      have hτq : chapter05QuotientMap H (τ : G) = 1 :=
        (QuotientGroup.eq_one_iff _).2 τ.property
      simp [hτq]
  have hlower_image {σ : G} {t : ℝ} (ht : 0 < t) :
      chapter05QuotientMap H σ ∈
          T.quotientSetup.downstairs.lowerGroup
            (chapter05HerbrandFunction T.subextension t) ↔
        chapter05QuotientMap H σ ∈
          (T.quotientSetup.upstairs.lowerGroup t).map
            (chapter05QuotientMap H) := by
    obtain ⟨n, hn_upper, hn_attained⟩ := hcoset_max σ
    by_cases hq1 : chapter05QuotientMap H σ = 1
    · simp [hq1]
    · have hσ : σ ∉ H := by
        intro hσH
        apply hq1
        exact (QuotientGroup.eq_one_iff _).2 hσH
      have hcoset_ne_one : ∀ τ : H, σ * (τ : G) ≠ 1 := by
        intro τ hτ
        apply hσ
        rw [eq_inv_of_mul_eq_one_left hτ]
        exact H.inv_mem τ.property
      have hmax_iff :
          (∃ τ : H, σ * (τ : G) ∈
            T.quotientSetup.upstairs.lowerGroup t) ↔
            t ≤ ((n - 1 : ℕ) : ℝ) := by
        constructor
        · rintro ⟨τ, hτ⟩
          have hmem :=
            (chapter05_lower_mem_iff_real
              T.quotientSetup.upstairs (hcoset_ne_one τ) ht).mp hτ
          have hsub :
              T.quotientSetup.upstairs.displacement (σ * (τ : G)) - 1 ≤
                n - 1 := by
            exact Nat.sub_le_sub_right (hn_upper τ) 1
          have hsub' :
              ((T.quotientSetup.upstairs.displacement
                (σ * (τ : G)) - 1 : ℕ) : ℝ) ≤
                ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast hsub
          linarith
        · intro htn
          obtain ⟨τ₀, hτ₀⟩ := hn_attained
          have hmem :
              t ≤ ((T.quotientSetup.upstairs.displacement
                (σ * (τ₀ : G)) - 1 : ℕ) : ℝ) := by
            simpa [hτ₀] using htn
          exact ⟨τ₀,
            (chapter05_lower_mem_iff_real
              T.quotientSetup.upstairs (hcoset_ne_one τ₀) ht).mpr hmem⟩
      have hFsub_pos : 0 <
          chapter05HerbrandFunction T.subextension t := by
        have hmono : StrictMonoOn
            (chapter05HerbrandFunction T.subextension)
            (Set.Ici (-1 : ℝ)) :=
          (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
            T.subextension).2.1
        have hstrict :
            chapter05HerbrandFunction T.subextension 0 <
              chapter05HerbrandFunction T.subextension t := by
          apply hmono
          · norm_num
          · change (-1 : ℝ) ≤ t
            linarith
          · exact ht
        simpa [chapter05_herbrand_function_zero T.subextension] using hstrict
      rw [chapter05_lower_mem_iff_real T.quotientSetup.downstairs
        hq1 hFsub_pos, hmap_lower σ t]
      by_cases hn0 : n = 0
      · have hallzero : ∀ τ : H,
            T.quotientSetup.upstairs.displacement (σ * (τ : G)) = 0 := by
          intro τ
          have := hn_upper τ
          omega
        have hsumzero :
            (∑ τ : H,
              T.quotientSetup.upstairs.displacement (σ * (τ : G))) = 0 := by
          simp [hallzero]
        have hdisp := chapter05_coset_displacement_identity_integral_form
          H T.quotientSetup (σ := σ) hσ
        have hdzero :
            T.quotientSetup.downstairs.displacement
              (chapter05QuotientMap H σ) = 0 := by
          have : T.quotientSetup.eLM *
              T.quotientSetup.downstairs.displacement
                (chapter05QuotientMap H σ) = 0 := by
            rw [hdisp]
            exact hsumzero
          have hepos : 0 < T.quotientSetup.eLM :=
            T.quotientSetup.eLM_pos
          exact (Nat.mul_eq_zero.mp this).resolve_left
            (Nat.ne_of_gt hepos)
        constructor
        · intro h
          exfalso
          rw [hdzero] at h
          norm_num at h
          exact (not_lt_of_ge h) hFsub_pos
        · intro h
          rw [hdzero]
          have htn := hmax_iff.mp h
          rw [hn0] at htn
          norm_num at htn
          exfalso
          linarith
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_attained' := hn_attained
        obtain ⟨τ₀, hτ₀⟩ := hn_attained
        have hsum_ge :
            T.quotientSetup.upstairs.displacement (σ * (τ₀ : G)) ≤
              ∑ τ : H,
                T.quotientSetup.upstairs.displacement (σ * (τ : G)) := by
          simpa using (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun τ : H =>
              T.quotientSetup.upstairs.displacement (σ * (τ : G)))
            (a := τ₀)
            (fun τ _ => Nat.zero_le _) (Finset.mem_univ τ₀))
        have hsum_pos : 0 <
            ∑ τ : H,
              T.quotientSetup.upstairs.displacement (σ * (τ : G)) := by
          rw [hτ₀] at hsum_ge
          exact lt_of_lt_of_le hnpos hsum_ge
        have hdisp := chapter05_coset_displacement_identity_integral_form
          H T.quotientSetup (σ := σ) hσ
        have hdpos : 0 <
            T.quotientSetup.downstairs.displacement
              (chapter05QuotientMap H σ) := by
          have hprod : 0 < T.quotientSetup.eLM *
              T.quotientSetup.downstairs.displacement
                (chapter05QuotientMap H σ) := by
            rw [hdisp]
            exact hsum_pos
          have hepos : 0 < T.quotientSetup.eLM :=
            T.quotientSetup.eLM_pos
          by_contra hdnot
          have hdzero :
              T.quotientSetup.downstairs.displacement
                (chapter05QuotientMap H σ) = 0 :=
            Nat.eq_zero_of_not_pos hdnot
          rw [hdzero] at hprod
          norm_num at hprod
        have hthreshold := chapter05_coset_threshold_identity
          H T.quotientSetup hσ n hn_upper hn_attained' (by omega)
        have hthreshold_real :
            ((T.quotientSetup.downstairs.displacement
              (chapter05QuotientMap H σ) - 1 : ℕ) : ℝ) =
              (1 / (T.quotientSetup.eLM : ℝ)) *
                ∑ j ∈ Finset.Icc 1 (n - 1),
                  (Nat.card (H ⊓
                    T.quotientSetup.upstairs.lowerGroup (j : ℝ) :
                    Subgroup G) : ℝ) := by
          have h := congrArg (fun q : ℚ => (q : ℝ)) hthreshold
          norm_num at h ⊢
          exact h
        have hFthreshold :
            ((T.quotientSetup.downstairs.displacement
              (chapter05QuotientMap H σ) - 1 : ℕ) : ℝ) =
              chapter05HerbrandFunction T.subextension ((n - 1 : ℕ) : ℝ) := by
          rw [hFsub_nat (n - 1)]
          exact hthreshold_real
        have hmono : StrictMonoOn
            (chapter05HerbrandFunction T.subextension)
            (Set.Ici (-1 : ℝ)) :=
          (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
            T.subextension).2.1
        rw [hFthreshold]
        constructor
        · intro h
          apply hmax_iff.mpr
          by_contra hnot
          have hlt : ((n - 1 : ℕ) : ℝ) < t := by
            exact lt_of_not_ge hnot
          have hxdom : ((n - 1 : ℕ) : ℝ) ∈ Set.Ici (-1) := by
            change (-1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ)
            have hxnonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
              exact_mod_cast (Nat.zero_le (n - 1))
            exact le_trans (by norm_num) hxnonneg
          have htdom : t ∈ Set.Ici (-1) := by
            exact le_trans (by norm_num) ht.le
          have hstrict := hmono hxdom
            htdom hlt
          linarith
        · intro h
          have htn := hmax_iff.mp h
          by_cases heq : t = ((n - 1 : ℕ) : ℝ)
          · simp [heq]
          · have hlt : t < ((n - 1 : ℕ) : ℝ) :=
              lt_of_le_of_ne htn heq
            have hxdom : ((n - 1 : ℕ) : ℝ) ∈ Set.Ici (-1) := by
              change (-1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ)
              have hxnonneg : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
                exact_mod_cast (Nat.zero_le (n - 1))
              exact le_trans (by norm_num) hxnonneg
            have htdom : t ∈ Set.Ici (-1) := by
              exact le_trans (by norm_num) ht.le
            have hstrict := hmono
              htdom hxdom hlt
            exact hstrict.le
  have hsub_card_real {t : ℝ} (ht : 0 < t) :
      Nat.card (T.subextension.lowerGroup t) =
        Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup t : Subgroup G) := by
    rw [T.subgroup_lower_formula t (by linarith)]
    exact chapter05_comap_subtype_card H _
  have hgroup_image {t : ℝ} (ht : 0 < t) :
      T.quotientSetup.downstairs.lowerGroup
          (chapter05HerbrandFunction T.subextension t) =
        (T.quotientSetup.upstairs.lowerGroup t).map
          (chapter05QuotientMap H) := by
    ext x
    obtain ⟨σ, rfl⟩ :=
      Chapter05QuotientRamificationSetup.quotient_map_surjective H x
    exact hlower_image ht
  have hcard_mul {t : ℝ} (ht : 0 < t) :
      Nat.card (T.quotientSetup.downstairs.lowerGroup
          (chapter05HerbrandFunction T.subextension t)) *
        Nat.card (T.subextension.lowerGroup t) =
      Nat.card (T.quotientSetup.upstairs.lowerGroup t) := by
    rw [hgroup_image ht]
    have hmap := chapter05_map_card_mul_inf_kernel
      (chapter05QuotientMap H)
      (T.quotientSetup.upstairs.lowerGroup t)
    rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H] at hmap
    calc
      Nat.card ↥((T.quotientSetup.upstairs.lowerGroup t).map
          (chapter05QuotientMap H)) * Nat.card ↥(T.subextension.lowerGroup t) =
          Nat.card ↥((T.quotientSetup.upstairs.lowerGroup t).map
            (chapter05QuotientMap H)) *
            Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup t : Subgroup G) := by
              rw [hsub_card_real ht]
      _ = Nat.card (T.quotientSetup.upstairs.lowerGroup t) := by
        simpa [inf_comm] using hmap
  have hcard_zero :
      Nat.card (T.quotientSetup.downstairs.lowerGroup 0) *
          Nat.card (T.subextension.lowerGroup 0) =
        Nat.card (T.quotientSetup.upstairs.lowerGroup 0) := by
    have hmap := chapter05_map_card_mul_inf_kernel
      (chapter05QuotientMap H)
      (T.quotientSetup.upstairs.lowerGroup 0)
    rw [Chapter05QuotientRamificationSetup.quotient_map_kernel H] at hmap
    calc
      Nat.card (T.quotientSetup.downstairs.lowerGroup 0) *
          Nat.card (T.subextension.lowerGroup 0) =
      Nat.card ((T.quotientSetup.upstairs.lowerGroup 0).map
            (chapter05QuotientMap H)) *
            Nat.card (H ⊓ T.quotientSetup.upstairs.lowerGroup 0 : Subgroup G) := by
              rw [T.quotientSetup.downstairs_lower_zero_eq_inertia_image,
                hsub_card0, T.quotientSetup.eLM_eq_inertia_card]
      _ = Nat.card (T.quotientSetup.upstairs.lowerGroup 0) := by
        simpa [inf_comm] using hmap
  have hsub_pos {t : ℝ} (ht : 0 < t) :
      0 < chapter05HerbrandFunction T.subextension t := by
    have hmono : MonotoneOn
        (chapter05HerbrandFunction T.subextension)
        (Set.Ici (-1 : ℝ)) :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        T.subextension).2.1.monotoneOn
    have hle : chapter05HerbrandFunction T.subextension 0 ≤
        chapter05HerbrandFunction T.subextension t := by
      apply hmono
      · norm_num
      · change (-1 : ℝ) ≤ t
        linarith
      · exact ht.le
    have hne : chapter05HerbrandFunction T.subextension 0 ≠
        chapter05HerbrandFunction T.subextension t := by
      intro hEq
      exact (ne_of_gt ht) (hLM.1 hEq.symm)
    have hstrict := lt_of_le_of_ne hle hne
    simpa [chapter05_herbrand_function_zero T.subextension] using hstrict
  have hslope_comp {t : ℝ} (ht : 0 < t) :
      chapter05HerbrandSlope T.quotientSetup.downstairs
          (chapter05HerbrandFunction T.subextension t) *
        chapter05HerbrandSlope T.subextension t =
      chapter05HerbrandSlope T.quotientSetup.upstairs t := by
    have hcard := congrArg (fun n : ℕ => (n : ℝ)) (hcard_mul ht)
    have hcard0 := congrArg (fun n : ℕ => (n : ℝ)) hcard_zero
    have hpos_down : 0 < (Nat.card
        (T.quotientSetup.downstairs.lowerGroup
          (chapter05HerbrandFunction T.subextension t)) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_sub : 0 < (Nat.card (T.subextension.lowerGroup t) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_up : 0 < (Nat.card
        (T.quotientSetup.upstairs.lowerGroup t) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_down0 : 0 < (Nat.card
        (T.quotientSetup.downstairs.lowerGroup 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_sub0 : 0 < (Nat.card (T.subextension.lowerGroup 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos_up0 : 0 < (Nat.card
        (T.quotientSetup.upstairs.lowerGroup 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    rw [chapter05HerbrandSlope, if_neg (not_le.mpr (hsub_pos ht)),
      chapter05HerbrandSlope, if_neg (not_le.mpr ht),
      chapter05HerbrandSlope, if_neg (not_le.mpr ht)]
    norm_num at hcard hcard0 ⊢
    field_simp [ne_of_gt hpos_down0, ne_of_gt hpos_sub0,
      ne_of_gt hpos_up0]
    nlinarith
  have hsub_nonneg {t : ℝ} (ht : 0 ≤ t) :
      0 ≤ chapter05HerbrandFunction T.subextension t := by
    have hmono : MonotoneOn
        (chapter05HerbrandFunction T.subextension)
        (Set.Ici (-1 : ℝ)) :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        T.subextension).2.1.monotoneOn
    have hzero : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
    have ht' : t ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ t
      linarith
    have hle := hmono hzero ht' ht
    simpa [chapter05_herbrand_function_zero T.subextension] using hle
  have hsegment : ∀ (m : ℕ) {x : ℝ},
      (m : ℝ) ≤ x → x ≤ ((m + 1 : ℕ) : ℝ) →
      chapter05HerbrandFunction T.quotientSetup.downstairs
          (chapter05HerbrandFunction T.subextension x) -
        chapter05HerbrandFunction T.quotientSetup.downstairs
          (chapter05HerbrandFunction T.subextension (m : ℝ)) =
      chapter05HerbrandFunction T.quotientSetup.upstairs x -
        chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) := by
    intro m x hmx hxnext
    by_cases hxeq : x = (m : ℝ)
    · subst x
      ring
    have hmlt : (m : ℝ) < x := lt_of_le_of_ne hmx (Ne.symm hxeq)
    have hxpos : 0 < x := by
      have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have hm_dom : (m : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ (m : ℝ)
      linarith
    have hx_dom : x ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ x
      linarith
    have hzero_dom : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
    have hmono_sub : MonotoneOn
        (chapter05HerbrandFunction T.subextension)
        (Set.Ici (-1 : ℝ)) :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        T.subextension).2.1.monotoneOn
    have hsub_m_nonneg : 0 ≤
        chapter05HerbrandFunction T.subextension (m : ℝ) := by
      have hle := hmono_sub hzero_dom hm_dom (by positivity)
      simpa [chapter05_herbrand_function_zero T.subextension] using hle
    have hsub_x_nonneg : 0 ≤
        chapter05HerbrandFunction T.subextension x :=
      hsub_nonneg (le_of_lt hxpos)
    have hcont_sub : ContinuousOn
        (chapter05HerbrandFunction T.subextension)
        (Set.uIcc (m : ℝ) x) := by
      apply (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
        T.subextension).1.mono
      intro y hy
      have hy' : y ∈ Set.Icc (m : ℝ) x := by
        simpa [Set.uIcc_of_le hmx] using hy
      exact hm_dom.trans hy'.1
    have hderiv_sub : ∀ y ∈ Set.Ioo (m : ℝ) x,
        HasDerivAt (chapter05HerbrandFunction T.subextension)
          (chapter05HerbrandSlope T.subextension y) y := by
      intro y hy
      have hypos : 0 < y := by
        have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith [hy.1]
      have hy_upper : y ≤ ((m + 1 : ℕ) : ℝ) := by
        exact le_trans hy.2.le hxnext
      let c : ℝ :=
        (Nat.card (T.subextension.lowerGroup (m + 1 : ℕ)) : ℝ) /
          (Nat.card (T.subextension.lowerGroup 0) : ℝ)
      have hlocal : (fun z : ℝ =>
          chapter05HerbrandFunction T.subextension z) =ᶠ[𝓝 y]
          (fun z : ℝ =>
            chapter05HerbrandFunction T.subextension (m : ℝ) +
              (z - (m : ℝ)) * c) := by
        have hnhds : Set.Ioo (m : ℝ) ((m + 1 : ℕ) : ℝ) ∈ 𝓝 y :=
          Ioo_mem_nhds hy.1 (lt_of_lt_of_le hy.2 hxnext)
        filter_upwards [hnhds] with z hz
        have hdiff :=
          (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
            T.subextension).2.2 m hz.1.le hz.2.le le_rfl (by norm_num)
        dsimp [c]
        linarith
      have haffine : HasDerivAt (fun z : ℝ =>
          chapter05HerbrandFunction T.subextension (m : ℝ) +
            (z - (m : ℝ)) * c) c y := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id' y).sub_const (m : ℝ)).mul_const c).const_add
            (chapter05HerbrandFunction T.subextension (m : ℝ))
      have hderiv : HasDerivAt (chapter05HerbrandFunction T.subextension)
          c y := haffine.congr_of_eventuallyEq hlocal
      have hc : chapter05HerbrandSlope T.subextension y = c := by
        rw [chapter05HerbrandSlope, if_neg (not_le.mpr hypos)]
        rw [T.subextension.lower_real_convention m y hy.1 hy_upper]
      exact hderiv.congr_deriv hc.symm
    have hderiv_nonneg : ∀ y ∈ Set.Ioo (m : ℝ) x,
        0 ≤ chapter05HerbrandSlope T.subextension y := by
      intro y hy
      rw [chapter05HerbrandSlope]
      split_ifs with hy0
      · positivity
      · have hnum : 0 ≤ (Nat.card
            (T.subextension.lowerGroup y) : ℝ) := by positivity
        have hden : 0 < (Nat.card
            (T.subextension.lowerGroup 0) : ℝ) := by
          exact_mod_cast Nat.card_pos
        positivity
    have hchange :
        (∫ y in (m : ℝ)..x,
          (chapter05HerbrandSlope T.quotientSetup.downstairs ∘
            chapter05HerbrandFunction T.subextension) y *
            chapter05HerbrandSlope T.subextension y) =
          ∫ z in chapter05HerbrandFunction T.subextension (m : ℝ)..
            chapter05HerbrandFunction T.subextension x,
            chapter05HerbrandSlope T.quotientSetup.downstairs z := by
      simpa only [Function.comp_apply] using
        (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
          (f := chapter05HerbrandFunction T.subextension)
          (f' := chapter05HerbrandSlope T.subextension)
          (g := chapter05HerbrandSlope T.quotientSetup.downstairs)
          hcont_sub
          (by simpa [min_eq_left hmx, max_eq_right hmx] using hderiv_sub)
          (by simpa [min_eq_left hmx, max_eq_right hmx] using hderiv_nonneg))
    have hintegrand :
        (∫ y in (m : ℝ)..x,
          (chapter05HerbrandSlope T.quotientSetup.downstairs ∘
            chapter05HerbrandFunction T.subextension) y *
            chapter05HerbrandSlope T.subextension y) =
          ∫ y in (m : ℝ)..x,
            chapter05HerbrandSlope T.quotientSetup.upstairs y := by
      apply intervalIntegral.integral_congr_Ioo_of_le hmx
      intro y hy
      exact hslope_comp (by
        have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith [hy.1])
    have hdown_diff := chapter05_herbrand_function_sub_eq_integral
      T.quotientSetup.downstairs hsub_m_nonneg hsub_x_nonneg
    have hup_diff := chapter05_herbrand_function_sub_eq_integral
      T.quotientSetup.upstairs (a := (m : ℝ)) (b := x)
      (by positivity) (by positivity)
    calc
      chapter05HerbrandFunction T.quotientSetup.downstairs
          (chapter05HerbrandFunction T.subextension x) -
          chapter05HerbrandFunction T.quotientSetup.downstairs
            (chapter05HerbrandFunction T.subextension (m : ℝ)) =
          ∫ z in chapter05HerbrandFunction T.subextension (m : ℝ)..
            chapter05HerbrandFunction T.subextension x,
            chapter05HerbrandSlope T.quotientSetup.downstairs z := hdown_diff
      _ = ∫ y in (m : ℝ)..x,
          (chapter05HerbrandSlope T.quotientSetup.downstairs ∘
            chapter05HerbrandFunction T.subextension) y *
            chapter05HerbrandSlope T.subextension y := hchange.symm
      _ = ∫ y in (m : ℝ)..x,
          chapter05HerbrandSlope T.quotientSetup.upstairs y := hintegrand
      _ = chapter05HerbrandFunction T.quotientSetup.upstairs x -
          chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) :=
        hup_diff.symm
  have hclock_nat : ∀ m : ℕ,
      chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) =
        chapter05HerbrandFunction T.quotientSetup.downstairs
          (chapter05HerbrandFunction T.subextension (m : ℝ)) := by
    intro m
    induction m with
    | zero => simp [chapter05_herbrand_function_zero]
    | succ m ihm =>
        have hseg := hsegment m (x := ((m + 1 : ℕ) : ℝ))
          (by norm_num) (by norm_num)
        rw [show (m + 1 : ℕ) = m + 1 by rfl] at hseg
        calc
          chapter05HerbrandFunction T.quotientSetup.upstairs ((m + 1 : ℕ) : ℝ) =
              chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) +
                (chapter05HerbrandFunction T.quotientSetup.upstairs ((m + 1 : ℕ) : ℝ) -
                  chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ)) := by ring
          _ = chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) +
                (chapter05HerbrandFunction T.quotientSetup.downstairs
                  (chapter05HerbrandFunction T.subextension ((m + 1 : ℕ) : ℝ)) -
                chapter05HerbrandFunction T.quotientSetup.downstairs
                  (chapter05HerbrandFunction T.subextension (m : ℝ))) := by
              rw [hseg]
          _ = chapter05HerbrandFunction T.quotientSetup.downstairs
                (chapter05HerbrandFunction T.subextension ((m + 1 : ℕ) : ℝ)) := by
              rw [ihm]
              ring
  by_cases hu0 : u ≤ 0
  · simp [chapter05_herbrand_function_of_nonpositive _ hu0]
  · let m : ℕ := ⌊u⌋₊
    have hmu : (m : ℝ) ≤ u := by
      exact Nat.floor_le (le_of_not_ge hu0)
    have hum : u ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [m] using (Nat.lt_floor_add_one u).le
    have hseg := hsegment m hmu hum
    calc
      chapter05HerbrandFunction T.quotientSetup.upstairs u =
          chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) +
            (chapter05HerbrandFunction T.quotientSetup.upstairs u -
              chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ)) := by ring
      _ = chapter05HerbrandFunction T.quotientSetup.upstairs (m : ℝ) +
            (chapter05HerbrandFunction T.quotientSetup.downstairs
              (chapter05HerbrandFunction T.subextension u) -
              chapter05HerbrandFunction T.quotientSetup.downstairs
                (chapter05HerbrandFunction T.subextension (m : ℝ))) := by
          rw [hseg]
      _ = chapter05HerbrandFunction T.quotientSetup.downstairs
          (chapter05HerbrandFunction T.subextension u) := by
          rw [hclock_nat m]
          ring

theorem chapter05_herbrand_inverse_tower_transitivity
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction T.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05HerbrandInverse T.quotientSetup.upstairs v =
      chapter05HerbrandInverse T.subextension
        (chapter05HerbrandInverse T.quotientSetup.downstairs v) := by
  have hdown_inv_ge : (-1 : ℝ) ≤
      chapter05HerbrandInverse T.quotientSetup.downstairs v := by
    by_contra hnot
    have hlt : chapter05HerbrandInverse T.quotientSetup.downstairs v <
        (-1 : ℝ) := lt_of_not_ge hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive
      T.quotientSetup.downstairs (by linarith)
    have hspec := chapter05_herbrand_inverse_spec
      T.quotientSetup.downstairs hMK v
    have hinv_eq : chapter05HerbrandInverse T.quotientSetup.downstairs v = v :=
      hidentity.symm.trans hspec
    linarith
  have hsub_inv_ge : (-1 : ℝ) ≤
      chapter05HerbrandInverse T.subextension
        (chapter05HerbrandInverse T.quotientSetup.downstairs v) := by
    by_contra hnot
    have hlt : chapter05HerbrandInverse T.subextension
        (chapter05HerbrandInverse T.quotientSetup.downstairs v) <
        (-1 : ℝ) := lt_of_not_ge hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive
      T.subextension (by linarith)
    have hspec := chapter05_herbrand_inverse_spec T.subextension hLM
      (chapter05HerbrandInverse T.quotientSetup.downstairs v)
    have hinv_eq : chapter05HerbrandInverse T.subextension
        (chapter05HerbrandInverse T.quotientSetup.downstairs v) =
        chapter05HerbrandInverse T.quotientSetup.downstairs v :=
      hidentity.symm.trans hspec
    linarith
  apply hLK.injective
  calc
    chapter05HerbrandFunction T.quotientSetup.upstairs
        (chapter05HerbrandInverse T.quotientSetup.upstairs v) = v :=
      chapter05_herbrand_inverse_spec T.quotientSetup.upstairs hLK v
    _ = chapter05HerbrandFunction T.quotientSetup.downstairs
        (chapter05HerbrandInverse T.quotientSetup.downstairs v) :=
      (chapter05_herbrand_inverse_spec T.quotientSetup.downstairs hMK v).symm
    _ = chapter05HerbrandFunction T.quotientSetup.downstairs
        (chapter05HerbrandFunction T.subextension
          (chapter05HerbrandInverse T.subextension
            (chapter05HerbrandInverse T.quotientSetup.downstairs v))) := by
      rw [chapter05_herbrand_inverse_spec T.subextension hLM]
    _ = chapter05HerbrandFunction T.quotientSetup.upstairs
        (chapter05HerbrandInverse T.subextension
          (chapter05HerbrandInverse T.quotientSetup.downstairs v)) :=
      (chapter05_herbrand_tower_transitivity H T hLM).symm

/-- A closure-independent invariant is the formal interface for descent from a Galois closure. -/
structure Chapter05ClosureIndependentInvariant (C X : Type*) where
  nonempty : Nonempty C
  value : C → X
  independent : ∀ c₁ c₂ : C, value c₁ = value c₂

namespace Chapter05ClosureIndependentInvariant

variable {C X : Type*}

theorem value_eq (I : Chapter05ClosureIndependentInvariant C X)
    (c₁ c₂ : C) : I.value c₁ = I.value c₂ := by
  exact I.independent c₁ c₂

end Chapter05ClosureIndependentInvariant

/-
 The non-Galois protocol used later in the book is recorded as a reusable
 interface: choose a finite Galois closure, apply subgroup and quotient
 formulas there, and descend only invariants equipped with the independence
 witness.  Different and discriminant ideals are the principal later
 instances of this interface.
-/
theorem chapter05_galois_closure_descent_of_independent_invariant
    {C X : Type*}
    (I : Chapter05ClosureIndependentInvariant C X)
    (c₁ c₂ : C) : I.value c₁ = I.value c₂ := by
  exact I.independent c₁ c₂

end
end LastLib.Book03RamificationTheory.Chapter05
