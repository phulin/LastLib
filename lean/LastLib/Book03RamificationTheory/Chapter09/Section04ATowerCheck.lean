import LastLib.Book03RamificationTheory.Chapter09.Section03TameAndWildPartsOfTheDifferent

namespace LastLib.Book03RamificationTheory.Chapter09

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open scoped Classical
open scoped BigOperators

/-! ## 9.4. A tower check -/

def chapter09HerbrandIndexWeight
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) : ℝ :=
  (Nat.card (D.lowerGroup u) : ℝ) /
    (Nat.card (D.lowerGroup 0) : ℝ)

theorem chapter09_herbrand_slope_is_index_weight
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) (hu : 0 < u) :
    chapter05HerbrandSlope D u = chapter09HerbrandIndexWeight D u := by
  simp [chapter05HerbrandSlope, chapter09HerbrandIndexWeight, hu]

structure Chapter09TowerDifferentCheck
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  tower : Chapter05HerbrandTowerSetup G H
  dLK : ℕ
  dLM : ℕ
  dMK : ℕ
  dLK_hilbert :
    dLK = chapter09GroupCountSum tower.quotientSetup.upstairs
  dLM_hilbert :
    dLM = chapter09GroupCountSum tower.subextension
  dMK_hilbert :
    dMK = chapter09GroupCountSum tower.quotientSetup.downstairs

theorem chapter09_tower_lower_subgroup_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) :
    T.subextension.lowerGroup u =
      (T.quotientSetup.upstairs.lowerGroup u).comap
        (Subgroup.subtype H) := by
  exact chapter05_lower_subgroup_formula H T hu

theorem chapter09_tower_quotient_upper_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05HerbrandTowerSetup G H)
    (_hup : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.upstairs))
    (_hdown : Function.Bijective
      (chapter05HerbrandFunction T.quotientSetup.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup T.quotientSetup.downstairs v =
      chapter05UpperQuotientImage H T.quotientSetup.upstairs v := by
  exact chapter05_herbrand_quotient_theorem H T.quotientSetup hv

theorem chapter09_tower_quotient_exact_sequence
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] :
    Function.MulExact (Subgroup.subtype H)
        (chapter05QuotientMap H) ∧
      Function.Surjective (chapter05QuotientMap H) := by
  exact Chapter05QuotientRamificationSetup.quotient_exact_sequence H

theorem chapter09_tower_fixed_field_quotient_equiv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (Gal(L / K))) [H.Normal] :
    Nonempty
      ((Gal(L / K) ⧸ H) ≃*
        Gal(LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K)) := by
  exact chapter05_fixed_field_quotient_galois_equiv H

theorem chapter09_different_transitivity_from_tower_check
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (C : Chapter09TowerDifferentCheck G H)
    (_hLK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.upstairs))
    (_hLM : Function.Bijective
      (chapter05HerbrandFunction C.tower.subextension))
    (_hMK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.downstairs)) :
    C.dLK = C.dLM + C.tower.quotientSetup.eLM * C.dMK := by
  rw [C.dLK_hilbert, C.dLM_hilbert, C.dMK_hilbert]
  rw [← chapter09_displacement_sum_eq_group_count_sum
    C.tower.quotientSetup.upstairs,
    ← chapter09_displacement_sum_eq_group_count_sum C.tower.subextension,
    ← chapter09_displacement_sum_eq_group_count_sum
      C.tower.quotientSetup.downstairs]
  let U := C.tower.quotientSetup.upstairs
  let M := C.tower.subextension
  let Q := G ⧸ H
  let qmap : G →* Q := chapter05QuotientMap H
  have hdisp_sub (τ : H) :
      M.displacement τ = U.displacement (τ : G) := by
    by_cases hτ1 : τ = 1
    · subst τ
      exact M.displacement_one.trans U.displacement_one.symm
    have hτ_ne : (τ : G) ≠ 1 := by
      intro hτ
      apply hτ1
      exact Subtype.ext hτ
    have hiff (n : ℕ) :
        n + 1 ≤ M.displacement τ ↔
          n + 1 ≤ U.displacement (τ : G) := by
      rw [← M.lower_nat_mem_iff hτ1 n,
        C.tower.subgroup_lower_formula (n : ℝ)
          (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])]
      change (τ : G) ∈ U.lowerGroup (n : ℝ) ↔ _
      exact U.lower_nat_mem_iff hτ_ne n
    apply Nat.le_antisymm
    · by_cases hz : M.displacement τ = 0
      · omega
      · have hp : 1 ≤ M.displacement τ := Nat.one_le_iff_ne_zero.mpr hz
        have hh := (hiff (M.displacement τ - 1)).mp (by omega)
        omega
    · by_cases hz : U.displacement (τ : G) = 0
      · omega
      · have hp : 1 ≤ U.displacement (τ : G) :=
          Nat.one_le_iff_ne_zero.mpr hz
        have hh := (hiff (U.displacement (τ : G) - 1)).mpr (by omega)
        omega
  let eH : H ≃ {g : G // g ∈ H} :=
    { toFun := fun τ => ⟨τ, τ.property⟩
      invFun := fun g => ⟨g, g.property⟩
      left_inv := by intro τ; rfl
      right_inv := by intro g; rfl }
  have hfullM :
      chapter09DisplacementSum M = ∑ g : H, M.displacement g := by
    unfold chapter09DisplacementSum
    have h := @Finset.sum_erase_add H ℕ _
      (fun a b => Classical.propDecidable (a = b))
      (Finset.univ : Finset H) M.displacement (a := (1 : H))
      (Finset.mem_univ (1 : H))
    simpa [M.displacement_one] using h
  have hfullU :
      chapter09DisplacementSum U = ∑ g : G, U.displacement g := by
    unfold chapter09DisplacementSum
    have h := @Finset.sum_erase_add G ℕ _
      (fun a b => Classical.propDecidable (a = b))
      (Finset.univ : Finset G) U.displacement (a := (1 : G))
      (Finset.mem_univ (1 : G))
    simpa [U.displacement_one] using h
  have hfullQ :
      chapter09DisplacementSum C.tower.quotientSetup.downstairs =
        ∑ g : Q, C.tower.quotientSetup.downstairs.displacement g := by
    unfold chapter09DisplacementSum
    have h := @Finset.sum_erase_add Q ℕ _
      (fun a b => Classical.propDecidable (a = b))
      (Finset.univ : Finset Q)
      C.tower.quotientSetup.downstairs.displacement (a := (1 : Q))
      (Finset.mem_univ (1 : Q))
    simpa [C.tower.quotientSetup.downstairs.displacement_one] using h
  have hsum_H :
      chapter09DisplacementSum M =
        ∑ g : {g : G // g ∈ H}, U.displacement g := by
    rw [hfullM]
    change (∑ τ : H, M.displacement τ) = _
    rw [show (∑ τ : H, M.displacement τ) =
        ∑ τ : H, U.displacement (τ : G) by
      apply Finset.sum_congr rfl
      intro τ hτ
      exact hdisp_sub τ]
  let Q0 := {q : Q // q ≠ 1}
  let G0 := {g : G // g ∉ H}
  have hqmap_surj : Function.Surjective qmap :=
    Chapter05QuotientRamificationSetup.quotient_map_surjective H
  let rep : Q0 → G := fun q => Classical.choose (hqmap_surj q)
  have hrep (q : Q0) : qmap (rep q) = q :=
    Classical.choose_spec (hqmap_surj q)
  let e0 : Q0 × H → G0 := fun x =>
    ⟨rep x.1 * (x.2 : G), by
      intro hmem
      apply x.1.property
      calc
        (x.1 : Q) = qmap (rep x.1) := (hrep x.1).symm
        _ = qmap (rep x.1 * (x.2 : G)) := by
          have hxq : qmap (x.2 : G) = 1 :=
            (QuotientGroup.eq_one_iff _).2 x.2.property
          rw [map_mul, hxq, mul_one]
        _ = 1 := (QuotientGroup.eq_one_iff _).2 hmem⟩
  let e0inv : G0 → Q0 × H := fun g =>
    let q : Q0 := ⟨qmap (g : G), by
      intro hq
      apply g.property
      exact (QuotientGroup.eq_one_iff _).mp hq⟩
    ⟨q, ⟨(rep q)⁻¹ * (g : G), by
      have hq : qmap ((rep q)⁻¹ * (g : G)) = 1 := by
        rw [map_mul, map_inv, hrep q]
        simp [q]
      exact (QuotientGroup.eq_one_iff _).mp hq⟩⟩
  have he0 : Function.Bijective e0 := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hq : qmap (rep x.1 * (x.2 : G)) =
          qmap (rep y.1 * (y.2 : G)) := congrArg (fun z : G0 => qmap z) hxy
      have hxyq : x.1 = y.1 := by
        apply Subtype.ext
        have hxq : qmap (x.2 : G) = 1 :=
          (QuotientGroup.eq_one_iff _).2 x.2.property
        have hyq : qmap (y.2 : G) = 1 :=
          (QuotientGroup.eq_one_iff _).2 y.2.property
        simpa [map_mul, hrep, hxq, hyq] using hq
      have hxyg : (x.2 : G) = (y.2 : G) := by
        have hxy' : rep x.1 * (x.2 : G) =
            rep y.1 * (y.2 : G) := Subtype.ext_iff.mp hxy
        rw [hxyq] at hxy'
        exact mul_left_cancel hxy'
      exact Prod.ext hxyq (Subtype.ext hxyg)
    · intro g
      let q : Q0 := ⟨qmap (g : G), by
        intro hq
        apply g.property
        exact (QuotientGroup.eq_one_iff _).mp hq⟩
      have hτ : (rep q)⁻¹ * (g : G) ∈ H := by
        have hq : qmap ((rep q)⁻¹ * (g : G)) = 1 := by
          rw [map_mul, map_inv, hrep q]
          simp [q]
        exact (QuotientGroup.eq_one_iff _).mp hq
      refine ⟨(q, ⟨(rep q)⁻¹ * (g : G), hτ⟩), ?_⟩
      apply Subtype.ext
      change rep q * ((rep q)⁻¹ * (g : G)) = (g : G)
      group
  have hsum_G0 :
      ∑ g : G0, U.displacement g =
        ∑ x : Q0 × H, U.displacement (e0 x) := by
    exact (Fintype.sum_bijective e0 he0 _ _ (fun _ => rfl)).symm
  have hcoset (q : Q0) :
      C.tower.quotientSetup.eLM *
          C.tower.quotientSetup.downstairs.displacement q =
        ∑ τ : H, U.displacement (rep q * (τ : G)) := by
    have hσ : rep q ∉ H := by
      intro hrepH
      apply q.property
      rw [← hrep q]
      exact (QuotientGroup.eq_one_iff _).2 hrepH
    have h := chapter05_coset_displacement_identity_integral_form H
      C.tower.quotientSetup (σ := rep q) hσ
    calc
      C.tower.quotientSetup.eLM *
          C.tower.quotientSetup.downstairs.displacement (q : Q) =
          C.tower.quotientSetup.eLM *
            C.tower.quotientSetup.downstairs.displacement
              (qmap (rep q)) := by rw [hrep q]
      _ = ∑ τ : H, U.displacement (rep q * (τ : G)) := by
        simpa [U] using h
  have hsum_Q0 :
      C.tower.quotientSetup.eLM *
          (∑ q : Q0,
            C.tower.quotientSetup.downstairs.displacement q) =
        ∑ x : Q0 × H, U.displacement (e0 x) := by
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    apply Fintype.sum_congr
    intro q
    rw [← hcoset q]
  have hsplit_G :
      chapter09DisplacementSum U =
        (∑ g : {g : G // g ∈ H}, U.displacement g) +
          ∑ g : G0, U.displacement g := by
    rw [show chapter09DisplacementSum U = ∑ g : G, U.displacement g by
      exact hfullU]
    exact (Fintype.sum_subtype_add_sum_subtype
      (fun g : G => g ∈ H) (fun g => U.displacement g)).symm
  have hsplit_Q :
      chapter09DisplacementSum C.tower.quotientSetup.downstairs =
        ∑ q : Q0,
          C.tower.quotientSetup.downstairs.displacement q := by
    have hz : (∑ q : {q : Q // ¬q ≠ 1},
        C.tower.quotientSetup.downstairs.displacement q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hq1 : (q : Q) = 1 := by
        by_contra hq1
        exact q.property hq1
      simpa [hq1] using
        C.tower.quotientSetup.downstairs.displacement_one
    calc
      chapter09DisplacementSum C.tower.quotientSetup.downstairs =
          ∑ q : Q, C.tower.quotientSetup.downstairs.displacement q := hfullQ
      _ = (∑ q : Q0,
          C.tower.quotientSetup.downstairs.displacement q) +
          ∑ q : {q : Q // ¬q ≠ 1},
            C.tower.quotientSetup.downstairs.displacement q :=
        (Fintype.sum_subtype_add_sum_subtype
          (fun q : Q => q ≠ 1)
          (fun q => C.tower.quotientSetup.downstairs.displacement q)).symm
      _ = ∑ q : Q0, C.tower.quotientSetup.downstairs.displacement q := by
        rw [hz, add_zero]
  rw [hsum_H, hsplit_G, hsplit_Q, hsum_G0]
  rw [← hsum_Q0]

theorem chapter09_different_transitivity_field_form
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (C : Chapter09TowerDifferentCheck G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction C.tower.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction C.tower.quotientSetup.downstairs)) :
    C.dLK = C.dLM + C.tower.quotientSetup.eLM * C.dMK := by
  exact chapter09_different_transitivity_from_tower_check H C hLK hLM hMK

end

end LastLib.Book03RamificationTheory.Chapter09
