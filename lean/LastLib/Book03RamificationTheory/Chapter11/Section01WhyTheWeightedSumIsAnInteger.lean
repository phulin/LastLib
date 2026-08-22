import LastLib.Book03RamificationTheory.Chapter11.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open scoped BigOperators

/-! ## 11.1. Why the weighted sum is an integer -/

/-- The Artin class function attached to the lower displacement function. -/
def chapter11ArtinClassFunction
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : G → k := by
  classical
  exact fun σ ↦ if hσ : σ = 1 then
      (D.f : k) * ∑ τ ∈ (Finset.univ.erase (1 : G)),
        (chapter11Displacement D τ : k)
    else -(D.f : k) * (chapter11Displacement D σ : k)

/-- The normalized character pairing, with the inverse convention used by the source. -/
def chapter11CharacterPairing
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : G → k) (ρ : Representation k G V) : k :=
  (Fintype.card G : k)⁻¹ *
    ∑ σ : G, A σ * Representation.character ρ σ⁻¹

/-- The averaging operator for a subgroup, written in the same coordinates as the source. -/
def chapter11AveragingProjector
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : V →ₗ[k] V := by
  classical
  exact (Nat.card H : k)⁻¹ • ∑ h : H, ρ h

theorem chapter11_card_inertia_eq_e
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Nat.card D.inertia = D.e := by
  exact D.inertia_card

theorem chapter11_card_group_eq_ef
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Fintype.card G = D.e * D.f := by
  exact D.group_card

theorem chapter11_displacement_conjugation_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (g σ : G) :
    chapter11Displacement D (g * σ * g⁻¹) = chapter11Displacement D σ := by
  by_cases hσ : σ = 1
  · subst σ
    simp
  · have hconj : g * σ * g⁻¹ ≠ 1 := by
      intro h
      have h' := congrArg (fun x : G => g⁻¹ * x * g) h
      apply hσ
      simpa [mul_assoc] using h'
    rw [chapter11_displacement_eq_support_card_of_ne_one D hconj,
      chapter11_displacement_eq_support_card_of_ne_one D hσ]
    congr 1
    ext i
    simp only [chapter11LowerSupport, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hmem⟩
      exact ⟨hi, (D.lower_conj_invariant i g σ).mpr hmem⟩
    · rintro ⟨hi, hmem⟩
      exact ⟨hi, (D.lower_conj_invariant i g σ).mp hmem⟩

theorem chapter11_displacement_inverse_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) :
    chapter11Displacement D σ⁻¹ = chapter11Displacement D σ := by
  by_cases hσ : σ = 1
  · subst σ
    simp
  · have hinv : σ⁻¹ ≠ 1 := by
      simpa using hσ
    rw [chapter11_displacement_eq_support_card_of_ne_one D hinv,
      chapter11_displacement_eq_support_card_of_ne_one D hσ]
    congr 1
    ext i
    simp [chapter11LowerSupport]

theorem chapter11_artin_class_function_conjugation_invariant
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (g σ : G) :
    chapter11ArtinClassFunction (k := k) D (g * σ * g⁻¹) =
      chapter11ArtinClassFunction (k := k) D σ := by
  by_cases hσ : σ = 1
  · subst σ
    simp [chapter11ArtinClassFunction]
  · have hconj : g * σ * g⁻¹ ≠ 1 := by
      intro h
      have h' := congrArg (fun x : G => g⁻¹ * x * g) h
      apply hσ
      simpa [mul_assoc] using h'
    simp only [chapter11ArtinClassFunction, dif_neg hconj, dif_neg hσ]
    rw [chapter11_displacement_conjugation_invariant]

theorem chapter11_artin_class_function_sum_eq_zero
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    ∑ σ : G, chapter11ArtinClassFunction (k := k) D σ = 0 := by
  classical
  have hsum := Finset.sum_erase_add
    (s := (Finset.univ : Finset G))
    (f := chapter11ArtinClassFunction (k := k) D)
    (Finset.mem_univ (1 : G))
  rw [← hsum]
  have herase :
      (∑ σ ∈ (Finset.univ.erase (1 : G)),
          chapter11ArtinClassFunction (k := k) D σ) =
        ∑ σ ∈ (Finset.univ.erase (1 : G)),
          -(D.f : k) * (chapter11Displacement D σ : k) := by
    apply Finset.sum_congr rfl
    intro σ hσ
    simp [chapter11ArtinClassFunction, (Finset.mem_erase.mp hσ).1]
  rw [herase]
  have hone :
      chapter11ArtinClassFunction (k := k) D 1 =
        (D.f : k) *
          ∑ τ ∈ (Finset.univ.erase (1 : G)),
            (chapter11Displacement D τ : k) := by
    simp [chapter11ArtinClassFunction]
  rw [hone]
  change
    (∑ σ ∈ (Finset.univ.erase (1 : G)),
        -(D.f : k) * (chapter11Displacement D σ : k)) +
      (D.f : k) *
        ∑ τ ∈ (Finset.univ.erase (1 : G)),
          (chapter11Displacement D τ : k) = 0
  rw [← Finset.mul_sum]
  ring

theorem chapter11_artin_class_function_eq_zero_of_not_mem_inertia
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) {σ : G}
    (hσ : σ ∉ D.inertia) :
    chapter11ArtinClassFunction (k := k) D σ = 0 := by
  by_cases hσ1 : σ = 1
  · subst σ
    exact False.elim (hσ (by simp))
  · simp only [chapter11ArtinClassFunction, dif_neg hσ1]
    rw [chapter11_displacement_eq_zero_of_not_mem_inertia D hσ]
    simp

theorem chapter11_averaging_projector_range
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) :
    LinearMap.range (chapter11AveragingProjector ρ H) =
      Representation.invariants (ρ.comp H.subtype) := by
  let _ : Invertible (Fintype.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let ρH : Representation k H V := ρ.comp H.subtype
  have haverage :
      chapter11AveragingProjector ρ H = Representation.averageMap ρH := by
    ext v
    simp [chapter11AveragingProjector, Representation.averageMap,
      GroupAlgebra.average, Representation.asAlgebraHom, ρH,
      Nat.card_eq_fintype_card, map_sum, map_smul]
  rw [haverage]
  exact (Representation.isProj_averageMap ρH).range

theorem chapter11_averaging_projector_fixed
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (v : V)
    (hv : v ∈ Representation.invariants (ρ.comp H.subtype)) :
    chapter11AveragingProjector ρ H v = v := by
  let _ : Invertible (Fintype.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let ρH : Representation k H V := ρ.comp H.subtype
  have haverage :
      chapter11AveragingProjector ρ H = Representation.averageMap ρH := by
    ext w
    simp [chapter11AveragingProjector, Representation.averageMap,
      GroupAlgebra.average, Representation.asAlgebraHom, ρH,
      Nat.card_eq_fintype_card, map_sum, map_smul]
  rw [haverage]
  exact Representation.averageMap_id ρH v hv

/-- The fixed-space formula in the displayed weighted-sum normalization. -/
theorem chapter11_artin_conductor_eq_fixed_space_sum
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11ArtinConductor D ρ =
      ∑ i ∈ Finset.range D.bound,
        ((Nat.card (D.lower i) : ℚ) / (Nat.card D.inertia : ℚ)) *
          ((Module.finrank k V -
            Module.finrank k (Representation.invariants (ρ.comp (D.lower i).subtype))) : ℚ) := by
  classical
  unfold chapter11ArtinConductor chapter11LowerWeight
  change (∑ i ∈ Finset.range D.bound,
      ((Nat.card (D.lower i) : ℚ) / (Nat.card D.inertia : ℚ)) *
        (Module.finrank k
          (V ⧸ Representation.invariants (ρ.comp (D.lower i).subtype)) : ℚ)) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [Submodule.finrank_quotient]
  rw [Nat.cast_sub]
  exact Submodule.finrank_le _

/-- The Artin character pairing is the conductor.  The target field only changes the scalar cast. -/
theorem chapter11_artin_class_function_pairing_eq_artin_conductor
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11CharacterPairing (chapter11ArtinClassFunction D) ρ =
      (chapter11ArtinConductor D ρ : k) := by
  classical
  have hsum_subtype (H : Subgroup G) (f : G → k) :
      (∑ g : G, if g ∈ H then f g else 0) = ∑ h : H, f h := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun g hg => ⟨g, (Finset.mem_filter.mp hg).2⟩) ?_ ?_ ?_ ?_
    · intro g hg
      simp
    · intro g₁ hg₁ g₂ hg₂ h
      exact congrArg Subtype.val h
    · intro h hh
      refine ⟨(h : G), by simp [h.property], ?_⟩
      rfl
    · intro g hg
      rfl
  have hsum_fixed (H : Subgroup G) :
      (Finset.univ.sum (fun h : H =>
        (Module.finrank k V : k) - Representation.character ρ h)) =
        (Nat.card H : k) *
          ((Module.finrank k V : k) -
            Module.finrank k (Representation.invariants (ρ.comp H.subtype))) := by
    let _ : Invertible (Fintype.card H : k) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    have hchar :=
      Representation.card_inv_mul_sum_char_eq_finrank (ρ := ρ.comp H.subtype)
    have hcard : (Nat.card H : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.card_pos : 0 < Nat.card H))
    have hchar' := hchar
    field_simp [hcard] at hchar'
    have hchar'' :
        (Finset.univ.sum (fun h : H => Representation.character ρ h)) =
          (Nat.card H : k) * Module.finrank k
            (Representation.invariants (ρ.comp H.subtype)) := by
      simpa [Representation.character] using hchar'
    rw [Finset.sum_sub_distrib, Finset.sum_const, hchar'']
    simp [mul_sub]
  have hsum_inverse (H : Subgroup G) :
      (Finset.univ.sum (fun h : H =>
        (Module.finrank k V : k) - Representation.character ρ h⁻¹)) =
        Finset.univ.sum (fun h : H =>
          (Module.finrank k V : k) - Representation.character ρ h) := by
    rw [← Equiv.sum_comp (Equiv.inv H)]
    simp
  have hdiff (H : Subgroup G) :
      (Finset.univ.sum (fun g : G =>
        if g ∈ H then
          (Module.finrank k V : k) - Representation.character ρ g⁻¹
        else 0)) =
        (Nat.card H : k) *
          ((Module.finrank k V : k) -
            Module.finrank k (Representation.invariants (ρ.comp H.subtype))) := by
    rw [hsum_subtype]
    rw [hsum_inverse H]
    exact hsum_fixed H
  have hdisp (σ : G) (hσ : σ ≠ 1) :
      (chapter11Displacement D σ : k) =
        (Finset.range D.bound).sum (fun i : ℕ =>
          if σ ∈ D.lower i then 1 else 0) := by
    rw [chapter11_displacement_eq_support_card_of_ne_one D hσ]
    rw [chapter11LowerSupport, Finset.card_filter]
    norm_cast
  have hpair :
      (Finset.univ.sum (fun σ : G =>
        chapter11ArtinClassFunction (k := k) D σ * Representation.character ρ σ⁻¹)) =
        (D.f : k) *
          (Finset.univ.erase (1 : G)).sum (fun σ =>
            (chapter11Displacement D σ : k) *
              ((Module.finrank k V : k) - Representation.character ρ σ⁻¹)) := by
    have hsum := Finset.sum_erase_add
      (s := (Finset.univ : Finset G))
      (f := fun σ : G =>
        chapter11ArtinClassFunction (k := k) D σ * Representation.character ρ σ⁻¹)
      (Finset.mem_univ (1 : G))
    have hone :
        chapter11ArtinClassFunction (k := k) D 1 *
            Representation.character ρ (1 : G)⁻¹ =
          (D.f : k) *
            (Finset.univ.erase (1 : G)).sum
              (fun σ => (chapter11Displacement D σ : k)) *
            (Module.finrank k V : k) := by
      simp [chapter11ArtinClassFunction]
    have herase :
        (Finset.univ.erase (1 : G)).sum (fun σ =>
          chapter11ArtinClassFunction (k := k) D σ *
            Representation.character ρ σ⁻¹) =
          (Finset.univ.erase (1 : G)).sum (fun σ =>
            -(D.f : k) * (chapter11Displacement D σ : k) *
              Representation.character ρ σ⁻¹) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [chapter11ArtinClassFunction, (Finset.mem_erase.mp hσ).1]
    rw [← hsum, herase, hone]
    calc
      (∑ x ∈ Finset.univ.erase (1 : G),
          -(D.f : k) * (chapter11Displacement D x : k) *
            Representation.character ρ x⁻¹) +
          (D.f : k) *
            (∑ x ∈ Finset.univ.erase (1 : G),
              (chapter11Displacement D x : k)) *
            (Module.finrank k V : k) =
        -(D.f : k) *
            (∑ x ∈ Finset.univ.erase (1 : G),
              (chapter11Displacement D x : k) *
                Representation.character ρ x⁻¹) +
          (D.f : k) *
            (∑ x ∈ Finset.univ.erase (1 : G),
              (chapter11Displacement D x : k) *
        (Module.finrank k V : k)) := by
        congr 1
        · have hterm :
              (Finset.univ.erase (1 : G)).sum (fun x =>
                -(D.f : k) * (chapter11Displacement D x : k) *
                  Representation.character ρ x⁻¹) =
                (Finset.univ.erase (1 : G)).sum (fun x =>
                  -(D.f : k) *
                    ((chapter11Displacement D x : k) *
                      Representation.character ρ x⁻¹)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          rw [hterm, ← Finset.mul_sum]
        · rw [mul_assoc, Finset.sum_mul]
      _ = (D.f : k) *
          (∑ x ∈ Finset.univ.erase (1 : G),
            (chapter11Displacement D x : k) *
              ((Module.finrank k V : k) - Representation.character ρ x⁻¹)) := by
        have hsum_sub :
            (Finset.univ.erase (1 : G)).sum (fun x =>
              (chapter11Displacement D x : k) *
                ((Module.finrank k V : k) - Representation.character ρ x⁻¹)) =
              (Finset.univ.erase (1 : G)).sum (fun x =>
                (chapter11Displacement D x : k) *
                  (Module.finrank k V : k)) -
                (Finset.univ.erase (1 : G)).sum (fun x =>
                  (chapter11Displacement D x : k) *
                    Representation.character ρ x⁻¹) := by
          calc
            _ = (Finset.univ.erase (1 : G)).sum (fun x =>
                (chapter11Displacement D x : k) *
                  (Module.finrank k V : k) -
                    (chapter11Displacement D x : k) *
                      Representation.character ρ x⁻¹) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = _ := by rw [Finset.sum_sub_distrib]
        rw [hsum_sub]
        ring
  have herase_diff (H : Subgroup G) :
      (Finset.univ.erase (1 : G)).sum (fun g =>
        if g ∈ H then
          (Module.finrank k V : k) - Representation.character ρ g⁻¹
        else 0) =
        (Nat.card H : k) *
          ((Module.finrank k V : k) -
            Module.finrank k (Representation.invariants (ρ.comp H.subtype))) := by
    have hsum := Finset.sum_erase_add
      (s := (Finset.univ : Finset G))
      (f := fun g : G =>
        if g ∈ H then
          (Module.finrank k V : k) - Representation.character ρ g⁻¹
        else 0)
      (Finset.mem_univ (1 : G))
    have hone :
        (if (1 : G) ∈ H then
            (Module.finrank k V : k) - Representation.character ρ (1 : G)⁻¹
          else 0) = 0 := by
      simp
    calc
      (Finset.univ.erase (1 : G)).sum (fun g =>
          if g ∈ H then
            (Module.finrank k V : k) - Representation.character ρ g⁻¹
          else 0) =
          (Finset.univ.erase (1 : G)).sum (fun g =>
            if g ∈ H then
              (Module.finrank k V : k) - Representation.character ρ g⁻¹
            else 0) + 0 := by rw [add_zero]
      _ = (Finset.univ.erase (1 : G)).sum (fun g =>
            if g ∈ H then
              (Module.finrank k V : k) - Representation.character ρ g⁻¹
            else 0) +
            (if (1 : G) ∈ H then
              (Module.finrank k V : k) - Representation.character ρ (1 : G)⁻¹
            else 0) := by rw [hone]
      _ = Finset.univ.sum (fun g : G =>
            if g ∈ H then
              (Module.finrank k V : k) - Representation.character ρ g⁻¹
            else 0) := hsum
      _ = (Nat.card H : k) *
          ((Module.finrank k V : k) -
            Module.finrank k (Representation.invariants (ρ.comp H.subtype))) :=
        hdiff H
  have hexpand :
      (Finset.univ.erase (1 : G)).sum (fun σ =>
        (chapter11Displacement D σ : k) *
          ((Module.finrank k V : k) - Representation.character ρ σ⁻¹)) =
        (Finset.range D.bound).sum (fun i =>
          (Finset.univ.erase (1 : G)).sum (fun σ =>
            if σ ∈ D.lower i then
              (Module.finrank k V : k) - Representation.character ρ σ⁻¹
            else 0)) := by
    calc
      _ = (Finset.univ.erase (1 : G)).sum (fun σ =>
          ((Finset.range D.bound).sum (fun i =>
            if σ ∈ D.lower i then 1 else 0)) *
            ((Module.finrank k V : k) - Representation.character ρ σ⁻¹)) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [hdisp σ (Finset.mem_erase.mp hσ).1, Finset.sum_mul]
      _ = (Finset.univ.erase (1 : G)).sum (fun σ =>
          (Finset.range D.bound).sum (fun i =>
            (if σ ∈ D.lower i then 1 else 0) *
              ((Module.finrank k V : k) - Representation.character ρ σ⁻¹))) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [Finset.sum_mul]
      _ = (Finset.range D.bound).sum (fun i =>
          (Finset.univ.erase (1 : G)).sum (fun σ =>
            (if σ ∈ D.lower i then 1 else 0) *
              ((Module.finrank k V : k) - Representation.character ρ σ⁻¹))) := by
        conv_lhs => rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro σ hσ
        by_cases hmem : σ ∈ D.lower i <;> simp [hmem]
  have hnorm :
      (Fintype.card G : k)⁻¹ * (D.f : k) =
        (Nat.card D.inertia : k)⁻¹ := by
    rw [D.group_card, Nat.cast_mul, D.inertia_card]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.e_pos),
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.f_pos)]
  unfold chapter11CharacterPairing
  rw [hpair, hexpand]
  simp_rw [herase_diff]
  rw [← mul_assoc, hnorm]
  rw [chapter11_artin_conductor_eq_fixed_space_sum D ρ]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [div_eq_mul_inv]
  ring

/-- The pairing is unchanged if the summation variable is inverted. -/
theorem chapter11_artin_class_function_pairing_inverse_form
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11CharacterPairing (chapter11ArtinClassFunction D) ρ =
      (Fintype.card G : k)⁻¹ *
        ∑ σ : G, chapter11ArtinClassFunction D σ⁻¹ *
          Representation.character ρ σ := by
  unfold chapter11CharacterPairing
  congr 1
  rw [← Equiv.sum_comp (Equiv.inv G)]
  simp

end
end LastLib.Book03RamificationTheory.Chapter11
