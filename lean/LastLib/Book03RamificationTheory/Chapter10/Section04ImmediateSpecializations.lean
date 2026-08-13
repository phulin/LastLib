import LastLib.Book03RamificationTheory.Chapter10.Section02ArtinAndSwanConductors

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

open MeasureTheory

/-! ## 10.4. Immediate specializations -/

universe u v w

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [CharZero E] [Group G] [Fintype G]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- `G₀` acts trivially on an unramified representation. -/
def IsUnramifiedRepresentation
    (F : RamificationFiltration G) (ρ : Representation E G V) : Prop :=
  ∀ g : F.lower.group 0, ρ g = LinearMap.id

/-- `G₁` acts trivially on a tamely ramified representation. -/
def IsTamelyRamifiedRepresentation
    (F : RamificationFiltration G) (ρ : Representation E G V) : Prop :=
  ∀ g : F.lower.group 1, ρ g = LinearMap.id

/-- The trivial representation predicate, stated on the action maps. -/
def IsTrivialRepresentation (ρ : Representation E G V) : Prop :=
  ∀ g : G, ρ g = LinearMap.id

def IsOneDimensionalRepresentation (_ρ : Representation E G V) : Prop :=
  Module.finrank E V = 1

/- The source requires the character to be nontrivial on inertia, not merely
   nontrivial on the full Galois quotient; the final conjunct records exactly
   that distinction. -/

/-- A one-dimensional tame character that is nontrivial on inertia. -/
def IsNontrivialTameCharacter
    (F : RamificationFiltration G) (ρ : Representation E G V) : Prop :=
  IsOneDimensionalRepresentation ρ ∧
    IsTamelyRamifiedRepresentation F ρ ∧
    ¬ IsUnramifiedRepresentation F ρ

/--
The one-break condition used by the last specialization.  The values at the
single endpoint `r` are intentionally left unconstrained, matching the
endpoint-insensitivity of the upper integral.
-/
def HasUniqueUpperBreak
    (F : RamificationFiltration G) (ρ : Representation E G V) (r : ℝ) : Prop :=
  0 < r ∧
    (∀ {v : ℝ}, 0 ≤ v → v < r →
      fixedSpaceCodimReal ρ (F.upper.group v) = 1) ∧
    (∀ {v : ℝ}, r < v →
      fixedSpaceCodimReal ρ (F.upper.group v) = 0)

omit [CharZero E] [FiniteDimensional E V] in
theorem isUnramified_iff_inertia_trivial
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    IsUnramifiedRepresentation F ρ ↔
      ∀ g : inertiaGroup F, ρ g = LinearMap.id := by
  rfl

omit [CharZero E] [FiniteDimensional E V] in
theorem isTame_iff_wild_group_trivial
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    IsTamelyRamifiedRepresentation F ρ ↔
      ∀ g : wildRamificationGroup F, ρ g = LinearMap.id := by
  rfl

omit [CharZero E] in
theorem artinConductor_eq_zero_of_unramified
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsUnramifiedRepresentation F ρ) :
    artinConductor F hseparable ρ = 0 := by
  have hfixed0 : fixedSpace ρ (F.lower.group 0) = ⊤ :=
    fixedSpace.top_of_trivial_on ρ (F.lower.group 0) hρ
  have hterm : ∀ i : ℕ, lowerConductorTerm F ρ i = 0 := by
    intro i
    have hfixed : fixedSpace ρ (F.lower.group i) = ⊤ := by
      apply top_unique
      rw [← hfixed0]
      exact fixedSpace.antitone ρ (F.lower.antitone (Nat.zero_le i))
    exact lowerConductorTerm_eq_zero_of_fixed_space_top F ρ i hfixed
  unfold artinConductor
  exact Finset.sum_eq_zero fun i hi => hterm i

omit [CharZero E] in
theorem swanConductor_eq_zero_of_tame
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsTamelyRamifiedRepresentation F ρ) :
    swanConductor F hseparable ρ = 0 := by
  have hfixed1 : fixedSpace ρ (F.lower.group 1) = ⊤ :=
    fixedSpace.top_of_trivial_on ρ (F.lower.group 1) hρ
  unfold swanConductor
  apply Finset.sum_eq_zero
  intro i hi
  have hi_one : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hfixed : fixedSpace ρ (F.lower.group i) = ⊤ := by
    apply top_unique
    rw [← hfixed1]
    exact fixedSpace.antitone ρ (F.lower.antitone hi_one)
  exact lowerConductorTerm_eq_zero_of_fixed_space_top F ρ i hfixed

omit [CharZero E] in
theorem artinConductor_eq_tame_of_tame
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsTamelyRamifiedRepresentation F ρ) :
    artinConductor F hseparable ρ = tameConductor F hseparable ρ := by
  rw [artinConductor_eq_tame_add_swan F hseparable ρ,
    swanConductor_eq_zero_of_tame F hseparable ρ hρ, add_zero]

omit [CharZero E] in
theorem trivialRepresentation_conductor_zero
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsTrivialRepresentation ρ) :
    artinConductor F hseparable ρ = 0 := by
  apply artinConductor_eq_zero_of_unramified F hseparable ρ
  intro g
  simpa using hρ g

omit [CharZero E] in
theorem nontrivial_one_dimensional_tame_character_conductor_one
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V)
    (hρ : IsNontrivialTameCharacter F ρ) :
    artinConductor F hseparable ρ = 1 := by
  have hnotfixed : fixedSpace ρ (inertiaGroup F) ≠ ⊤ := by
    intro htop
    apply hρ.2.2
    intro g
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixedSpace ρ (inertiaGroup F) := by
      rw [htop]
      exact Submodule.mem_top
    exact (fixedSpace.mem_iff ρ (inertiaGroup F) v).mp hv g
  have hcodim_ne : fixedSpaceCodim ρ (inertiaGroup F) ≠ 0 :=
    (fixedSpaceCodim.eq_zero_iff ρ (inertiaGroup F)).not.mpr hnotfixed
  have hcodim_pos : 1 ≤ fixedSpaceCodim ρ (inertiaGroup F) :=
    Nat.one_le_iff_ne_zero.mpr hcodim_ne
  have hcodim_le : fixedSpaceCodim ρ (inertiaGroup F) ≤ 1 := by
    rw [← hρ.1]
    exact Submodule.finrank_quotient_le _
  have hcodim : fixedSpaceCodim ρ (inertiaGroup F) = 1 :=
    Nat.le_antisymm hcodim_le hcodim_pos
  rw [artinConductor_eq_tame_of_tame F hseparable ρ hρ.2.1]
  change (fixedSpaceCodim ρ (F.lower.group 0) : ℚ) = 1
  simpa [inertiaGroup] using congrArg (fun n : ℕ => (n : ℚ)) hcodim

omit [CharZero E] in
theorem unique_upper_break_swan_eq_break
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {r : ℝ}
    (_hρ : IsOneDimensionalRepresentation ρ)
    (hbreak : HasUniqueUpperBreak F ρ r) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = r := by
  have hsubset : Set.Ioo (0 : ℝ) r ⊆ Set.Ici 0 := by
    intro v hv
    exact le_of_lt hv.1
  have hzero_ae : ∀ᵐ v : ℝ ∂volume,
      v ∈ Set.Ici 0 \ Set.Ioo (0 : ℝ) r →
        upperFixedSpaceFunction F ρ v = 0 := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0,
      Measure.ae_ne (volume : Measure ℝ) r] with v hv0 hvrne hmem
    have hvpos : 0 < v := lt_of_le_of_ne hmem.1 (Ne.symm hv0)
    have hvr : r < v := by
      by_contra hnot
      have hle : v ≤ r := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hmem.2 ⟨hvpos, hlt⟩
      · exact hvrne heq
    rw [upperFixedSpaceFunction]
    exact hbreak.2.2 hvr
  have harea : upperDepthArea F ρ = r := by
    unfold upperDepthArea
    have hmeas : MeasurableSet (Set.Ici (0 : ℝ)) := measurableSet_Ici
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := (volume : Measure ℝ))
      (f := upperFixedSpaceFunction F ρ) (s := Set.Ioo (0 : ℝ) r)
      (t := Set.Ici (0 : ℝ)) hmeas.nullMeasurableSet hsubset hzero_ae]
    calc
      (∫ v in Set.Ioo (0 : ℝ) r, upperFixedSpaceFunction F ρ v) =
          ∫ v in Set.Ioo (0 : ℝ) r, (fun _ => (1 : ℝ)) v := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [upperFixedSpaceFunction, hbreak.2.1 hv.1.le hv.2]
      _ = r := by
        rw [setIntegral_const,
          Real.volume_real_Ioo_of_le hbreak.1.le]
        simp
  calc
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = upperDepthArea F ρ :=
      swanConductor_eq_upperDepthArea F hseparable ρ
    _ = r := harea

omit [CharZero E] in
theorem unique_upper_break_artin_eq_break_add_one
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {r : ℝ}
    (hρ : IsOneDimensionalRepresentation ρ)
    (hbreak : HasUniqueUpperBreak F ρ r) :
    ((artinConductor F hseparable ρ : ℚ) : ℝ) = r + 1 := by
  have hzero : (0 : ℝ) ≤ 0 := le_rfl
  have hcodim_real : fixedSpaceCodimReal ρ (F.lower.group 0) = 1 := by
    have h := hbreak.2.1 (v := (0 : ℝ)) hzero hbreak.1
    simpa only [F.upper.group_zero_eq_lower_zero] using h
  have hdim : Module.finrank E V = 1 := hρ
  have hcodim_le : fixedSpaceCodim ρ (F.lower.group 0) ≤ 1 := by
    rw [← hdim]
    exact Submodule.finrank_quotient_le _
  have hcodim_ge : 1 ≤ fixedSpaceCodim ρ (F.lower.group 0) := by
    have hreal : (1 : ℝ) ≤ (fixedSpaceCodim ρ (F.lower.group 0) : ℝ) := by
      change (1 : ℝ) ≤ fixedSpaceCodimReal ρ (F.lower.group 0)
      rw [hcodim_real]
    exact_mod_cast hreal
  have hcodim : fixedSpaceCodim ρ (F.lower.group 0) = 1 := by
    exact Nat.le_antisymm hcodim_le hcodim_ge
  have htame : ((tameConductor F hseparable ρ : ℚ) : ℝ) = 1 := by
    rw [tameConductor_eq_inertia_codimension]
    change ((fixedSpaceCodim ρ (F.lower.group 0) : ℚ) : ℝ) = 1
    rw [hcodim]
    norm_num
  calc
    ((artinConductor F hseparable ρ : ℚ) : ℝ) =
        ((tameConductor F hseparable ρ : ℚ) : ℝ) +
          ((swanConductor F hseparable ρ : ℚ) : ℝ) := by
      rw [artinConductor_eq_tame_add_swan]
      norm_num [Rat.cast_add]
    _ = 1 + r := by
      rw [htame, unique_upper_break_swan_eq_break F hseparable ρ hρ hbreak]
    _ = r + 1 := by ring

omit [CharZero E] in
theorem unique_upper_break_conductors
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {r : ℝ}
    (hρ : IsOneDimensionalRepresentation ρ)
    (hbreak : HasUniqueUpperBreak F ρ r) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = r ∧
      ((artinConductor F hseparable ρ : ℚ) : ℝ) = r + 1 := by
  constructor
  · exact unique_upper_break_swan_eq_break F hseparable ρ hρ hbreak
  · exact unique_upper_break_artin_eq_break_add_one F hseparable ρ hρ hbreak

end
end LastLib.Book03RamificationTheory.Chapter10
