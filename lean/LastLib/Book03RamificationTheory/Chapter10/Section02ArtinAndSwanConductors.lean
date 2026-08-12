import LastLib.Book03RamificationTheory.Chapter10.Section01WhatAConductorShouldMeasure

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## 10.2. Artin and Swan conductors -/

universe u v w

variable {E : Type u} {G : Type v} {V : Type w}
variable [Field E] [Group G] [Fintype G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

/-- The codimension of the fixed space at a lower-numbered group. -/
def lowerFixedSpaceCodim
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) : ℕ :=
  fixedSpaceCodim ρ (F.lower.group i)

def lowerFixedSpaceCodimRat
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) : ℚ :=
  (lowerFixedSpaceCodim F ρ i : ℚ)

/-- The single lower-numbered contribution to the Artin conductor. -/
def lowerConductorTerm
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) : ℚ :=
  F.lower.weight i * lowerFixedSpaceCodimRat F ρ i

/--
The Artin conductor exponent.  The displayed finite sum is the source's
`∑ i ≥ 0`: the chosen cutoff makes every omitted term zero.
-/
def artinConductor
    (F : RamificationFiltration G) (_hseparable : F.residue_separable)
    (ρ : Representation E G V) : ℚ :=
  ∑ i ∈ Finset.range (F.lower.cutoff + 1), lowerConductorTerm F ρ i

/-- The tame part, namely the codimension of inertia invariants. -/
def tameConductor
    (F : RamificationFiltration G) (_hseparable : F.residue_separable)
    (ρ : Representation E G V) : ℚ :=
  lowerFixedSpaceCodimRat F ρ 0

/-- The Swan conductor, retaining only the positive lower-numbered groups. -/
def swanConductor
    (F : RamificationFiltration G) (_hseparable : F.residue_separable)
    (ρ : Representation E G V) : ℚ :=
  ∑ i ∈ Finset.Ico 1 (F.lower.cutoff + 1), lowerConductorTerm F ρ i

@[simp] theorem lowerConductorTerm_eq_weight_mul_codimension
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) :
    lowerConductorTerm F ρ i =
      F.lower.weight i * lowerFixedSpaceCodimRat F ρ i := rfl

@[simp] theorem tameConductor_eq_inertia_codimension
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    tameConductor F hseparable ρ = fixedSpaceCodimRat ρ (inertiaGroup F) := by
  rfl

theorem lower_weight_increment_is_upper_depth
    (F : RamificationFiltration G) {i : ℕ} (hi : i < F.lower.cutoff) :
    F.upper.depth (i + 1) - F.upper.depth i = (F.lower.weight (i + 1) : ℝ) :=
  F.upper.depth_step hi

theorem artinConductor_eq_tame_add_swan
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    artinConductor F hseparable ρ =
      tameConductor F hseparable ρ + swanConductor F hseparable ρ := by
  sorry

theorem artinConductor_eq_full_lower_sum
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {N : ℕ} (hN : F.lower.cutoff ≤ N) :
    artinConductor F hseparable ρ =
      ∑ i ∈ Finset.range (N + 1), lowerConductorTerm F ρ i := by
  sorry

theorem swanConductor_eq_full_positive_lower_sum
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) {N : ℕ} (hN : F.lower.cutoff ≤ N) :
    swanConductor F hseparable ρ =
      ∑ i ∈ Finset.Ico 1 (N + 1), lowerConductorTerm F ρ i := by
  sorry

theorem lowerConductorTerm_nonnegative
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ) :
    0 ≤ lowerConductorTerm F ρ i := by
  sorry

theorem artinConductor_nonnegative
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    0 ≤ artinConductor F hseparable ρ := by
  sorry

theorem tameConductor_nonnegative
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    0 ≤ tameConductor F hseparable ρ := by
  sorry

theorem swanConductor_nonnegative
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    0 ≤ swanConductor F hseparable ρ := by
  sorry

theorem lowerConductorTerm_eq_zero_of_fixed_space_top
    (F : RamificationFiltration G) (ρ : Representation E G V) (i : ℕ)
    (hfixed : fixedSpace ρ (F.lower.group i) = ⊤) :
    lowerConductorTerm F ρ i = 0 := by
  sorry

/-- The upper-depth-area form of Swan, with the integral over `[0, ∞)`. -/
theorem swanConductor_eq_upperDepthArea
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) = upperDepthArea F ρ := by
  sorry

theorem swanConductor_eq_upper_depth_integral
    (F : RamificationFiltration G) (hseparable : F.residue_separable)
    (ρ : Representation E G V) :
    ((swanConductor F hseparable ρ : ℚ) : ℝ) =
      ∫ v in Set.Ici (0 : ℝ), fixedSpaceCodimReal ρ (F.upper.group v) := by
  sorry

/-- The fixed-space codimension function is stepwise constant and eventually
zero; endpoint choices do not affect its upper-depth integral. -/
theorem upper_fixed_space_function_is_step_with_finite_support
    (F : RamificationFiltration G) (ρ : Representation E G V) :
    (∃ B : ℝ, ∀ v, B ≤ v → upperFixedSpaceFunction F ρ v = 0) ∧
      (∀ {i : ℕ} {v w : ℝ}, i < F.lower.cutoff →
        F.upper.depth i < v → v ≤ F.upper.depth (i + 1) →
        F.upper.depth i < w → w ≤ F.upper.depth (i + 1) →
        upperFixedSpaceFunction F ρ v = upperFixedSpaceFunction F ρ w) := by
  sorry

theorem upper_fixed_space_function_endpoint_values_irrelevant
    (F : RamificationFiltration G) (ρ : Representation E G V)
    {f : ℝ → ℝ}
    (hf : ∀ᵐ v ∂volume.restrict (Set.Ici (0 : ℝ)),
      f v = upperFixedSpaceFunction F ρ v) :
    (∫ v in Set.Ici (0 : ℝ), f v) = upperDepthArea F ρ := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter10
