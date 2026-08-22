import LastLib.Book03RamificationTheory.Chapter01.Section04TameAndWild

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.5. The maximal tame stage -/

/-- The fixed field of wild inertia is the canonical candidate for the maximal
tame subextension. -/
def chapter01MaximalTameSubextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : Subgroup (chapter01GaloisGroup K L)) : IntermediateField K L :=
  chapter01FixedField W

/-- The wild lower group is normal once the selected branch is globally
preserved, so its fixed field is canonical inside `L/K`. -/
theorem chapter01_wild_inertia_normal_in_ambient_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : Subgroup (chapter01GaloisGroup K L))
    (hconj : ∀ g : chapter01GaloisGroup K L, ∀ w : W,
      g * (w : chapter01GaloisGroup K L) * g⁻¹ ∈ W) :
    W.Normal := by
  refine ⟨?_⟩
  intro w hw g
  exact hconj g ⟨w, hw⟩

/-- Conjugation-invariant wild inertia gives a well-defined fixed field. -/
theorem chapter01_maximal_tame_subextension_fixed_field
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : Subgroup (chapter01GaloisGroup K L))
    (_hnormal : W.Normal) :
    chapter01MaximalTameSubextension W = IntermediateField.fixedField W := by
  rfl

/-- The three cuts in the Galois field tower. -/
structure Chapter01ThreeStageDecomposition
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I W : Subgroup (chapter01GaloisGroup K L))
    [I.Normal] [W.Normal]
    (f p : ℕ) where
  wild_le_inertia : W ≤ I
  unramifiedField : IntermediateField K L
  tameField : IntermediateField K L
  residue_degree_positive : 0 < f
  unramified_eq_fixed_inertia :
    unramifiedField = chapter01FixedField I
  tame_eq_fixed_wild :
    tameField = chapter01FixedField W
  unramified_le_tame : unramifiedField ≤ tameField
  unramified_degree : Module.finrank K unramifiedField = f
  tame_degree :
    letI := (IntermediateField.inclusion unramified_le_tame).toAlgebra
    Module.finrank unramifiedField tameField = Nat.card I / Nat.card W
  wild_degree : Module.finrank tameField L = Nat.card W
  tame_stage_prime_to_p : Nat.Coprime (Nat.card I / Nat.card W) p
  wild_stage_p_primary : chapter01PPrimaryOrder W p

/-- The maximal tame stage theorem in a defectless, separable-residue profile. -/
-- SOURCE_ISSUE: The source assigns the degrees `f`, `|G₀/G₁|`, and `|G₁|`
-- without an explicit defectless hypothesis.  The interface below retains
-- the degree equality through `hdefectless`; a perfect base residue field is
-- a standard sufficient replacement.
-- LOCAL_DEPENDENCY_GUESS: `hprofile` is the group-level package that a
-- valuation instantiation must identify with the canonical inertia and first
-- lower ramification groups from Sections 1.2–1.3.
theorem chapter01_maximal_tame_subextension_exists
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [IsGalois K L] [Finite (chapter01GaloisGroup K L)]
    [FiniteDimensional k l] [IsGalois k l]
    (A : ValuationSubring L)
    (_hdecomposition : chapter01DecompositionGroup K A = ⊤)
    (I W : Subgroup (chapter01GaloisGroup K L)) [I.Normal] [W.Normal]
    (_hI : I = chapter01InertiaGroupInG K A)
    (_hW : W = chapter01WildInertiaGroupInG K A)
    (f p : ℕ)
    (hprofile : Chapter01TameWildProfile
      (chapter01GaloisGroup K L) I W p (Nat.card I))
    (_hresidue_separable : Algebra.IsSeparable k l)
    (hdefectless : Module.finrank K L = Nat.card I * f)
    (hresidue_degree : Nat.card (Gal(l / k)) = f) :
    Nonempty (Chapter01ThreeStageDecomposition K L I W f p) := by
  let U : IntermediateField K L := chapter01FixedField I
  let T : IntermediateField K L := chapter01FixedField W
  have hIdegree : Module.finrank (chapter01FixedField I) L = Nat.card I :=
    IntermediateField.finrank_fixedField_eq_card I
  have hWdegree : Module.finrank (chapter01FixedField W) L = Nat.card W :=
    IntermediateField.finrank_fixedField_eq_card W
  have hIpos : 0 < Nat.card I := Nat.card_pos
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hfpos : 0 < f := by
    rw [← hresidue_degree]
    exact Nat.card_pos
  have hUdegree : Module.finrank K U = f := by
    apply Nat.eq_of_mul_eq_mul_right hIpos
    have hprod := Module.finrank_mul_finrank K U L
    change Module.finrank K U * Module.finrank U L = Module.finrank K L at hprod
    rw [show U = chapter01FixedField I from rfl,
      show Module.finrank U L = Nat.card I from hIdegree, hdefectless] at hprod
    calc
      Module.finrank K U * Nat.card I = Nat.card I * f := hprod
      _ = f * Nat.card I := Nat.mul_comm _ _
  have hTdegree : Module.finrank K T = Nat.card I / Nat.card W * f := by
    apply Nat.eq_of_mul_eq_mul_right hWpos
    have hprod := Module.finrank_mul_finrank K T L
    change Module.finrank K T * Module.finrank T L = Module.finrank K L at hprod
    rw [show T = chapter01FixedField W from rfl,
      show Module.finrank T L = Nat.card W from hWdegree, hdefectless] at hprod
    calc
      Module.finrank K T * Nat.card W = Nat.card I * f := hprod
      _ = (Nat.card W * (Nat.card I / Nat.card W)) * f :=
        congrArg (fun n => n * f) hprofile.order_factor
      _ = (Nat.card I / Nat.card W * f) * Nat.card W := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
  have hUT : U ≤ T := by
    dsimp [U, T]
    exact IntermediateField.fixedField_le hprofile.wild_le_inertia
  let _ : Algebra U T := (IntermediateField.inclusion hUT).toAlgebra
  have hUTdegree : Module.finrank U T = Nat.card I / Nat.card W := by
    apply Nat.eq_of_mul_eq_mul_left hfpos
    have hprod := Module.finrank_mul_finrank K U T
    change Module.finrank K U * Module.finrank U T = Module.finrank K T at hprod
    rw [hUdegree, hTdegree] at hprod
    calc
      f * Module.finrank U T = (Nat.card I / Nat.card W) * f := hprod
      _ = f * (Nat.card I / Nat.card W) := Nat.mul_comm _ _
  refine ⟨{
    wild_le_inertia := hprofile.wild_le_inertia
    unramifiedField := U
    tameField := T
    residue_degree_positive := hfpos
    unramified_eq_fixed_inertia := rfl
    tame_eq_fixed_wild := rfl
    unramified_le_tame := hUT
    unramified_degree := hUdegree
    tame_degree := ?_
    wild_degree := hWdegree
    tame_stage_prime_to_p := hprofile.tame_quotient_order
    wild_stage_p_primary := hprofile.wild_order
  }⟩
  exact hUTdegree

/-- Wild inertia is a finite `p`-group in positive residue characteristic. -/
theorem chapter01_wild_stage_is_totally_wild
    {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) (p : ℕ)
    (hW : chapter01PPrimaryOrder W p) :
    ∃ r : ℕ, Nat.card W = p ^ r := hW

/-- The wild stage has no nontrivial prime-to-`p` quotient. -/
theorem chapter01_wild_stage_has_no_nontrivial_tame_quotient
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (W : Subgroup G) (p : ℕ) (ρ : G →* Q)
    (hW : chapter01PPrimaryOrder W p)
    (hQprime : Nat.Coprime (Nat.card Q) p) :
    ∀ w : W, ρ (w : G) = 1 := by
  obtain ⟨r, hr⟩ := hW
  intro w
  have hw : (w : G) ^ Nat.card W = 1 := by
    exact congrArg Subtype.val (pow_card_eq_one' (G := W) (x := w))
  have hpow : ρ (w : G) ^ (p ^ r) = 1 := by
    rw [← hr, ← map_pow]
    simpa using congrArg ρ hw
  have hd₁ : orderOf (ρ (w : G)) ∣ p ^ r :=
    orderOf_dvd_of_pow_eq_one hpow
  have hd₂ : orderOf (ρ (w : G)) ∣ Nat.card Q := by
    let _ : Fintype Q := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  have hcop : Nat.Coprime (p ^ r) (Nat.card Q) := hQprime.symm.pow_left r
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop hd₁ hd₂)

/-- In characteristic exponent one the wild stage is absent. -/
theorem chapter01_characteristic_zero_has_no_wild_stage
    {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) (hW : chapter01PPrimaryOrder W 1) :
    W = ⊥ := by
  obtain ⟨r, hr⟩ := hW
  apply (Subgroup.card_eq_one).mp
  simpa using hr

/-- A coordinate choice for a tame totally ramified stage is extra data, not a
canonical subfield construction. -/
structure Chapter01TameCoordinateChoice
    (A K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K]
    [FiniteDimensional K L] (e : ℕ) where
  uniformizer : A
  uniformizer_generates : Ideal.span ({uniformizer} : Set A) =
    IsLocalRing.maximalIdeal A
  root : L
  root_pow_eq : root ^ e = algebraMap A L uniformizer
  generates : Algebra.adjoin K ({root} : Set L) = ⊤
  roots_of_unity : ∃ ζ : K, IsPrimitiveRoot ζ e

end

end LastLib.Book03RamificationTheory.Chapter01
