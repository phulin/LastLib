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
  sorry

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
    (I W : Subgroup (chapter01GaloisGroup K L)) [I.Normal] [W.Normal]
    (f p : ℕ)
    (hprofile : Chapter01TameWildProfile
      (chapter01GaloisGroup K L) I W p (Nat.card I))
    (hresidue_separable : Algebra.IsSeparable k l)
    (hdefectless : Module.finrank K L = Nat.card I * f)
    (hresidue_degree : Nat.card (Gal(l / k)) = f) :
    Nonempty (Chapter01ThreeStageDecomposition K L I W f p) := by
  sorry

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
  sorry

/-- In characteristic exponent one the wild stage is absent. -/
theorem chapter01_characteristic_zero_has_no_wild_stage
    {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) (hW : chapter01PPrimaryOrder W 1) :
    W = ⊥ := by
  sorry

/-- The canonical tame Kummer-coordinate package from Book 2, exposed under
the chapter-facing namespace. -/
abbrev Chapter01TameKummerPresentation :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09TameKummerPresentation

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
