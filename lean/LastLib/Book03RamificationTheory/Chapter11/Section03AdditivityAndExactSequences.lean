import LastLib.Book03RamificationTheory.Chapter11.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open CategoryTheory

/-! ## 11.3. Additivity and exact sequences -/

/-- The same conductor API on Mathlib's finite-dimensional representation object. -/
abbrev chapter11ArtinConductorFD
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V : FDRep k G) : ℚ :=
  chapter11ArtinConductor D V.ρ

abbrev chapter11TameConductorFD
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V : FDRep k G) : ℚ :=
  chapter11TameConductor D V.ρ

abbrev chapter11SwanConductorFD
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V : FDRep k G) : ℚ :=
  chapter11SwanConductor D V.ρ

/-- The product model of a direct sum of two representations. -/
noncomputable def chapter11DirectSumRepresentation
    {k G V W : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) :
    Representation k G (V × W) :=
  Representation.prod ρ σ

/-- The categorical direct sum of two finite-dimensional representations. -/
abbrev chapter11DirectSumFDRep
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (V W : FDRep k G) : FDRep k G := V ⊞ W

/-- Twist a representation by a one-dimensional character. -/
def chapter11Twist
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (χ : G →* kˣ) (ρ : Representation k G V) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by
    simp
  map_mul' g h := by
    ext
    simp [MonoidHom.map_mul, smul_smul, mul_comm]

/-- A character is unramified when it is trivial on inertia. -/
def chapter11UnramifiedCharacter
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (χ : G →* kˣ) : Prop :=
  ∀ σ : D.inertia, χ σ = 1

/-- A short exact sequence in the finite-dimensional representation category. -/
structure Chapter11ShortExactRepresentation
    (k G : Type*) [Field k] [CharZero k] [Fintype G] [Group G] where
  sequence : ShortComplex (FDRep k G)
  short_exact : sequence.ShortExact

/-- A splitting datum for a short exact representation sequence. -/
def Chapter11SplitShortExact
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (S : ShortComplex (FDRep k G)) : Prop :=
  ∃ (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂),
    S.f ≫ r = 𝟙 S.X₁ ∧
      s ≫ S.g = 𝟙 S.X₃ ∧
      r ≫ S.f + S.g ≫ s = 𝟙 S.X₂

theorem chapter11_short_exact_representation_splits
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (S : Chapter11ShortExactRepresentation k G) :
    Chapter11SplitShortExact S.sequence := by
  sorry

theorem chapter11_artin_conductor_direct_sum
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V W : FDRep k G) :
    chapter11ArtinConductorFD D (chapter11DirectSumFDRep V W) =
      chapter11ArtinConductorFD D V + chapter11ArtinConductorFD D W := by
  sorry

theorem chapter11_swan_conductor_direct_sum
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (V W : FDRep k G) :
    chapter11SwanConductorFD D (chapter11DirectSumFDRep V W) =
      chapter11SwanConductorFD D V + chapter11SwanConductorFD D W := by
  sorry

/-- Artin conductors are additive in a short exact sequence of finite-dimensional representations. -/
theorem chapter11_artin_conductor_short_exact_additive
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (S : Chapter11ShortExactRepresentation k G) :
    chapter11ArtinConductorFD D S.sequence.X₂ =
      chapter11ArtinConductorFD D S.sequence.X₁ +
        chapter11ArtinConductorFD D S.sequence.X₃ := by
  sorry

theorem chapter11_swan_conductor_short_exact_additive
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (S : Chapter11ShortExactRepresentation k G) :
    chapter11SwanConductorFD D S.sequence.X₂ =
      chapter11SwanConductorFD D S.sequence.X₁ +
        chapter11SwanConductorFD D S.sequence.X₃ := by
  sorry

/-- Duality preserves the codimension of every finite-group fixed space. -/
theorem chapter11_fixed_space_codimension_dual
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V)
    (H : Subgroup G) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ.dual H =
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ H := by
  sorry

theorem chapter11_artin_conductor_dual
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11ArtinConductor D ρ.dual = chapter11ArtinConductor D ρ := by
  sorry

theorem chapter11_swan_conductor_dual
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11SwanConductor D ρ.dual = chapter11SwanConductor D ρ := by
  sorry

/-- The restriction of an unramified twist to inertia is the original restriction. -/
theorem chapter11_unramified_twist_restricts_to_same_inertia_representation
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (χ : G →* kˣ) (hχ : chapter11UnramifiedCharacter D χ) :
    (chapter11Twist χ ρ).comp D.inertia.subtype =
      ρ.comp D.inertia.subtype := by
  sorry

theorem chapter11_artin_conductor_unramified_twist
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (χ : G →* kˣ) (hχ : chapter11UnramifiedCharacter D χ) :
    chapter11ArtinConductor D (chapter11Twist χ ρ) =
      chapter11ArtinConductor D ρ := by
  sorry

theorem chapter11_swan_conductor_unramified_twist
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (χ : G →* kˣ) (hχ : chapter11UnramifiedCharacter D χ) :
    chapter11SwanConductor D (chapter11Twist χ ρ) =
      chapter11SwanConductor D ρ := by
  sorry

/-- The levelwise restriction data which is needed for a ramified twist. -/
def chapter11RamifiedTwistLevelCharacter
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (χ : G →* kˣ) (i : ℕ) :
    D.lower i →* kˣ :=
  χ.comp (D.lower i).subtype

theorem chapter11_ramified_twist_has_nontrivial_level_data
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (χ : G →* kˣ)
    (hχ : ¬chapter11UnramifiedCharacter D χ) :
    ∃ i : ℕ, chapter11RamifiedTwistLevelCharacter D χ i ≠ 1 := by
  sorry

/- The source warning is exposed by `chapter11RamifiedTwistLevelCharacter`: a
  ramified-twist formula needs the restrictions to the lower ramification
  groups, not merely the two separate conductor exponents. -/

end
end LastLib.Book03RamificationTheory.Chapter11
