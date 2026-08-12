import LastLib.Book03RamificationTheory.Chapter11.Section01WhyTheWeightedSumIsAnInteger

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open scoped BigOperators

/-! ## 11.2. Artin's integrality theorem -/

/-- A one-dimensional representation attached to a multiplicative character. -/
def chapter11OneDimensionalRepresentation
    {k G : Type*} [Field k] [Group G]
    (χ : G →* kˣ) : Representation k G k where
  toFun g := (χ g : k) • LinearMap.id
  map_one' := by
    simp [Module.End.one_eq_id]
  map_mul' g h := by
    ext
    simp [MonoidHom.map_mul, mul_comm]

/-- A representation of an arbitrary group has finite image when its operator image is finite. -/
def Chapter11FiniteImage
    {Γ k V : Type*} [Group Γ] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) : Prop :=
  (Set.range fun g : Γ => ρ g).Finite

/-- A rational class function is an integral virtual character when its complex
scalar extension is a difference of finite-dimensional complex characters. -/
def Chapter11IntegralVirtualCharacter
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∃ V W : FDRep ℂ G, V.character - W.character = fun g ↦ (A g : ℂ)

/-- The complex-character formulation of being an actual finite-dimensional character. -/
def Chapter11IsCharacter
    {G : Type*} [Fintype G] [Group G] (A : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, V.character = A

/-!
Upper-numbering interface used only for the Hasse--Arf consequence.  The
character-conductor equation is the earlier Chapter 10 bridge: it is stated as
a field here so that the Chapter 11 file remains proof-ready even before the
preceding Book 3 chapters are merged.
-/

def Chapter11HasLargestUpperBreak
    {G : Type*} [Fintype G] [CommGroup G]
    (upper upperRight : ℚ → Subgroup G)
    (χ : G →* ℂˣ) (r : ℚ) : Prop :=
  (∀ g : G, g ∈ upperRight r → χ g = 1) ∧
    ∃ g : G, g ∈ upper r ∧ χ g ≠ 1

structure Chapter11UpperRamificationData
    {G : Type*} [Fintype G] [CommGroup G]
    (D : Chapter11RamificationData G) where
  upper : ℚ → Subgroup G
  upperRight : ℚ → Subgroup G
  upperRight_le_upper : ∀ r, upperRight r ≤ upper r
  upper_break_character_formula :
    ∀ (r : ℚ) (χ : G →* ℂˣ),
      Chapter11HasLargestUpperBreak upper upperRight χ r →
        chapter11ArtinConductor D (chapter11OneDimensionalRepresentation χ) = r + 1

def Chapter11UpperRamificationData.IsUpperBreak
    {G : Type*} [Fintype G] [CommGroup G]
    {D : Chapter11RamificationData G}
    (U : Chapter11UpperRamificationData D) (r : ℚ) : Prop :=
  U.upper r ≠ U.upperRight r

/-- The residue-degree-free ramification class function. -/
def chapter11RamificationClassFunction
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : G → k := by
  classical
  exact fun σ ↦ if hσ : σ = 1 then
      ∑ τ ∈ (Finset.univ.erase (1 : G)),
        (chapter11Displacement D τ : k)
    else -(chapter11Displacement D σ : k)

/-- The class function for the totally ramified inertia layer. -/
def chapter11InertiaClassFunction
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : D.inertia → k := by
  classical
  exact fun σ ↦ if hσ : σ = 1 then
      ∑ τ ∈ (Finset.univ.erase (1 : D.inertia)),
        (chapter11Displacement D (τ : G) : k)
    else -(chapter11Displacement D (σ : G) : k)

/-- Induction of a class function from a finite-index subgroup, using the normalized
sum over the ambient group. -/
def chapter11InducedClassFunction
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (I : Subgroup G) (b : I → k) : G → k := by
  classical
  exact fun g ↦ (Nat.card I : k)⁻¹ *
    ∑ x : G, if h : x⁻¹ * g * x ∈ I then
      b ⟨x⁻¹ * g * x, h⟩
    else 0

theorem chapter11_artin_class_function_eq_residue_degree_smul_ramification
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinClassFunction (k := k) D =
      (D.f : k) • chapter11RamificationClassFunction (k := k) D := by
  sorry

/-- The induction formula (11.1) for the Artin class function. -/
theorem chapter11_artin_class_function_eq_induced_inertia
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinClassFunction (k := k) D =
      chapter11InducedClassFunction (k := k) D.inertia
        (chapter11InertiaClassFunction (k := k) D) := by
  sorry

/-- The finite totally ramified ramification-character lemma. -/
theorem chapter11_ramification_character_lemma
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (htotal : D.f = 1) (hseparable : D.residue_separable) :
    Chapter11IntegralVirtualCharacter (chapter11RamificationClassFunction D) := by
  sorry

/-- The augmentation character of the finite quotient by a normal subgroup. -/
def chapter11AugmentationCharacter
    {C : Type*} [Fintype C] [Group C]
    (N : Subgroup C) : C → ℚ := by
  classical
  exact fun c ↦ if c ∈ N then
    ((Fintype.card C / Nat.card N : ℕ) : ℚ) - 1
  else -1

/-- An integral sum of augmentation characters of finite cyclic quotients. -/
structure Chapter11IntegralAugmentationDecomposition
    {C : Type*} [Fintype C] [Group C] (b : C → ℚ) where
  terms : Finset (Subgroup C)
  coefficient : Subgroup C → ℤ
  normal : ∀ N, N ∈ terms → N.Normal
  equation :
    b = fun c ↦ ∑ N ∈ terms,
      (coefficient N : ℚ) * chapter11AugmentationCharacter N c

/-- The integral cyclic-restriction condition used by the character criterion. -/
def Chapter11CyclicAugmentationCondition
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ C : Subgroup G, IsCyclic C →
    Nonempty
      (Chapter11IntegralAugmentationDecomposition (fun c : C ↦ A (c : G)))

def Chapter11IntegerValuedClassFunction
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ g : G, ∃ z : ℤ, (z : ℚ) = A g

def Chapter11ConjugacyInvariantClassFunction
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ g h : G, A (h * g * h⁻¹) = A g

/- The cyclic character criterion is kept as an explicit reusable bridge rather than
  hiding the integral-virtual-character step in the proof of the main theorem. -/
theorem chapter11_integral_virtual_character_iff_cyclic_augmentation
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ)
    (hinteger : Chapter11IntegerValuedClassFunction A)
    (hclass : Chapter11ConjugacyInvariantClassFunction A) :
    Chapter11IntegralVirtualCharacter A ↔
      Chapter11CyclicAugmentationCondition A := by
  sorry

theorem chapter11_ramification_character_cyclic_restriction
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (C : Subgroup G)
    (hC : IsCyclic C) :
    Nonempty
      (Chapter11IntegralAugmentationDecomposition
        (fun c : C ↦ chapter11RamificationClassFunction D (c : G))) := by
  sorry

theorem chapter11_ramification_class_function_is_integral_virtual
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (htotal : D.f = 1) (hseparable : D.residue_separable) :
    Chapter11IntegralVirtualCharacter (chapter11RamificationClassFunction D) := by
  exact chapter11_ramification_character_lemma D htotal hseparable

/-- Artin's theorem: the Artin class function is an actual complex character. -/
theorem chapter11_artin_integrality_theorem
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (hseparable : D.residue_separable) :
    Chapter11IsCharacter (chapter11ArtinClassFunction D : G → ℂ) := by
  sorry

def Chapter11NonnegativeInteger (x : ℚ) : Prop :=
  ∃ n : ℕ, (n : ℚ) = x

theorem chapter11_artin_conductor_is_nonnegative_integer
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) :
    Chapter11NonnegativeInteger (chapter11ArtinConductor D ρ) := by
  sorry

theorem chapter11_swan_conductor_is_nonnegative_integer
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) :
    Chapter11NonnegativeInteger (chapter11SwanConductor D ρ) := by
  sorry

theorem chapter11_swan_conductor_eq_artin_sub_tame
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11SwanConductor D ρ =
      chapter11ArtinConductor D ρ - chapter11TameConductor D ρ := by
  rfl

/-- The finite-image reduction used for representations of an absolute Galois group. -/
theorem chapter11_finite_image_quotient_is_finite
    {Γ k V : Type*} [Group Γ] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (hρ : Chapter11FiniteImage ρ) :
    Finite (Γ ⧸ MonoidHom.ker ρ) := by
  sorry

theorem chapter11_finite_image_factors_through_kernel_quotient
    {Γ k V : Type*} [Group Γ] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) :
    ∃ ρq : Representation k (Γ ⧸ MonoidHom.ker ρ) V,
      ∀ γ : Γ, ρ γ = ρq (QuotientGroup.mk' (MonoidHom.ker ρ) γ) := by
  sorry

theorem chapter11_finite_image_representation_is_computed_in_finite_quotient
    {Γ k V : Type*} [Group Γ] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (hρ : Chapter11FiniteImage ρ) :
    ∃ ρq : Representation k (Γ ⧸ MonoidHom.ker ρ) V,
      (∀ γ : Γ,
        ρ γ = ρq (QuotientGroup.mk' (MonoidHom.ker ρ) γ)) ∧
        Chapter11FiniteImage ρq := by
  sorry

/-- A nontrivial upper break in a finite abelian quotient admits a separating character. -/
theorem chapter11_exists_character_of_upper_break
    {G : Type*} [Fintype G] [CommGroup G]
    {D : Chapter11RamificationData G}
    (U : Chapter11UpperRamificationData D) {r : ℚ}
    (hr : U.IsUpperBreak r) :
    ∃ χ : G →* ℂˣ,
      Chapter11HasLargestUpperBreak U.upper U.upperRight χ r := by
  sorry

theorem chapter11_upper_break_character_has_conductor_r_plus_one
    {G : Type*} [Fintype G] [CommGroup G]
    {D : Chapter11RamificationData G}
    (U : Chapter11UpperRamificationData D) {r : ℚ} (χ : G →* ℂˣ)
    (hχ : Chapter11HasLargestUpperBreak U.upper U.upperRight χ r) :
    chapter11ArtinConductor D (chapter11OneDimensionalRepresentation χ) = r + 1 := by
  exact U.upper_break_character_formula r χ hχ

/-- Hasse--Arf in the abelian case: every upper break is integral. -/
theorem chapter11_hasse_arf_upper_break_integer
    {G : Type*} [Fintype G] [CommGroup G]
    {D : Chapter11RamificationData G}
    (U : Chapter11UpperRamificationData D) {r : ℚ}
    (hr : U.IsUpperBreak r) : ∃ z : ℤ, r = z := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter11
