import LastLib.Book03RamificationTheory.Chapter11.Section01WhyTheWeightedSumIsAnInteger

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
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
    (∀ u : ℚ, r < u → ∀ g : G, g ∈ upper u → χ g = 1) ∧
    ∃ g : G, g ∈ upper r ∧ χ g ≠ 1

structure Chapter11UpperRamificationData
    {G : Type*} [Fintype G] [CommGroup G]
    (D : Chapter11RamificationData G) where
  upper : ℚ → Subgroup G
  upperRight : ℚ → Subgroup G
  upperRight_le_upper : ∀ r, upperRight r ≤ upper r
  /-- Later upper groups lie in the stable right-hand group at an earlier
      index.  This is the filtration fact that turns triviality on
      `upperRight r` into triviality above `r`. -/
  upper_later_le_right : ∀ {r u : ℚ}, r < u → upper u ≤ upperRight r
  upper_break_character_formula :
    ∀ {r : ℚ} (χ : G →* ℂˣ), D.residue_separable → 0 ≤ r →
      Chapter11HasLargestUpperBreak upper upperRight χ r →
        chapter11ArtinConductor D (chapter11OneDimensionalRepresentation χ) = r + 1

def Chapter11UpperRamificationData.IsUpperBreak
    {G : Type*} [Fintype G] [CommGroup G]
    {D : Chapter11RamificationData G}
    (U : Chapter11UpperRamificationData D) (r : ℚ) : Prop :=
  0 ≤ r ∧ U.upper r ≠ U.upperRight r

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

/-!
The abstract filtration in `Dependencies.lean` does not by itself encode the
local-field congruences used in Artin's integrality proof.  The following
predicate is the explicit input supplied by that earlier local theory.  It is
strictly weaker than asking the Artin class function to be an actual
character, and so does not make the integrality theorem circular.  It is a
virtual-character input on the inertia subgroup, as required by the induction
step below.
-/
def Chapter11RamificationCharacterInput
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Prop :=
  Chapter11IntegralVirtualCharacter
    (G := D.inertia)
    (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ)

/-- Induction of a class function from a finite-index subgroup, using the normalized
sum over the ambient group. -/
def chapter11InducedClassFunction
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
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
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinClassFunction (k := k) D =
      chapter11InducedClassFunction (k := k) D.inertia
        (chapter11InertiaClassFunction (k := k) D) := by
  sorry

/-- The augmentation-shaped class function attached to a subgroup; when the
    subgroup is normal it is the augmentation character of the quotient. -/
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
  /-- The coefficient of the trivial character, omitted by a pure
      augmentation sum but needed for an arbitrary cyclic restriction. -/
  trivial_coefficient : ℤ
  terms : Finset (Subgroup C)
  coefficient : Subgroup C → ℤ
  normal : ∀ N, N ∈ terms → N.Normal
  equation :
    b = fun c ↦ (trivial_coefficient : ℚ) +
      ∑ N ∈ terms,
        (coefficient N : ℚ) * chapter11AugmentationCharacter N c

/-- The integral cyclic-restriction shadow of the character criterion. -/
def Chapter11CyclicAugmentationCondition
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ C : Subgroup G, IsCyclic C →
    Nonempty
      (Chapter11IntegralAugmentationDecomposition (fun c : C ↦ A (c : G)))

/-!
The character criterion used in the source is an elementary-subgroup
criterion, not a cyclic-subgroup criterion.  We spell out a finite
`p`-elementary subgroup as an internal product of a cyclic prime-to-`p`
subgroup and a `p`-group.  The commuting-product formulation avoids choosing
an external product equivalence.
-/
def Chapter11ElementarySubgroup
    {G : Type*} [Fintype G] [Group G] (H : Subgroup G) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ ∃ C P : Subgroup G,
    IsCyclic C ∧ IsPGroup p P ∧ Nat.Coprime (Nat.card C) p ∧
      C ≤ H ∧ P ≤ H ∧ H = C ⊔ P ∧
        ∀ c : C, ∀ q : P, (c : G) * (q : G) = (q : G) * (c : G)

def Chapter11ElementaryRestrictionCondition
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ H : Subgroup G, Chapter11ElementarySubgroup H →
    Chapter11IntegralVirtualCharacter (fun h : H ↦ A (h : G))

/-!
This certificate is the non-circular local input for the canonical profile
adapter in `Dependencies.lean`.  It records the elementary restrictions only;
the Artin-character conclusion is still produced by the theorem below.
-/
structure Chapter11CanonicalArtinInput
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) where
  elementary_restriction :
    Chapter11ElementaryRestrictionCondition
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ)

def Chapter11IntegerValuedClassFunction
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ g : G, ∃ z : ℤ, (z : ℚ) = A g

def Chapter11ConjugacyInvariantClassFunction
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ g h : G, A (h * g * h⁻¹) = A g

/- The Galois-law input for a rational-valued class function.  For a rational
  function this is exactly invariance under powering by an exponent prime to
  the element order. -/
def Chapter11PowerInvariantClassFunction
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∀ (g : G) (n : ℕ), Nat.Coprime n (orderOf g) → A (g ^ n) = A g

/- A virtual character restricts to an integral rational character on every
  cyclic subgroup.  Augmentation characters give a convenient basis for the
  nontrivial rational part, while `trivial_coefficient` handles the trivial
  part. -/
theorem chapter11_integral_virtual_character_implies_cyclic_augmentation
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ)
    (hA : Chapter11IntegralVirtualCharacter A) :
    Chapter11CyclicAugmentationCondition A := by
  sorry

/- The source's character criterion is recorded as an explicit reusable
   elementary-subgroup bridge. -/
theorem chapter11_integral_virtual_character_iff_elementary_restriction
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ)
    (hinteger : Chapter11IntegerValuedClassFunction A)
    (hclass : Chapter11ConjugacyInvariantClassFunction A)
    (hpower : Chapter11PowerInvariantClassFunction A) :
    Chapter11IntegralVirtualCharacter A ↔
      Chapter11ElementaryRestrictionCondition A := by
  sorry

theorem chapter11_ramification_class_function_integer_valued
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11IntegerValuedClassFunction (chapter11RamificationClassFunction D) := by
  sorry

theorem chapter11_ramification_class_function_conjugacy_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11ConjugacyInvariantClassFunction
      (chapter11RamificationClassFunction D) := by
  sorry

theorem chapter11_ramification_class_function_power_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11PowerInvariantClassFunction
      (chapter11RamificationClassFunction D) := by
  sorry

theorem chapter11_inertia_class_function_integer_valued
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11IntegerValuedClassFunction
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ) := by
  sorry

theorem chapter11_inertia_class_function_conjugacy_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11ConjugacyInvariantClassFunction
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ) := by
  sorry

theorem chapter11_inertia_class_function_power_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11PowerInvariantClassFunction
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ) := by
  sorry

/-- The finite totally ramified inertia-layer ramification-character lemma.
   The elementary-restriction premise is the genuinely local input omitted by
   the abstract finite-filtration record. -/
theorem chapter11_ramification_character_lemma
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (helementary : Chapter11ElementaryRestrictionCondition
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ)) :
    Chapter11RamificationCharacterInput D := by
  sorry

theorem chapter11_canonical_artin_input_character_input
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (hinput : Chapter11CanonicalArtinInput D) :
    Chapter11RamificationCharacterInput D := by
  sorry

theorem chapter11_chapter05_adapter_character_input
    {G : Type*} [Fintype G] [Group G]
    (P : Chapter05RamificationFiltration G)
    (C : Chapter11CanonicalRamificationContext P)
    (hinput : Chapter11CanonicalArtinInput
      (chapter11RamificationDataOfChapter05 P C)) :
    Chapter11RamificationCharacterInput
      (chapter11RamificationDataOfChapter05 P C) := by
  sorry

theorem chapter11_ramification_class_function_is_integral_virtual
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (helementary : Chapter11ElementaryRestrictionCondition
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ)) :
    Chapter11RamificationCharacterInput D := by
  exact chapter11_ramification_character_lemma D helementary

/-- Artin's theorem: the Artin class function is an actual complex character.

The abstract finite-filtration record receives the preceding local
ramification-character theorem as `hvirtual`; this keeps that theorem from
being smuggled into the present statement as an unproved consequence of
subgroup axioms alone. -/
theorem chapter11_artin_integrality_theorem
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (hseparable : D.residue_separable)
    (hperfect : D.residue_perfect)
    (hvirtual : Chapter11RamificationCharacterInput D) :
    Chapter11IsCharacter (chapter11ArtinClassFunction D : G → ℂ) := by
  sorry

def Chapter11NonnegativeInteger (x : ℚ) : Prop :=
  ∃ n : ℕ, (n : ℚ) = x

theorem chapter11_artin_conductor_is_nonnegative_integer
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) (hperfect : D.residue_perfect)
    (hvirtual : Chapter11RamificationCharacterInput D) :
    Chapter11NonnegativeInteger (chapter11ArtinConductor D ρ) := by
  sorry

theorem chapter11_swan_conductor_is_nonnegative_integer
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) (hperfect : D.residue_perfect)
    (hvirtual : Chapter11RamificationCharacterInput D) :
    Chapter11NonnegativeInteger (chapter11SwanConductor D ρ) := by
  sorry

theorem chapter11_swan_conductor_eq_artin_sub_tame
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11SwanConductor D ρ =
      chapter11ArtinConductor D ρ - chapter11TameConductor D ρ := by
  sorry

theorem chapter11_artin_conductor_eq_tame_add_swan
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) :
    chapter11ArtinConductor D ρ =
      chapter11TameConductor D ρ + chapter11SwanConductor D ρ := by
  sorry

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
    (hseparable : D.residue_separable) (hr : 0 ≤ r)
    (hχ : Chapter11HasLargestUpperBreak U.upper U.upperRight χ r) :
    chapter11ArtinConductor D (chapter11OneDimensionalRepresentation χ) = r + 1 := by
  exact U.upper_break_character_formula χ hseparable hr hχ

/-- Hasse--Arf in the abelian case: every upper break is integral. -/
theorem chapter11_hasse_arf_upper_break_integer
    {G : Type*} [Fintype G] [CommGroup G]
    {D : Chapter11RamificationData G}
    (U : Chapter11UpperRamificationData D) {r : ℚ}
    (hr : U.IsUpperBreak r) (hperfect : D.residue_perfect)
    (hvirtual : Chapter11RamificationCharacterInput D) :
    ∃ z : ℤ, r = z := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter11
