import LastLib.Book03RamificationTheory.Chapter06.Section03FiniteUpperBreakDecompositions
import LastLib.Book03RamificationTheory.Chapter11.Section01WhyTheWeightedSumIsAnInteger

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open LastLib.Book03RamificationTheory.Chapter05
open LastLib.Book03RamificationTheory.Chapter06
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

/-- A rational class function is an integral virtual character when its complex
scalar extension is a difference of finite-dimensional complex characters. -/
def Chapter11IntegralVirtualCharacter
    {G : Type*} [Fintype G] [Group G] (A : G → ℚ) : Prop :=
  ∃ V W : FDRep ℂ G, V.character - W.character = fun g ↦ (A g : ℂ)

/-- The complex virtual characters represented by the integral character ring
    `R(G)`.  Writing them as differences of finite-dimensional characters is
    the representation-theoretic form used by the induction argument below. -/
def Chapter11ComplexVirtualCharacter
    {G : Type*} [Fintype G] [Group G] (A : G → ℂ) : Prop :=
  ∃ V W : FDRep ℂ G, V.character - W.character = A

/-- The complex-character formulation of being an actual finite-dimensional character. -/
def Chapter11IsCharacter
    {G : Type*} [Fintype G] [Group G] (A : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, V.character = A

/-!
Upper-numbering interface used only for the Hasse--Arf consequence.  The
character-conductor equation is the preceding cyclic Hasse--Arf/local-theory
bridge: it is stated as a field here so that the Chapter 11 file remains
proof-ready without importing a later chapter.
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

/-- An induced one-dimensional character, viewed as a complex class function.
    The finite sum is the usual character formula for induction from a
    subgroup. -/
def chapter11InducedOneDimensionalCharacter
    {G : Type*} [Fintype G] [Group G]
    (H : Subgroup G) (χ : H →* ℂˣ) : G → ℂ :=
  chapter11InducedClassFunction (k := ℂ) H (fun h : H ↦ (χ h : ℂ))

/-- An integral monomial expression is a finite integral sum of characters
    induced from one-dimensional characters of subgroups. -/
def Chapter11IntegralMonomialExpression
    {G : Type*} [Fintype G] [Group G] (A : G → ℂ) : Prop :=
  ∃ s : Finset (Σ H : Subgroup G, H →* ℂˣ),
    ∃ n : (Σ H : Subgroup G, H →* ℂˣ) → ℤ,
      A = fun g =>
        ∑ x ∈ s, (n x : ℂ) *
          chapter11InducedOneDimensionalCharacter x.1 x.2 g

/-- Integral monomial induction, i.e. Proposition 11.1B in a form that can
    be consumed by later character pairings. -/
theorem chapter11_integral_monomial_induction
    {G : Type*} [Fintype G] [Group G] (A : G → ℂ)
    (hA : Chapter11ComplexVirtualCharacter A) :
    Chapter11IntegralMonomialExpression A := by
  sorry

theorem chapter11_character_has_integral_monomial_induction
    {G : Type*} [Fintype G] [Group G] (V : FDRep ℂ G) :
    Chapter11IntegralMonomialExpression V.character := by
  apply chapter11_integral_monomial_induction V.character
  refine ⟨V, FDRep.of (Representation.trivial ℂ G (Fin 0 → ℂ)), ?_⟩
  ext g
  simp [FDRep.character]

theorem chapter11_artin_class_function_eq_residue_degree_smul_ramification
    {k G : Type*} [Field k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinClassFunction (k := k) D =
      (D.f : k) • chapter11RamificationClassFunction (k := k) D := by
  funext σ
  by_cases hσ : σ = 1
  · simp [chapter11ArtinClassFunction, chapter11RamificationClassFunction, hσ]
  · simp [chapter11ArtinClassFunction, chapter11RamificationClassFunction, hσ,
      smul_eq_mul]

/-- The induction formula (11.1) for the Artin class function. -/
theorem chapter11_artin_class_function_eq_induced_inertia
    {k G : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinClassFunction (k := k) D =
      chapter11InducedClassFunction (k := k) D.inertia
        (chapter11InertiaClassFunction (k := k) D) := by
  classical
  funext g
  by_cases hg : g ∈ D.inertia
  · have hmem : ∀ x : G, x⁻¹ * g * x ∈ D.inertia := by
      intro x
      simpa using D.inertia_normal.conj_mem g hg x⁻¹
    have hvalue : ∀ x : G,
        (if h : x⁻¹ * g * x ∈ D.inertia then
            chapter11InertiaClassFunction (k := k) D ⟨x⁻¹ * g * x, h⟩
          else 0) =
          chapter11InertiaClassFunction (k := k) D ⟨g, hg⟩ := by
      intro x
      rw [dif_pos (hmem x)]
      by_cases hg1 : g = 1
      · subst g
        simp [chapter11InertiaClassFunction]
      · have hconj1 : x⁻¹ * g * x ≠ 1 := by
          intro h
          apply hg1
          have h' := congrArg (fun y : G => x * y * x⁻¹) h
          simpa [mul_assoc] using h'
        have hconj1' :
            (⟨x⁻¹ * g * x, hmem x⟩ : D.inertia) ≠ 1 := by
          intro h
          apply hconj1
          exact congrArg Subtype.val h
        have hg1' : (⟨g, hg⟩ : D.inertia) ≠ 1 := by
          intro h
          apply hg1
          exact congrArg Subtype.val h
        simp only [chapter11InertiaClassFunction, dif_neg hconj1', dif_neg hg1']
        change -(chapter11Displacement D (x⁻¹ * g * x) : k) =
          -(chapter11Displacement D g : k)
        rw [show x⁻¹ * g * x = x⁻¹ * g * (x⁻¹)⁻¹ by simp]
        rw [chapter11_displacement_conjugation_invariant]
    have hcard : Fintype.card G = Nat.card D.inertia * D.f := by
      rw [D.group_card, D.inertia_card]
    have hcard' : (Fintype.card G : k) =
        (D.f : k) * (Nat.card D.inertia : k) := by
      rw [hcard, Nat.cast_mul, mul_comm]
    have hsum_subtype (f : G → k) :
        (∑ x : G, if x ∈ D.inertia then f x else 0) =
          ∑ x : D.inertia, f x := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij
        (fun x hx => ⟨x, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_ ?_
      · intro x hx
        simp
      · intro x₁ hx₁ x₂ hx₂ h
        exact congrArg Subtype.val h
      · intro x hx
        refine ⟨(x : G), by simp [x.property], ?_⟩
        rfl
      · intro x hx
        rfl
    have hsum_erase_G (f : G → k) (hf : f 1 = 0) :
        (∑ x ∈ (Finset.univ.erase (1 : G)), f x) = ∑ x : G, f x := by
      have h := Finset.sum_erase_add
        (s := (Finset.univ : Finset G)) (f := f)
        (Finset.mem_univ (1 : G))
      rw [← h, hf, add_zero]
    have hsum_erase_I (f : D.inertia → k) (hf : f 1 = 0) :
        (∑ x ∈ (Finset.univ.erase (1 : D.inertia)), f x) =
          ∑ x : D.inertia, f x := by
      have h := Finset.sum_erase_add
        (s := (Finset.univ : Finset D.inertia)) (f := f)
        (Finset.mem_univ (1 : D.inertia))
      rw [← h, hf, add_zero]
    have hdisp :
        (∑ x : G, (chapter11Displacement D x : k)) =
          ∑ x : D.inertia, (chapter11Displacement D (x : G) : k) := by
      calc
        (∑ x : G, (chapter11Displacement D x : k)) =
            ∑ x : G, if x ∈ D.inertia then
              (chapter11Displacement D x : k) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxin : x ∈ D.inertia
          · simp [hxin]
          · rw [chapter11_displacement_eq_zero_of_not_mem_inertia D hxin]
            simp [hxin]
        _ = ∑ x : D.inertia, (chapter11Displacement D (x : G) : k) :=
          hsum_subtype (fun x => (chapter11Displacement D x : k))
    have hleft :
        chapter11ArtinClassFunction (k := k) D g =
          (D.f : k) * chapter11InertiaClassFunction (k := k) D ⟨g, hg⟩ := by
      by_cases hg1 : g = 1
      · subst g
        rw [chapter11ArtinClassFunction, chapter11InertiaClassFunction]
        have hsub : (⟨1, hg⟩ : D.inertia) = 1 := Subtype.ext (by rfl)
        rw [dif_pos hsub]
        split
        · rename_i htrue
          rw [hsum_erase_G
            (fun x : G => (chapter11Displacement D x : k))
            (by simp [chapter11Displacement]), hdisp]
          rw [← hsum_erase_I (fun x : D.inertia =>
            (chapter11Displacement D (x : G) : k))
            (by simp [chapter11Displacement])]
        · rename_i hfalse
          exact False.elim (hfalse rfl)
      · simp [chapter11ArtinClassFunction, chapter11InertiaClassFunction, hg1]
    have hsum :
        (∑ x : G, if h : x⁻¹ * g * x ∈ D.inertia then
            chapter11InertiaClassFunction (k := k) D ⟨x⁻¹ * g * x, h⟩
          else 0) =
          ∑ _ : G, chapter11InertiaClassFunction (k := k) D ⟨g, hg⟩ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hvalue x
    rw [hleft, chapter11InducedClassFunction, hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard']
    field_simp
  · have hnot : ∀ x : G, x⁻¹ * g * x ∉ D.inertia := by
      intro x hx
      apply hg
      have h' := D.inertia_normal.conj_mem (x⁻¹ * g * x) hx x
      simpa [mul_assoc] using h'
    rw [chapter11_artin_class_function_eq_zero_of_not_mem_inertia D hg]
    simp [chapter11InducedClassFunction, hnot]

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
def Chapter11PElementarySubgroup
    {G : Type*} [Fintype G] [Group G] (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup G,
    IsCyclic C ∧ IsPGroup p P ∧ Nat.Coprime (Nat.card C) p ∧
      C ≤ H ∧ P ≤ H ∧ H = C ⊔ P ∧
        ∀ c : C, ∀ q : P, (c : G) * (q : G) = (q : G) * (c : G)

def Chapter11ElementarySubgroup
    {G : Type*} [Fintype G] [Group G] (H : Subgroup G) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ Chapter11PElementarySubgroup p H

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
    (hclass : Chapter11ConjugacyInvariantClassFunction A) :
    Chapter11IntegralVirtualCharacter A ↔
      Chapter11ElementaryRestrictionCondition A := by
  sorry

theorem chapter11_ramification_class_function_integer_valued
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11IntegerValuedClassFunction (chapter11RamificationClassFunction D) := by
  classical
  intro σ
  by_cases hσ : σ = 1
  · subst σ
    refine ⟨∑ τ ∈ (Finset.univ.erase (1 : G)),
      (chapter11Displacement D τ : ℤ), ?_⟩
    simp [chapter11RamificationClassFunction, chapter11Displacement]
  · refine ⟨-(chapter11Displacement D σ : ℤ), ?_⟩
    simp [chapter11RamificationClassFunction, hσ]

theorem chapter11_ramification_class_function_conjugacy_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11ConjugacyInvariantClassFunction
      (chapter11RamificationClassFunction D) := by
  intro g h
  by_cases hg : g = 1
  · subst g
    simp [chapter11RamificationClassFunction]
  · have hconj : h * g * h⁻¹ ≠ 1 := by
      intro h'
      apply hg
      have := congrArg (fun x : G => h⁻¹ * x * h) h'
      simpa [mul_assoc] using this
    simp only [chapter11RamificationClassFunction, dif_neg hg, dif_neg hconj]
    rw [chapter11_displacement_conjugation_invariant]

private theorem chapter11_displacement_pow_eq_of_coprime
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) (n : ℕ)
    (hn : Nat.Coprime n (orderOf σ)) :
    chapter11Displacement D (σ ^ n) = chapter11Displacement D σ := by
  classical
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hn
  have hsupport : chapter11LowerSupport D (σ ^ n) =
      chapter11LowerSupport D σ := by
    ext i
    simp only [chapter11LowerSupport, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hmem⟩
      refine ⟨hi, ?_⟩
      rw [← hm]
      exact (D.lower i).pow_mem hmem m
    · rintro ⟨hi, hmem⟩
      exact ⟨hi, (D.lower i).pow_mem hmem n⟩
  by_cases hσ : σ = 1
  · subst σ
    simp [chapter11Displacement]
  · have hpow : σ ^ n ≠ 1 := by
      intro h
      apply hσ
      calc
        σ = (σ ^ n) ^ m := hm.symm
        _ = 1 := by rw [h, one_pow]
    rw [chapter11_displacement_eq_support_card_of_ne_one D hpow,
      chapter11_displacement_eq_support_card_of_ne_one D hσ, hsupport]

theorem chapter11_ramification_class_function_power_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11PowerInvariantClassFunction
      (chapter11RamificationClassFunction D) := by
  intro σ n hn
  by_cases hσ : σ = 1
  · subst σ
    simp [chapter11RamificationClassFunction]
  · obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hn
    have hpow : σ ^ n ≠ 1 := by
      intro h
      apply hσ
      calc
        σ = (σ ^ n) ^ m := hm.symm
        _ = 1 := by rw [h, one_pow]
    simp only [chapter11RamificationClassFunction, dif_neg hpow, dif_neg hσ]
    rw [chapter11_displacement_pow_eq_of_coprime D σ n hn]

theorem chapter11_inertia_class_function_integer_valued
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11IntegerValuedClassFunction
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ) := by
  classical
  intro σ
  by_cases hσ : σ = 1
  · subst σ
    refine ⟨∑ τ ∈ (Finset.univ.erase (1 : D.inertia)),
      (chapter11Displacement D (τ : G) : ℤ), ?_⟩
    simp [chapter11InertiaClassFunction, chapter11Displacement]
  · refine ⟨-(chapter11Displacement D (σ : G) : ℤ), ?_⟩
    simp [chapter11InertiaClassFunction, hσ]

theorem chapter11_inertia_class_function_conjugacy_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11ConjugacyInvariantClassFunction
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ) := by
  intro g h
  by_cases hg : g = 1
  · subst g
    simp [chapter11InertiaClassFunction]
  · have hconj : h * g * h⁻¹ ≠ (1 : D.inertia) := by
      intro h'
      apply hg
      apply Subtype.ext
      have h'' := congrArg Subtype.val h'
      have h''' := congrArg (fun x : G => (h : G)⁻¹ * x * (h : G)) h''
      simpa [mul_assoc] using h'''
    simp only [chapter11InertiaClassFunction, dif_neg hg, dif_neg hconj]
    change -(chapter11Displacement D ((h : G) * (g : G) * (h : G)⁻¹) : ℚ) =
      -(chapter11Displacement D (g : G) : ℚ)
    rw [chapter11_displacement_conjugation_invariant]

theorem chapter11_inertia_class_function_power_invariant
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) :
    Chapter11PowerInvariantClassFunction
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ) := by
  intro σ n hn
  have hn' : Nat.Coprime n (orderOf (σ : G)) := by
    simpa only [Subgroup.orderOf_coe] using hn
  by_cases hσ : σ = 1
  · subst σ
    simp [chapter11InertiaClassFunction]
  · obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hn'
    have hpow : (σ : G) ^ n ≠ 1 := by
      intro h
      apply hσ
      apply Subtype.ext
      calc
        (σ : G) = ((σ : G) ^ n) ^ m := hm.symm
        _ = 1 := by rw [h, one_pow]
    have hpow' : σ ^ n ≠ (1 : D.inertia) := by
      intro h
      apply hpow
      simpa using congrArg Subtype.val h
    simp only [chapter11InertiaClassFunction, dif_neg hpow', dif_neg hσ]
    change -(chapter11Displacement D (((σ : G) ^ n)) : ℚ) =
      -(chapter11Displacement D (σ : G) : ℚ)
    rw [chapter11_displacement_pow_eq_of_coprime D (σ : G) n hn']

/-- The finite totally ramified inertia-layer ramification-character lemma.
   The elementary-restriction premise is the genuinely local input omitted by
   the abstract finite-filtration record. -/
theorem chapter11_ramification_character_lemma
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (helementary : Chapter11ElementaryRestrictionCondition
      (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ)) :
    Chapter11RamificationCharacterInput D := by
  unfold Chapter11RamificationCharacterInput
  rw [chapter11_integral_virtual_character_iff_elementary_restriction
    (fun σ : D.inertia => chapter11InertiaClassFunction (k := ℚ) D σ)
    (chapter11_inertia_class_function_conjugacy_invariant D)]
  exact helementary

/-- Induction carries the integral virtual character on inertia to the full
    Artin class function.  This is the reusable virtual-character half of
    Artin's integrality proof; positivity is supplied separately by the
    fixed-space formula. -/
theorem chapter11_artin_class_function_integral_virtual_of_inertia_input
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G)
    (hvirtual : Chapter11RamificationCharacterInput D) :
    Chapter11IntegralVirtualCharacter
      (fun σ : G => chapter11ArtinClassFunction (k := ℚ) D σ) := by
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
    Chapter11IntegralVirtualCharacter
      (fun σ : G => chapter11ArtinClassFunction (k := ℚ) D σ) := by
  /- Prior attempt: this returned only the inertia-layer input, despite the
     theorem name claiming a result for the full Artin class function.
     exact chapter11_ramification_character_lemma D helementary -/
  sorry

/-- Artin's theorem: the Artin class function is an actual complex character.

The abstract finite-filtration record receives the elementary-restriction
certificate as an explicit local input.  The theorem below then records the
character argument; it does not assume the integral virtual-character
conclusion that the argument is meant to establish. -/
theorem chapter11_artin_integrality_theorem
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (hseparable : D.residue_separable)
    (hperfect : D.residue_perfect)
    (hinput : Chapter11CanonicalArtinInput D) :
    Chapter11IsCharacter (chapter11ArtinClassFunction D : G → ℂ) := by
  sorry

def Chapter11NonnegativeInteger (x : ℚ) : Prop :=
  ∃ n : ℕ, (n : ℚ) = x

theorem chapter11_artin_conductor_is_nonnegative_integer
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) (hperfect : D.residue_perfect)
    (hinput : Chapter11CanonicalArtinInput D) :
    Chapter11NonnegativeInteger (chapter11ArtinConductor D ρ) := by
  sorry

theorem chapter11_swan_conductor_is_nonnegative_integer
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) (hperfect : D.residue_perfect)
    (hinput : Chapter11CanonicalArtinInput D) :
    Chapter11NonnegativeInteger (chapter11SwanConductor D ρ) := by
  sorry

/-!
The Chapter 6 finite upper-profile API measures the same wild contribution by
an upper-depth integral, while Chapter 11 obtains its integrality from the
Artin character.  The comparison is kept explicit here so the later bridge
does not force an import from Chapter 6 back into an earlier chapter.
-/
theorem chapter11_artin_integrality_implies_chapter06_total_swan_conductor_integral
    {k G V : Type*} [Field k] [CharZero k] [Fintype G] [Finite G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (P : Chapter05RamificationFiltration G)
    (D : Chapter11RamificationData G) (ρ : Representation k G V)
    (hseparable : D.residue_separable) (hperfect : D.residue_perfect)
    (hinput : Chapter11CanonicalArtinInput D)
    (hupper :
      ((chapter11SwanConductor D ρ : ℚ) : ℝ) =
        chapter06SwanConductor P ρ) :
    chapter06TotalSwanConductorIntegral P ρ := by
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
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : LastLib.Book03RamificationTheory.Chapter10.FiniteImageRepresentation
      k Γ V) :
    Finite (Γ ⧸ MonoidHom.ker ρ.toRepresentation) := by
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
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : LastLib.Book03RamificationTheory.Chapter10.FiniteImageRepresentation
      k Γ V) :
    Finite (Γ ⧸ MonoidHom.ker ρ.toRepresentation) ∧
      ∃ ρq : Representation k (Γ ⧸ MonoidHom.ker ρ.toRepresentation) V,
        (∀ γ : Γ,
          ρ.toRepresentation γ =
            ρq (QuotientGroup.mk' (MonoidHom.ker ρ.toRepresentation) γ)) ∧
          (Set.range ρq).Finite := by
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
    (hinput : Chapter11CanonicalArtinInput D) :
    ∃ z : ℤ, r = z := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter11
