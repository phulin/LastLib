import LastLib.Book03RamificationTheory.Chapter13.Section02TheRegularRepresentation

namespace LastLib.Book03RamificationTheory.Chapter13

noncomputable section

open LastLib.Book03RamificationTheory.Chapter11
open LastLib.Book03RamificationTheory.Chapter12
open scoped BigOperators

/-! ## 13.5. Discriminants of fields cut out by representations -/

/-- The finite-image condition for an absolute or profinite representation. -/
def chapter13FiniteImageRepresentation
    {E Γ V : Type*} [Semiring E] [Group Γ]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E Γ V) : Prop :=
  (Set.range ρ).Finite

def chapter13RepresentationFaithful
    {E G V : Type*} [Semiring E] [Group G]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) : Prop :=
  MonoidHom.ker ρ = ⊥

/-- The fixed field cut out by the kernel of a representation of a finite
Galois group. -/
def chapter13RepresentationFixedField
    {E K L V : Type*} [Semiring E] [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E (Gal(L / K)) V) : IntermediateField K L :=
  IntermediateField.fixedField (MonoidHom.ker ρ)

theorem chapter13_representation_fixed_field_eq_top_iff_faithful
    {E K L V : Type*} [Semiring E] [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup V] [Module E V]
    (ρ : Representation E (Gal(L / K)) V) :
    chapter13RepresentationFixedField ρ = ⊤ ↔
      chapter13RepresentationFaithful ρ := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: replace this wrapper by the canonical finite-image
quotient/fixed-field realization from Chapter 12 once the absolute Galois
interfaces are reconciled.  The representation and ramification profile are
kept on the finite Galois group so the regular-conductor identity is usable. -/
structure Chapter13FiniteImageRepresentationContext
    (K L E V : Type*)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Fintype (Gal(L / K))]
    (D : Chapter11RamificationData (Gal(L / K))) where
  representation : Representation E (Gal(L / K)) V
  finite_image : chapter13FiniteImageRepresentation representation
  residue_extension_separable : D.residue_separable

theorem chapter13_finite_image_context_fixed_field
    {K L E V : Type*}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Fintype (Gal(L / K))]
    {D : Chapter11RamificationData (Gal(L / K))}
    (R : Chapter13FiniteImageRepresentationContext K L E V D)
    (hfaithful : chapter13RepresentationFaithful R.representation) :
    chapter13RepresentationFixedField R.representation = ⊤ := by
  exact (chapter13_representation_fixed_field_eq_top_iff_faithful
    R.representation).2 hfaithful

/- The discriminant of the cut-out field is computed by the regular module,
not by an arbitrary representation carried by the same quotient. -/
theorem chapter13_finite_image_cutout_discriminant_eq_regular_conductor
    {K L E V : Type*}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Fintype (Gal(L / K))]
    {D : Chapter11RamificationData (Gal(L / K))}
    (R : Chapter13FiniteImageRepresentationContext K L E V D)
    (Δ : Chapter13LocalDiscriminantData D)
    (hcutout : chapter13RepresentationFixedField R.representation = ⊤) :
    (Δ.discriminantExponent : ℚ) =
      chapter11ArtinConductor D
        (chapter13RegularRepresentation ℚ (Gal(L / K))) := by
  sorry

/- The source warns that an arbitrary representation conductor need not be
the cut-out discriminant.  This comparison predicate records the only
equality that can be asserted for a particular representation without adding
extra hypotheses. -/
def chapter13RepresentationConductorMatchesRegular
    {E G V : Type*} [Field E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (D : Chapter11RamificationData G) (ρ : Representation E G V) : Prop :=
  chapter13ArtinConductor D (chapter13RegularRepresentation ℚ G) =
    chapter13ArtinConductor D ρ

/-- The upper ramification level is nontrivial exactly when it contains a
nonidentity element. -/
def chapter13UpperLevelNontrivial
    {G : Type*} [Group G]
    (upper : ℚ → Subgroup G) (u : ℚ) : Prop :=
  upper u ≠ ⊥

def chapter13RepresentationSeesUpperLevel
    {E G V : Type*} [Field E] [Group G]
    [AddCommGroup V] [Module E V]
    (upper : ℚ → Subgroup G) (ρ : Representation E G V) (u : ℚ) : Prop :=
  ∃ g : G, g ∈ upper u ∧ ρ g ≠ LinearMap.id

theorem chapter13_faithful_representation_detects_upper_levels
    {E G V : Type*} [Field E] [Group G]
    [AddCommGroup V] [Module E V]
    (upper : ℚ → Subgroup G) (ρ : Representation E G V)
    (hfaithful : chapter13RepresentationFaithful ρ) (u : ℚ) :
    chapter13UpperLevelNontrivial upper u ↔
      chapter13RepresentationSeesUpperLevel upper ρ u := by
  sorry

def chapter13HasLastLowerBreakAt
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) (B : ℕ) : Prop :=
  ∀ i : ℕ, B < i → D.lower i = ⊥

/- The lower-numbered formula turns a last-break bound into the coarse
discriminant estimate used for finite-image fields. -/
theorem chapter13_discriminant_exponent_le_of_last_lower_break
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable)
    (B : ℕ)
    (hB : chapter13HasLastLowerBreakAt D B) :
    (Δ.discriminantExponent : ℚ) ≤
      (D.f : ℚ) * ((B + 1 : ℕ) : ℚ) *
        ((Fintype.card D.inertia - 1 : ℕ) : ℚ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter13
