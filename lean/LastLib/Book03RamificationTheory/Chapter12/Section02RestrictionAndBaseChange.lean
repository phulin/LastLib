import LastLib.Book03RamificationTheory.Chapter12.Core

namespace LastLib.Book03RamificationTheory.Chapter12

noncomputable section

universe uV

open scoped BigOperators

/-!
## 12.3. Restriction and base change
-/

/- Intersecting a lower filtration with a subgroup is the lower-subgroup
theorem in the form needed for restriction. -/
def chapter12IntersectRamificationProfile
    {G : Type*} [Group G] [Fintype G]
    (P : Chapter12RamificationProfile G) (H : Subgroup G) :
    Chapter12RamificationProfile H where
  inertia := P.inertia.comap H.subtype
  lower := fun i => (P.lower i).comap H.subtype
  bound := P.bound
  lower_zero := by
    simpa [P.lower_zero]
  lower_succ_le := by
    intro i x hx
    exact P.lower_succ_le i hx
  lower_eq_bot_of_bound := by
    intro i hi
    simpa [P.lower_eq_bot_of_bound i hi]

theorem chapter12_intersected_lower_group_coe
    {G : Type*} [Group G] [Fintype G]
    (P : Chapter12RamificationProfile G) (H : Subgroup G) (i : ℕ) :
    ((P.lower i).comap H.subtype : Set H) =
      ((H ⊓ P.lower i : Subgroup G).comap H.subtype : Set H) := by
  sorry

def chapter12RestrictionConductorSum
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : Chapter12RamificationProfile G) (H : Subgroup G)
    (ρ : Representation ℚ G V) : ℚ :=
  ∑ i in Finset.range (P.bound + 1),
    ((Nat.card (H ⊓ P.lower i) : ℚ) /
        (Nat.card (H ⊓ P.lower 0) : ℚ)) *
      (chapter12FixedSpaceCodimension (H ⊓ P.lower i) ρ : ℚ)

theorem chapter12_fixed_space_codimension_intersection_eq_comap
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (H : Subgroup G) (S : Subgroup G) (ρ : Representation ℚ G V) :
    chapter12FixedSpaceCodimension (H ⊓ S) ρ =
      chapter12FixedSpaceCodimension (S.comap H.subtype) (ρ.comp H.subtype) := by
  sorry

/- The exact lower-numbering restriction formula from the source.  The finite
range is the API form of the infinite sum because the profile records the
eventual triviality bound. -/
theorem chapter12_lower_subgroup_restriction_formula
    {G H V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V]
    (pG : Chapter12ConductorProfile G) (Hsub : Subgroup G)
    (pH : Chapter12ConductorProfile Hsub)
    (hprofile : pH.ramification =
      chapter12IntersectRamificationProfile pG.ramification Hsub)
    (ρ : Representation ℚ G V) :
    (pH.artinConductor _ (chapter12RestrictedRepresentation Hsub.subtype ρ) : ℚ) =
      chapter12RestrictionConductorSum pG.ramification Hsub ρ := by
  sorry

/- The source warning that restriction is not determined by `e` and the
upstairs conductor is represented by the explicit intersection/fixed-space
ledger on the right-hand side. -/
theorem chapter12_restriction_uses_intersection_fixed_spaces
    {G H V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V]
    (pG : Chapter12ConductorProfile G) (Hsub : Subgroup G)
    (ρ : Representation ℚ G V) :
    chapter12RestrictionConductorSum pG.ramification Hsub ρ =
      ∑ i in Finset.range (pG.ramification.bound + 1),
        ((Nat.card (Hsub ⊓ pG.ramification.lower i) : ℚ) /
            (Nat.card (Hsub ⊓ pG.ramification.lower 0) : ℚ)) *
          (chapter12FixedSpaceCodimension
            (Hsub ⊓ pG.ramification.lower i) ρ : ℚ) := by
  rfl

/- Upper-numbering comparison data isolates the exact transition statements
used for unramified and tamely ramified base change. -/
structure Chapter12UnramifiedUpperComparison
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) where
  baseInertia : Subgroup G
  extensionInertia : Subgroup H
  baseUpper : ℚ → Subgroup G
  extensionUpper : ℚ → Subgroup H
  inertia_eq : extensionInertia = baseInertia.comap H.subtype
  upper_eq : ∀ u, extensionUpper u = (baseUpper u).comap H.subtype

structure Chapter12TameUpperComparison
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) where
  ramificationIndex : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  baseInertia : Subgroup G
  extensionInertia : Subgroup H
  baseUpper : ℚ → Subgroup G
  extensionUpper : ℚ → Subgroup H
  extensionInertia_le : extensionInertia ≤ baseInertia.comap H.subtype
  upper_eq : ∀ u, 0 < u →
    extensionUpper ((ramificationIndex : ℚ) * u) =
      (baseUpper u).comap H.subtype

/- A wild transition is deliberately recorded as a full Herbrand map instead
of a degree-only scalar. -/
structure Chapter12WildUpperComparison
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) where
  herbrandTransition : ℚ → ℚ
  baseUpper : ℚ → Subgroup G
  extensionUpper : ℚ → Subgroup H
  upper_eq : ∀ u, 0 < u →
    extensionUpper (herbrandTransition u) = (baseUpper u).comap H.subtype

/- LOCAL_DEPENDENCY_GUESS: this is the reusable upper-depth integral bridge
which the preceding Herbrand API should eventually provide.  The change of
variables is expressed for an abstract area, while the conductor values are
connected to that area by the two displayed fields. -/
structure Chapter12TameSwanAreaCompatibility
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H) where
  baseArea :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V],
      Representation ℚ G V → ℚ
  extensionArea :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V],
      Representation ℚ H V → ℚ
  baseArea_eq_swan :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ G V),
      baseArea V ρ = (pK.swanConductor V ρ : ℚ)
  extensionArea_eq_swan :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ H V),
      extensionArea V ρ = (pM.swanConductor V ρ : ℚ)
  change_of_variables :
    ∀ (V : Type uV) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (ρ : Representation ℚ G V),
      extensionArea V (ρ.comp H.subtype) =
        (T.ramificationIndex : ℚ) * baseArea V ρ

theorem chapter12_unramified_upper_groups_agree
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (U : Chapter12UnramifiedUpperComparison G H) (u : ℚ) :
    U.extensionUpper u = (U.baseUpper u).comap H.subtype :=
  U.upper_eq u

theorem chapter12_unramified_inertia_groups_agree
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (U : Chapter12UnramifiedUpperComparison G H) :
    U.extensionInertia = U.baseInertia.comap H.subtype :=
  U.inertia_eq

theorem chapter12_tame_herbrand_scaling
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (T : Chapter12TameUpperComparison G H) (u : ℚ) (hu : 0 < u) :
    T.extensionUpper ((T.ramificationIndex : ℚ) * u) =
      (T.baseUpper u).comap H.subtype :=
  T.upper_eq u hu

theorem chapter12_wild_base_change_requires_herbrand_transition
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (W : Chapter12WildUpperComparison G H) (u : ℚ) (hu : 0 < u) :
    W.extensionUpper (W.herbrandTransition u) =
      (W.baseUpper u).comap H.subtype :=
  W.upper_eq u hu

/- Unramified base change leaves both conductor parts unchanged. -/
theorem chapter12_unramified_base_change_conductors
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (U : Chapter12UnramifiedUpperComparison G H)
    (hbase_inertia : pK.ramification.inertia = U.baseInertia)
    (hextension_inertia : pM.ramification.inertia = U.extensionInertia)
    (hprofile : pM.ramification =
      chapter12IntersectRamificationProfile pK.ramification H)
    (hgroup : ∀ i, H ⊓ pK.ramification.lower i = pK.ramification.lower i)
    (ρ : Representation ℚ G V) :
    pM.artinConductor _ (chapter12RestrictedRepresentation H.subtype ρ) =
        pK.artinConductor _ ρ ∧
    pM.swanConductor _ (chapter12RestrictedRepresentation H.subtype ρ) =
        pK.swanConductor _ ρ := by
  sorry

/- In the tame case positive upper depth is rescaled by `e`, so Swan scales by
`e`; the tame term is separately recomputed from the new inertia subgroup. -/
theorem chapter12_tame_base_change_swan
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H)
    (C : Chapter12TameSwanAreaCompatibility pK pM T)
    (ρ : Representation ℚ G V) :
    pM.swanConductor _ (chapter12RestrictedRepresentation H.subtype ρ) =
      T.ramificationIndex * pK.swanConductor _ ρ := by
  sorry

theorem chapter12_tame_base_change_tame_term
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {H : Subgroup G}
    (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H)
    (hinertia : pM.ramification.inertia = T.extensionInertia)
    (ρ : Representation ℚ G V) :
    pM.artinConductor _ (chapter12RestrictedRepresentation H.subtype ρ) =
      chapter12FixedSpaceCodimension T.extensionInertia
          (chapter12RestrictedRepresentation H.subtype ρ) +
        pM.swanConductor _ (chapter12RestrictedRepresentation H.subtype ρ) := by
  simpa [hinertia] using
    pM.artin_eq_tame_add_swan _
      (chapter12RestrictedRepresentation H.subtype ρ)

/- The tame change-of-variables statement in the source, displayed at the
conductor level so it can be consumed without choosing an integration API. -/
theorem chapter12_tame_change_of_variables_for_swan
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H)
    (C : Chapter12TameSwanAreaCompatibility pK pM T)
    (ρ : Representation ℚ G V) :
    (pM.swanConductor _ (chapter12RestrictedRepresentation H.subtype ρ) : ℚ) =
      (T.ramificationIndex : ℚ) * (pK.swanConductor _ ρ : ℚ) := by
  exact_mod_cast chapter12_tame_base_change_swan pK pM T C ρ

end
end LastLib.Book03RamificationTheory.Chapter12
