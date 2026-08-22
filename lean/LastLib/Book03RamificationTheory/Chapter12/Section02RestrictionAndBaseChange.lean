import LastLib.Book03RamificationTheory.Chapter12.Core
import Mathlib.Data.Real.Basic

namespace LastLib.Book03RamificationTheory.Chapter12

noncomputable section

universe u

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
    simp [P.lower_zero]
  lower_succ_le := by
    intro i x hx
    exact P.lower_succ_le i hx
  lower_eq_bot_of_bound := by
    intro i hi
    simp [P.lower_eq_bot_of_bound i hi]

theorem chapter12_intersected_lower_group_coe
    {G : Type*} [Group G] [Fintype G]
    (P : Chapter12RamificationProfile G) (H : Subgroup G) (i : ℕ) :
    ((P.lower i).comap H.subtype : Set H) =
      ((H ⊓ P.lower i : Subgroup G).comap H.subtype : Set H) := by
  sorry

def chapter12RestrictionConductorSum
    {E G V : Type*} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (P : Chapter12RamificationProfile G) (H : Subgroup G)
    (ρ : Representation E G V) : E :=
  Finset.sum (Finset.range (P.bound + 1)) (fun i =>
      ((Nat.card (H ⊓ P.lower i : Subgroup G) : E) /
        (Nat.card (H ⊓ P.lower 0 : Subgroup G) : E)) *
      (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
        ρ (H ⊓ P.lower i) : E))

theorem chapter12_fixed_space_codimension_intersection_eq_comap
    {E G V : Type*} [Field E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : Subgroup G) (S : Subgroup G) (ρ : Representation E G V) :
    LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ (H ⊓ S) =
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
        (ρ.comp H.subtype) (S.comap H.subtype) := by
  sorry

/- The exact lower-numbering restriction formula from the source.  The finite
range is the API form of the infinite sum because the profile records the
eventual triviality bound. -/
theorem chapter12_lower_subgroup_restriction_formula
    {E G H V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (pG : Chapter12ConductorProfile G) (Hsub : Subgroup G)
    (pH : Chapter12ConductorProfile Hsub)
    (hprofile : pH.ramification =
      chapter12IntersectRamificationProfile pG.ramification Hsub)
    (ρ : Representation E G V) :
    (pH.artinConductor _ (ρ.comp Hsub.subtype) : E) =
      chapter12RestrictionConductorSum pG.ramification Hsub ρ := by
  sorry

/- The source warning that restriction is not determined by `e` and the
upstairs conductor is represented by the explicit intersection/fixed-space
ledger on the right-hand side. -/
theorem chapter12_restriction_uses_intersection_fixed_spaces
    {E G V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (pG : Chapter12ConductorProfile G) (Hsub : Subgroup G)
    (ρ : Representation E G V) :
    chapter12RestrictionConductorSum pG.ramification Hsub ρ =
      Finset.sum (Finset.range (pG.ramification.bound + 1)) (fun i =>
        ((Nat.card (Hsub ⊓ pG.ramification.lower i : Subgroup G) : E) /
            (Nat.card (Hsub ⊓ pG.ramification.lower 0 : Subgroup G) : E)) *
          (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
            ρ (Hsub ⊓ pG.ramification.lower i) : E)) := by
  rfl

/- Upper-numbering comparison data isolates the exact transition statements
used for unramified and tamely ramified base change. -/
structure Chapter12UnramifiedUpperComparison
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) where
  baseInertia : Subgroup G
  extensionInertia : Subgroup H
  baseUpper : ℝ → Subgroup G
  extensionUpper : ℝ → Subgroup H
  inertia_eq : extensionInertia = baseInertia.comap H.subtype
  upper_eq : ∀ u, (-1 : ℝ) ≤ u →
    extensionUpper u = (baseUpper u).comap H.subtype

structure Chapter12TameUpperComparison
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) where
  ramificationIndex : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  baseInertia : Subgroup G
  extensionInertia : Subgroup H
  baseUpper : ℝ → Subgroup G
  extensionUpper : ℝ → Subgroup H
  extensionInertia_eq : extensionInertia = baseInertia.comap H.subtype
  upper_eq : ∀ u, 0 < u →
    extensionUpper ((ramificationIndex : ℝ) * u) =
      (baseUpper u).comap H.subtype

/- A wild transition is deliberately recorded as a full Herbrand map instead
of a degree-only scalar. -/
structure Chapter12WildUpperComparison
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) where
  herbrandTransition : ℝ → ℝ
  baseUpper : ℝ → Subgroup G
  extensionUpper : ℝ → Subgroup H
  upper_eq : ∀ u, 0 < u →
    extensionUpper (herbrandTransition u) = (baseUpper u).comap H.subtype

/- LOCAL_DEPENDENCY_GUESS: this is the reusable upper-depth integral bridge
which the preceding Herbrand API should eventually provide.  The change of
variables is expressed for an abstract area, while the conductor values are
connected to that area by the two displayed fields. -/
structure Chapter12TameSwanAreaCompatibility
    {G : Type u} [Group G] [Fintype G] {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H) where
  baseArea :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Representation E G V → ℝ
  extensionArea :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Representation E H V → ℝ
  baseArea_eq_swan :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E G V),
      baseArea (E := E) V ρ = (pK.swanConductor (E := E) V ρ : ℝ)
  extensionArea_eq_swan :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E H V),
      extensionArea (E := E) V ρ = (pM.swanConductor (E := E) V ρ : ℝ)
  change_of_variables :
    ∀ {E : Type u} [Field E] [CharZero E]
      (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (ρ : Representation E G V),
      extensionArea (E := E) V (ρ.comp H.subtype) =
        (T.ramificationIndex : ℝ) * baseArea (E := E) V ρ

theorem chapter12_unramified_upper_groups_agree
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (U : Chapter12UnramifiedUpperComparison G H) (u : ℝ) (hu : (-1 : ℝ) ≤ u) :
    U.extensionUpper u = (U.baseUpper u).comap H.subtype :=
  U.upper_eq u hu

theorem chapter12_unramified_inertia_groups_agree
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (U : Chapter12UnramifiedUpperComparison G H) :
    U.extensionInertia = U.baseInertia.comap H.subtype :=
  U.inertia_eq

theorem chapter12_tame_herbrand_scaling
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (T : Chapter12TameUpperComparison G H) (u : ℝ) (hu : 0 < u) :
    T.extensionUpper ((T.ramificationIndex : ℝ) * u) =
      (T.baseUpper u).comap H.subtype :=
  T.upper_eq u hu

theorem chapter12_tame_inertia_groups_agree
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (T : Chapter12TameUpperComparison G H) :
    T.extensionInertia = T.baseInertia.comap H.subtype :=
  T.extensionInertia_eq

theorem chapter12_wild_base_change_requires_herbrand_transition
    {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    (W : Chapter12WildUpperComparison G H) (u : ℝ) (hu : 0 < u) :
    W.extensionUpper (W.herbrandTransition u) =
      (W.baseUpper u).comap H.subtype :=
  W.upper_eq u hu

/- Unramified base change leaves both conductor parts unchanged. -/
theorem chapter12_unramified_base_change_conductors
    {E G V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (U : Chapter12UnramifiedUpperComparison G H)
    (hbase_inertia : pK.ramification.inertia = U.baseInertia)
    (hextension_inertia : pM.ramification.inertia = U.extensionInertia)
    (hprofile : pM.ramification =
      chapter12IntersectRamificationProfile pK.ramification H)
    (hgroup : ∀ i, H ⊓ pK.ramification.lower i = pK.ramification.lower i)
    (ρ : Representation E G V) :
    pM.artinConductor _ (ρ.comp H.subtype) =
        pK.artinConductor _ ρ ∧
    pM.swanConductor _ (ρ.comp H.subtype) =
        pK.swanConductor _ ρ := by
  sorry

/- In the tame case positive upper depth is rescaled by `e`, so Swan scales by
`e`; the tame term is separately recomputed from the new inertia subgroup. -/
theorem chapter12_tame_base_change_swan
    {E G V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H)
    (C : Chapter12TameSwanAreaCompatibility pK pM T)
    (ρ : Representation E G V) :
    pM.swanConductor _ (ρ.comp H.subtype) =
      T.ramificationIndex * pK.swanConductor _ ρ := by
  sorry

theorem chapter12_tame_base_change_tame_term
    {E G V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {H : Subgroup G}
    (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H)
    (hinertia : pM.ramification.inertia = T.extensionInertia)
    (ρ : Representation E G V) :
    pM.artinConductor _ (ρ.comp H.subtype) =
      LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim
          (ρ.comp H.subtype) T.extensionInertia +
        pM.swanConductor _ (ρ.comp H.subtype) := by
  simpa [hinertia] using
    pM.artin_eq_tame_add_swan _
      (ρ.comp H.subtype)

/- The tame change-of-variables statement in the source, displayed at the
conductor level so it can be consumed without choosing an integration API. -/
theorem chapter12_tame_change_of_variables_for_swan
    {E G V : Type u} [Field E] [CharZero E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {H : Subgroup G}
    (pK : Chapter12ConductorProfile G) (pM : Chapter12ConductorProfile H)
    (T : Chapter12TameUpperComparison G H)
    (C : Chapter12TameSwanAreaCompatibility pK pM T)
    (ρ : Representation E G V) :
    (pM.swanConductor _ (ρ.comp H.subtype) : ℝ) =
      (T.ramificationIndex : ℝ) * (pK.swanConductor _ ρ : ℝ) := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter12
