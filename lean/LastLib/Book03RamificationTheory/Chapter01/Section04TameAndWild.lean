import LastLib.Book03RamificationTheory.Chapter01.Section03TheFirstInfinitesimalAction
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section04ImperfectResidueFields

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators LaurentSeries WithZero

/-! ## 1.4. Tame and wild extensions -/

/-- A finite separable field extension profile with explicit residue data. -/
structure Chapter01FiniteSeparableExtensionProfile
    (K E k l : Type*) [Field K] [Field E] [Field k] [Field l]
    [Algebra K E] [Algebra k l] [FiniteDimensional K E]
    [FiniteDimensional k l] where
  field_separable : Algebra.IsSeparable K E
  residue_separable : Algebra.IsSeparable k l
  ramification_index : ℕ

/-- The extension-level tame predicate: the field and residue extensions are
separable, and the ramification index is prime to the residue characteristic
exponent.  In the complete discretely valued setting of the book, no separate
residue-perfection hypothesis is needed. -/
def chapter01TamelyRamifiedExtension
    (K E k l : Type*) [Field K] [Field E] [Field k] [Field l]
    [Algebra K E] [Algebra k l] [FiniteDimensional K E]
    [FiniteDimensional k l] (e : ℕ) : Prop :=
  Algebra.IsSeparable K E ∧
    Algebra.IsSeparable k l ∧ chapter01TameIndex k e

/-- Wild ramification is the complement of the tame condition on finite
separable extensions. -/
def chapter01WildlyRamifiedExtension
    (K E k l : Type*) [Field K] [Field E] [Field k] [Field l]
    [Algebra K E] [Algebra k l] [FiniteDimensional K E]
    [FiniteDimensional k l] (e : ℕ) : Prop :=
  Algebra.IsSeparable K E ∧
    ¬chapter01TamelyRamifiedExtension K E k l e

theorem chapter01_wildly_ramified_iff_not_tame
    {K E k l : Type*} [Field K] [Field E] [Field k] [Field l]
    [Algebra K E] [Algebra k l] [FiniteDimensional K E]
    [FiniteDimensional k l]
    (hfield_separable : Algebra.IsSeparable K E) (e : ℕ) :
    chapter01WildlyRamifiedExtension K E k l e ↔
      ¬chapter01TamelyRamifiedExtension K E k l e := by
  simp [chapter01WildlyRamifiedExtension, hfield_separable]

/-- Unramifiedness includes separability of the residue extension. -/
def chapter01UnramifiedExtensionProfile
    (k l : Type*) [Field k] [Field l] [Algebra k l] (e : ℕ) : Prop :=
  e = 1 ∧ Algebra.IsSeparable k l

@[simp] theorem chapter01_unramified_profile_iff_tame_at_one
    (k l : Type*) [Field k] [Field l] [Algebra k l] :
    chapter01UnramifiedExtensionProfile k l 1 ↔
      chapter01TameExtension k l 1 := by
  simp [chapter01UnramifiedExtensionProfile, chapter01TameExtension,
    chapter01TameIndex]

/-- Under separable residue hypotheses, “wild” is the failure of the tame
prime-to-characteristic condition. -/
theorem chapter01_wild_is_not_tame
    {k l : Type*} [Field k] [Field l] [Algebra k l] (e : ℕ)
    (hsep : Algebra.IsSeparable k l) :
    chapter01WildExtension k l e ↔ ¬chapter01TameIndex k e := by
  simp [chapter01WildExtension, hsep]

/-- The numerical tame criterion is equivalent after replacing `e` by the
cardinality of inertia. -/
theorem chapter01_tame_index_iff_inertia_order_coprime
    {k : Type*} [Ring k] {G : Type*} [Group G] [Finite G]
    (I : Subgroup G) (e : ℕ) (hI : Nat.card I = e) :
    chapter01TameIndex k e ↔
      Nat.Coprime (Nat.card I) (chapter01CharacteristicExponent k) := by
  simp [chapter01TameIndex, hI]

/-- In the source's residue-separable convention, tameness is exactly
prime-to-characteristic inertia. -/
theorem chapter01_tame_iff_inertia_prime_to_characteristic
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    {G : Type*} [Group G] [Finite G]
    (I : Subgroup G) (e : ℕ)
    (hresidue_separable : Algebra.IsSeparable k l)
    (hI : Nat.card I = e) :
    chapter01TameExtension k l e ↔
      Nat.Coprime (Nat.card I) (chapter01CharacteristicExponent k) := by
  simp [chapter01TameExtension, chapter01TameIndex, hresidue_separable, hI]

/-- The positive-characteristic part of non-tameness is divisibility by the
residue characteristic. -/
theorem chapter01_wild_iff_prime_dvd
    (k : Type*) [Field k] (p e : ℕ) [Fact p.Prime] [CharP k p]
    (hchar : chapter01CharacteristicExponent k = p) :
    (¬chapter01TameIndex k e) ↔ p ∣ e := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_wild_iff_prime_dvd
      k p e hchar

/-- With separable residue extension in positive characteristic, wildness is
exactly divisibility of the ramification index by the characteristic. -/
theorem chapter01_wild_extension_iff_prime_dvd
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    (e p : ℕ) [Fact p.Prime] [CharP k p]
    (hchar : chapter01CharacteristicExponent k = p)
    (hresidue_separable : Algebra.IsSeparable k l) :
    chapter01WildExtension k l e ↔ p ∣ e := by
  rw [chapter01_wild_is_not_tame e hresidue_separable]
  exact chapter01_wild_iff_prime_dvd k p e hchar

/-- A finite tame/wild profile records the p-primary positive layer and the
prime-to-`p` tame quotient without identifying either with a conclusion. -/
structure Chapter01TameWildProfile
    (G : Type*) [Group G] [Finite G]
    (I W : Subgroup G) (p e : ℕ) where
  inertia_order : Nat.card I = e
  wild_le_inertia : W ≤ I
  wild_order : chapter01PPrimaryOrder W p
  tame_quotient_order : Nat.Coprime (Nat.card I / Nat.card W) p
  order_factor : Nat.card I = Nat.card W * (Nat.card I / Nat.card W)

/-- In a tame/wild profile, the inertia is prime to `p` exactly when wild
inertia is trivial. -/
theorem chapter01_tame_iff_wild_inertia_trivial
    {G : Type*} [Group G] [Finite G]
    {I W : Subgroup G} {p e : ℕ}
    (D : Chapter01TameWildProfile G I W p e) :
    Nat.Coprime e p ↔ W = ⊥ := by
  sorry

/-- The tame quotient of the inertia stage has the order of the first
infinitesimal quotient. -/
theorem chapter01_tame_quotient_order
    {G : Type*} [Group G] [Finite G]
    {I W : Subgroup G} {p e : ℕ}
    (D : Chapter01TameWildProfile G I W p e) :
    Nat.card I / Nat.card W = e / Nat.card W := by
  rw [D.inertia_order]

/-- A prime-to-`p` totally ramified stage is the numerical tame stage. -/
def chapter01TotallyRamifiedTameStage (degree p : ℕ) : Prop :=
  Nat.Coprime degree p

theorem chapter01_tame_iff_totally_ramified_stage_prime_to_p
    (degree p : ℕ) :
    chapter01TotallyRamifiedTameStage degree p ↔ Nat.Coprime degree p := by
  rfl

/-- Finite residue-field units have no nontrivial `p`-power torsion. -/
theorem chapter01_finite_residue_units_no_p_torsion
    (l : Type*) [Field l] [Finite l] (p : ℕ) [Fact p.Prime] [CharP l p] :
    ∀ u : lˣ, u ^ p = 1 → u = 1 := by
  sorry

/-- The tame character identifies the tame inertia quotient with a subgroup
of residue-field units. -/
theorem chapter01_tame_character_quotient_embeds
    {I : Type*} [Group I] [Finite I]
    {l : Type*} [Field l] [Finite l]
    (θ : I →* lˣ) :
    Nonempty ((I ⧸ MonoidHom.ker θ) ≃* θ.range) := by
  sorry

/-- The character's image is prime to the residue characteristic. -/
theorem chapter01_tame_character_image_prime_to_p
    {I : Type*} [Group I] [Finite I]
    (l : Type*) [Field l] [Finite l]
    (p : ℕ) [Fact p.Prime] [CharP l p]
    (θ : I →* lˣ) :
    Nat.Coprime (Nat.card θ.range) p := by
  sorry

/-- The imperfect-residue warning example is represented with the canonical
Laurent-series tower from Book 2. -/
abbrev chapter01LaurentSeries (k : Type*) [Field k] : Type _ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09LaurentSeries k

abbrev chapter01LaurentSeriesTower
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Type _ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09LaurentSeriesTower k l

/-- Data for `k(a^(1/p))((t))/k((t))` with purely inseparable residue growth,
re-exported from the canonical Book 2 example. -/
abbrev Chapter01PurelyInseparableResidueExample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [Module.Finite k l] :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09ImperfectLaurentSeriesExample
    k l

/-- The example has `e=1`, purely inseparable residue growth, and is not a
separable field extension. -/
theorem chapter01_imperfect_residue_example_is_not_tame
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [Module.Finite k l]
    (E : Chapter01PurelyInseparableResidueExample k l) :
    E.ramification_index = 1 ∧
      IsPurelyInseparable k l ∧
      ¬Algebra.IsSeparable k l ∧
      ¬chapter01TameExtension k l E.ramification_index := by
  sorry

/-- Profile for the later warning that a separable field extension can have
`e=1` and purely inseparable residue growth. -/
structure Chapter01SeparableFierceExtensionProfile
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l] where
  data :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07FiniteLocalExtensionData
      K L k l
  field_separable :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07FiniteExtensionIsSeparable
      K L
  residue_purely_inseparable : IsPurelyInseparable k l
  residue_not_separable :
    ¬LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07ResidueExtensionIsSeparable
      k l
  ramification_index_eq_one : data.ramificationIndex = 1

-- LOCAL_DEPENDENCY_GUESS: the concrete polynomial construction cited in the
-- source's later section should provide a `Nonempty` instance for this
-- profile; the chapter-1 API records the exact obstruction it must satisfy.
def chapter01SeparableFierceExtensionExists
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l] : Prop :=
  Nonempty (Chapter01SeparableFierceExtensionProfile K L k l)

/-- A separable fierce profile is not unramified under the canonical Book 2
predicate. -/
theorem chapter01_separable_fierce_profile_is_not_unramified
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    (E : Chapter01SeparableFierceExtensionProfile K L k l) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07FiercelyRamifiedExtension
        E.data ∧
      ¬LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07UnramifiedExtension
        E.data := by
  refine ⟨⟨E.ramification_index_eq_one, E.residue_purely_inseparable,
    E.residue_not_separable⟩, ?_⟩
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.chapter07_fierce_is_not_unramified
      E.data
      ⟨E.ramification_index_eq_one, E.residue_purely_inseparable,
        E.residue_not_separable⟩

end

end LastLib.Book03RamificationTheory.Chapter01
