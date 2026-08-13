import LastLib.Book06GlobalClassFieldTheory.Chapter06.Dependencies

/- The local dual subgroup and pointwise Kummer support keep the restricted
   product pairing finite without collapsing unramified valuation classes. -/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter06

open scoped BigOperators

noncomputable section

/-! # 6.2. The finite local--global character sequence

The pinned library supplies the standard Kummer and cohomological building
blocks, but not the number-field local invariant sequence.  The interfaces
below keep the local fields, their unramified subgroups, and the finite
arithmetic-duality input explicit.
-/

/- The degree-one Kummer group for the Cartier dual coefficient. -/
abbrev Chapter06H1Mu (F : Type*) [Field F] (n : ℕ) :=
  Chapter06KummerClassGroup F n

/- Continuous degree-one classes for the trivial finite coefficient module. -/
abbrev Chapter06H1A
    (G : Type*) (n : ℕ) [Group G] [TopologicalSpace G]
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)] :=
  Chapter06ContinuousACharacter G (Chapter06A n)

theorem chapter06_H1_mu_is_kummer
    {F : Type*} [Field F] (n : ℕ) :
    Chapter06H1Mu F n = Additive (Fˣ ⧸ Chapter06NthPowerSubgroup F n) :=
  rfl

/- The local data package for the invariant pairing.  The field
   localCupProduct records the cup product before applying the local Brauer
   invariant, while pairing is its invariant-valued composite. -/
structure Chapter06LocalCupPairingData
    (ι : Type*) (n : ℕ)
    (HLocal HMu HBr HTate : ι → Type*)
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] where
  positive : 0 < n
  kind : ι → Chapter06PlaceKind
  unramified : ∀ v, AddSubgroup (HLocal v)
  /- At an unramified finite place, the local pairing vanishes when both
     entries are unramified.  It does not vanish for an arbitrary Kummer
     class: an unramified character can pair nontrivially with a valuation
     class. -/
  unramifiedDual : ∀ v, AddSubgroup (HMu v)
  localCupProduct : ∀ v, HLocal v →+ HMu v →+ HBr v
  localInvariant : ∀ v, HBr v →+ Chapter06OneOverNModOne n
  pairing : ∀ v, HLocal v →+ HMu v →+ Chapter06OneOverNModOne n
  pairing_eq_invariant :
    ∀ v c a, pairing v c a = localInvariant v (localCupProduct v c a)
  perfect : ∀ v, Function.Bijective (pairing v)
  unramified_pairing_zero :
    ∀ v c, c ∈ unramified v → ∀ a, a ∈ unramifiedDual v → pairing v c a = 0
  real_place_uses_tate :
    ∀ v, kind v = Chapter06PlaceKind.real →
      Nonempty (HLocal v ≃+ HTate v)
  tatePairing : ∀ v, HTate v →+ HMu v →+ Chapter06OneOverNModOne n
  tate_pairing_agrees :
    ∀ v (_hv : kind v = Chapter06PlaceKind.real) c a,
      ∃ e : HLocal v ≃+ HTate v,
        tatePairing v (e c) a = pairing v c a
  complex_place_groups_vanishes :
    ∀ v, kind v = Chapter06PlaceKind.complex →
      Subsingleton (HLocal v) ∧ Subsingleton (HMu v)

theorem chapter06_real_place_tate_identification
    {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    (D : Chapter06LocalCupPairingData ι n HLocal HMu HBr HTate)
    {v : ι} (hv : D.kind v = Chapter06PlaceKind.real) :
    Nonempty (HLocal v ≃+ HTate v) :=
  D.real_place_uses_tate v hv

theorem chapter06_complex_place_groups_vanish
    {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    (D : Chapter06LocalCupPairingData ι n HLocal HMu HBr HTate)
    {v : ι} (hv : D.kind v = Chapter06PlaceKind.complex) :
    Subsingleton (HLocal v) ∧ Subsingleton (HMu v) :=
  D.complex_place_groups_vanishes v hv

/- The finite-place support condition used when a restricted product element
   is cut down to a finite set S. -/
def chapter06AdmissibleFinitePlaceSet
    {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    (D : Chapter06LocalCupPairingData ι n HLocal HMu HBr HTate)
    (c : Chapter06RestrictedProduct ι HLocal D.unramified)
    (placesAboveN : ι → Prop) (S : Finset ι) : Prop :=
  (∀ v, D.kind v ≠ Chapter06PlaceKind.finite → v ∈ S) ∧
    (∀ v, placesAboveN v → v ∈ S) ∧
    (∀ v, c v ∉ D.unramified v → v ∈ S)

/- Finite S-duality, the finite-level calculation used before passing to the
   restricted product. -/
structure Chapter06FiniteSArithmeticDuality
    (G A : Type*) (ι : Type*) (HLocal : ι → Type*) (HMuGlobal : Type*)
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)] [AddCommGroup HMuGlobal]
    (S : Finset ι) where
  localization : Chapter06ContinuousACharacter G A →+ (∀ v : S, HLocal v)
  lambda : (∀ v : S, HLocal v) →+ (HMuGlobal →+ Chapter06QModZ)
  exact_at_middle :
    Chapter06ExactAtMiddle localization lambda

/- LOCAL_DEPENDENCY_GUESS: The finite-S object above is the degree-one
   compact-support arithmetic-duality calculation from Chapter 4, Section
   4.1.  No earlier LastLib file in this worktree exposes that calculation,
   so this is an explicit replacement interface rather than a restatement of
   Theorem 6.1.  Its global term is now the chapter's actual continuous
   character group.  The comparison fields in the calculation record the
   identification of its finite-S maps with the restricted-product maps. -/

/- The local finite calculation includes all archimedean places, all places
   above n, and all exceptional places of the chosen local family. -/
structure Chapter06FiniteSLocalCalculation
    (G A : Type*) (ι : Type*) (n : ℕ)
    (HLocal HMu HBr HTate : ι → Type*) (HMuGlobal : Type*)
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06LocalCupPairingData ι n HLocal HMu HBr HTate)
    (placesAboveN : ι → Prop)
    (kummerRestriction : ∀ v, HMuGlobal →+ HMu v)
    (localization :
      Chapter06ContinuousACharacter G A →+
        Chapter06RestrictedProduct ι HLocal D.unramified)
    (c : Chapter06RestrictedProduct ι HLocal D.unramified)
    (S : Finset ι) where
  admissible : chapter06AdmissibleFinitePlaceSet D c placesAboveN S
  duality : Chapter06FiniteSArithmeticDuality G A ι HLocal HMuGlobal S
  /- The finite calculation is a model of the actual localization and
     pairing, not an unrelated exact sequence with the same source types. -/
  localization_agrees :
    ∀ x v, duality.localization x v = localization x v
  lambda_agrees :
    ∀ z a, (∀ v, kummerRestriction v a ∉ D.unramifiedDual v → v ∈ S) →
      duality.lambda z a =
      ∑ v : S, chapter06InvariantTargetInclusion n
        (D.pairing v (z v) (kummerRestriction v a))

/- Restriction of a restricted-product family to a finite set S.  These maps
   are the transition maps used when the finite calculation is enlarged. -/
def chapter06FiniteSRestriction
    {ι : Type*} {HLocal : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    {U : ∀ v, AddSubgroup (HLocal v)}
    (c : Chapter06RestrictedProduct ι HLocal U) (S : Finset ι) :
    ∀ v : S, HLocal v :=
  fun v => c v

def chapter06RestrictFiniteLocalFamily
    {ι : Type*} {HLocal : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    {S T : Finset ι} (hST : S ⊆ T) :
    (∀ v : T, HLocal v) →+ (∀ v : S, HLocal v) where
  toFun := fun c v => c ⟨v, hST v.property⟩
  map_zero' := by
    funext v
    simp
  map_add' := by
    intro c₁ c₂
    funext v
    simp

theorem chapter06_finiteS_restriction_compatibility
    {ι : Type*} {HLocal : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    {U : ∀ v, AddSubgroup (HLocal v)}
    {S T : Finset ι} (hST : S ⊆ T)
    (c : Chapter06RestrictedProduct ι HLocal U) :
    chapter06RestrictFiniteLocalFamily hST
        (chapter06FiniteSRestriction c T) =
      chapter06FiniteSRestriction c S := by
  ext v
  rfl

/- The split-everywhere separation input used for injectivity of
   localization. -/
def Chapter06ComponentSeparation
    (G A : Type*) (ι : Type*) (HLocal : ι → Type*)
    [Group G] [AddCommGroup A] [∀ v, AddCommGroup (HLocal v)]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    (localizationAt : ∀ v, Chapter06ContinuousACharacter G A →+ HLocal v) : Prop :=
  ∀ c : Chapter06ContinuousACharacter G A,
    (∀ v, localizationAt v c = 0) → c = 0

/- LOCAL_DEPENDENCY_GUESS: component_separation is the split-everywhere
   separation result referred to from Chapter 4, Section 4.2.  It is kept as
   a separate input so the injectivity proof cannot silently identify a
   global character with zero. -/

/- All local and finite-level data needed to state the global exact
   sequence. -/
structure Chapter06FiniteLocalGlobalCharacterData
    (G A : Type*) (ι : Type*) (n : ℕ)
    (HLocal HMu HBr HTate : ι → Type*) (HMuGlobal : Type*)
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal] where
  localData : Chapter06LocalCupPairingData ι n HLocal HMu HBr HTate
  placesAboveN : ι → Prop
  archimedean_finite : Set.Finite {v | localData.kind v ≠ Chapter06PlaceKind.finite}
  placesAboveN_finite : Set.Finite {v | placesAboveN v}
  kummerRestriction : ∀ v, HMuGlobal →+ HMu v
  kummer_support_finite :
    ∀ a, Set.Finite {v | kummerRestriction v a ∉ localData.unramifiedDual v}
  localizationAt : ∀ v, Chapter06ContinuousACharacter G A →+ HLocal v
  localization :
    Chapter06ContinuousACharacter G A →+
      Chapter06RestrictedProduct ι HLocal localData.unramified
  localization_formula :
    ∀ c v, localization c v = localizationAt v c
  component_separation :
    Chapter06ComponentSeparation G A ι HLocal localizationAt
  finite_level_duality :
    ∀ c S, chapter06AdmissibleFinitePlaceSet localData c placesAboveN S →
      Nonempty (Chapter06FiniteSLocalCalculation G A ι n HLocal HMu HBr HTate
        HMuGlobal localData placesAboveN kummerRestriction localization c S)

theorem chapter06_admissible_finite_place_set_exists
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal) (c : Chapter06RestrictedProduct
      ι HLocal D.localData.unramified) :
    ∃ S : Finset ι,
      chapter06AdmissibleFinitePlaceSet D.localData c D.placesAboveN S := by
  sorry

/- The finite sum appearing in the global localization functional. -/
def chapter06LocalGlobalLambdaValue
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal)
    (c : Chapter06RestrictedProduct ι HLocal D.localData.unramified)
    (a : HMuGlobal) : Chapter06QModZ :=
  let s : Set ι := {v |
    c v ∉ D.localData.unramified v ∨
      D.kummerRestriction v a ∉ D.localData.unramifiedDual v}
  let hs : s.Finite := by
    have hu :
        ({v | c v ∉ D.localData.unramified v} ∪
          {v | D.kummerRestriction v a ∉ D.localData.unramifiedDual v}).Finite :=
      Set.Finite.union c.property (D.kummer_support_finite a)
    apply Set.Finite.subset hu
    intro v hv
    simpa only [s, Set.mem_union, Set.mem_ofPred_eq] using hv
  hs.toFinset.sum (fun v =>
    chapter06InvariantTargetInclusion n
      (D.localData.pairing v (c v) (D.kummerRestriction v a)))

/- The global dual localization functional. -/
noncomputable def chapter06LocalGlobalLambda
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal) :
    Chapter06RestrictedProduct ι HLocal D.localData.unramified →+
      (HMuGlobal →+ Chapter06QModZ) where
  toFun := fun c =>
    { toFun := chapter06LocalGlobalLambdaValue D c
      map_zero' := by sorry
      map_add' := by sorry }
  map_zero' := by
    ext a
    sorry
  map_add' := by
    intro c₁ c₂
    ext a
    sorry

@[simp]
theorem chapter06LocalGlobalLambda_apply
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal)
    (c : Chapter06RestrictedProduct ι HLocal D.localData.unramified)
    (a : HMuGlobal) :
    chapter06LocalGlobalLambda D c a = chapter06LocalGlobalLambdaValue D c a :=
  rfl

/- The remaining finite-level arithmetic-duality calculation is supplied as
   data in `D.finite_level_duality`; its comparison with the global maps is
   recorded by `Chapter06FiniteSLocalCalculation`. -/
/- Exactness at the middle and injectivity of localization. -/
theorem chapter06_finite_local_global_duality
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal) :
    Chapter06ExactAtMiddle D.localization (chapter06LocalGlobalLambda D) ∧
      Function.Injective D.localization := by
  sorry

theorem chapter06_globalization_iff_orthogonal
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal)
    (c : Chapter06RestrictedProduct ι HLocal D.localData.unramified) :
    (∃ x, D.localization x = c) ↔ chapter06LocalGlobalLambda D c = 0 := by
  sorry

/- The theorem's finite-set calculation is the safe replacement for an
   unrestricted Grunwald prescription. -/
theorem chapter06_theorem_6_1
    {G A : Type*} {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*} {HMuGlobal : Type*}
    [Group G] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)] [AddCommGroup HMuGlobal]
    (D : Chapter06FiniteLocalGlobalCharacterData
      G A ι n HLocal HMu HBr HTate HMuGlobal) :
    Chapter06ExactAtMiddle D.localization (chapter06LocalGlobalLambda D) ∧
      Function.Injective D.localization :=
  chapter06_finite_local_global_duality D

/- SOURCE_ISSUE: Section 6.2 says that the special 2-primary obstruction
   discovered by Wang contains an extra nonzero global class, but it does not
   specify the number field, the local conditions, or the exact class.  The
   API therefore records the unconditional orthogonality theorem only for
   idele-class characters; an explicit Wang obstruction should be added when
   those missing hypotheses are supplied. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
