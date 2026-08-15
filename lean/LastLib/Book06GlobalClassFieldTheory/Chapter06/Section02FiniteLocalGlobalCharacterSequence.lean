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
    ∀ v (_hv : kind v = Chapter06PlaceKind.real),
      ∃ e : HLocal v ≃+ HTate v, ∀ c a,
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
  /- The finite-S calculation is supplied by the arithmetic input below; it
     must not be replaced by global finiteness of H¹, which is generally
     false when ramification is allowed at arbitrary places. -/
  component_separation :
    Chapter06ComponentSeparation G A ι HLocal localizationAt
  finite_level_duality :
    ∀ c S, chapter06AdmissibleFinitePlaceSet localData c placesAboveN S →
      Nonempty (Chapter06FiniteSLocalCalculation G A ι n HLocal HMu HBr HTate
        HMuGlobal localData placesAboveN kummerRestriction localization c S)

/- The finite-support Kummer subgroup occurring in the Grunwald--Wang
   calculation.  This uses the zero local class, rather than the larger
   unramified subgroup used for the restricted-product support. -/
def chapter06KummerClassesTrivialOutside
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
    (S : Finset ι) : AddSubgroup HMuGlobal where
  carrier := {a | ∀ v, v ∉ S → D.kummerRestriction v a = 0}
  zero_mem' := by
    intro v hv
    simp
  add_mem' := by
    intro a b ha hb v hv
    rw [map_add, ha v hv, hb v hv, add_zero]
  neg_mem' := by
    intro a ha v hv
    rw [map_neg, ha v hv, neg_zero]

@[simp]
theorem chapter06_mem_kummer_classes_trivial_outside_iff
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
    (S : Finset ι) (a : HMuGlobal) :
    a ∈ chapter06KummerClassesTrivialOutside D S ↔
      ∀ v, v ∉ S → D.kummerRestriction v a = 0 :=
  Iff.rfl

/- The explicit cyclotomic descent in the source has one exceptional class.
   The abstract local data above do not expose a canonical cyclotomic layer,
   so this structure records exactly the resulting defect calculation at the
   finite-S interface: the caller supplies the Wang-special predicate and
   the distinguished defect class, while the two alternatives are stated
   without conflating zero with an unramified class. -/
structure Chapter06WangDefectCalculation
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
    (S : Finset ι) where
  wangSpecial : Prop
  defect : HMuGlobal
  defect_order_two : defect + defect = 0
  defect_nonzero : wangSpecial → defect ≠ 0
  defect_trivial_outside :
    wangSpecial → defect ∈ chapter06KummerClassesTrivialOutside D S
  nonspecial_calculation :
    ¬ wangSpecial → ∀ a,
      a ∈ chapter06KummerClassesTrivialOutside D S ↔ a = 0
  special_calculation :
    wangSpecial → ∀ a,
      a ∈ chapter06KummerClassesTrivialOutside D S ↔
        a = 0 ∨ a = defect

/- The remaining finite cyclotomic calculation translates the exceptional
   Kummer class into the sign obstruction on prescribed local characters.
   `specialPlaces : Finset S` makes the support condition explicit instead of
   silently summing over places outside the prescribed set. -/
structure Chapter06WangSignCalculation
    (G : Type*) (ι : Type*) (HLocal : ι → Type*) (HMuGlobal : Type*)
    [Group G] [TopologicalSpace G]
    (n : ℕ)
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [TopologicalSpace (Chapter06A (2 * n))]
    [IsTopologicalAddGroup (Chapter06A (2 * n))]
    [∀ v, AddCommGroup (HLocal v)] [AddCommGroup HMuGlobal]
    (S : Finset ι)
    (duality :
      Chapter06FiniteSArithmeticDuality G (Chapter06A n) ι HLocal HMuGlobal S)
    where
  positive : 0 < n
  /- This is the actual coefficient inclusion A_n → A_{2n}, rather than an
     unspecified map between two abstract coefficient groups. -/
  canonical_embedding : Chapter06A n →+ Chapter06A (2 * n)
  canonical_embedding_injective : Function.Injective canonical_embedding
  canonical_embedding_eq :
    canonical_embedding = chapter06CanonicalAEmbedding n
  wangSpecial : Prop
  /- The source alternative is stated for local characters whose orders have
     least common multiple n.  The generic local interface has no intrinsic
     order function, so that hypothesis is recorded explicitly here. -/
  has_exact_local_order_n : (∀ v : S, HLocal v) → Prop
  specialPlaces : Finset S
  sign : ∀ v : S, HLocal v → ZMod 2
  lambda_zero_iff :
    ∀ z, duality.lambda z = 0 ↔
      (¬ wangSpecial ∨
        specialPlaces.sum (fun v => sign v (z v)) = 0)
  /- The canonical coefficient map is also required to be compatible with
     the local restrictions.  The target is A_{2n}, not merely another copy
     of A_n, so the exceptional replacement is visible in the API. -/
  canonical_lift :
    Chapter06ContinuousACharacter G (Chapter06A n) →
      Chapter06ContinuousACharacter G (Chapter06A (2 * n))
  canonical_lift_formula :
    ∀ c g, (canonical_lift c).toMul.1 g =
      Multiplicative.ofAdd (canonical_embedding (c.toMul.1 g).toAdd)
  lift_localization :
    Chapter06ContinuousACharacter G (Chapter06A (2 * n)) →+
      (∀ v : S, HLocal v)
  canonical_lift_localization :
    ∀ c, lift_localization (canonical_lift c) = duality.localization c
  /- In the Wang-special, failed-sign case the same local data has an
     A_{2n}-valued global lift.  The final field says that every such lift,
     not just one selected witness, has exact order 2n. -/
  obstructed_lift :
    ∀ z, wangSpecial → has_exact_local_order_n z →
      specialPlaces.sum (fun v => sign v (z v)) ≠ 0 →
      ∃ c₂, lift_localization c₂ = z
  obstructed_lift_exact_order :
    ∀ z c₂, wangSpecial → has_exact_local_order_n z →
      specialPlaces.sum (fun v => sign v (z v)) ≠ 0 →
      lift_localization c₂ = z →
      Nat.card (MonoidHom.range c₂.toMul.1) = 2 * n

/- The sign form of the Grunwald--Wang alternative.  The hypothesis on
   `lambda` is the explicit finite cyclotomic calculation; exactness then
   turns it into the local-to-global statement. -/
theorem chapter06_grunwald_wang_sign_alternative
    {G : Type*} {ι : Type*} {HLocal : ι → Type*} {HMuGlobal : Type*}
    [Group G] [TopologicalSpace G]
    [∀ v, AddCommGroup (HLocal v)] [AddCommGroup HMuGlobal]
    {n : ℕ}
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [TopologicalSpace (Chapter06A (2 * n))]
    [IsTopologicalAddGroup (Chapter06A (2 * n))]
    {S : Finset ι}
    {duality :
      Chapter06FiniteSArithmeticDuality G (Chapter06A n) ι HLocal HMuGlobal S}
    (W : Chapter06WangSignCalculation G ι HLocal HMuGlobal n S duality)
    (z : ∀ v : S, HLocal v) :
    W.has_exact_local_order_n z →
    (∃ x, duality.localization x = z) ↔
      (¬ W.wangSpecial ∨
        W.specialPlaces.sum (fun v => W.sign v (z v)) = 0) := by
  sorry

/- The degree-2n replacement in the obstructed Wang-special case, including
   the exact-order assertion for every compatible lift. -/
theorem chapter06_grunwald_wang_obstructed_lift
    {G : Type*} {ι : Type*} {HLocal : ι → Type*} {HMuGlobal : Type*}
    [Group G] [TopologicalSpace G]
    [∀ v, AddCommGroup (HLocal v)] [AddCommGroup HMuGlobal]
    {n : ℕ}
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [TopologicalSpace (Chapter06A (2 * n))]
    [IsTopologicalAddGroup (Chapter06A (2 * n))]
    {S : Finset ι}
    {duality :
      Chapter06FiniteSArithmeticDuality G (Chapter06A n) ι HLocal HMuGlobal S}
    (W : Chapter06WangSignCalculation G ι HLocal HMuGlobal n S duality)
    (z : ∀ v : S, HLocal v)
    (hwang : W.wangSpecial)
    (hz : W.has_exact_local_order_n z)
    (hsign : W.specialPlaces.sum (fun v => W.sign v (z v)) ≠ 0) :
    ∃ c₂,
      W.lift_localization c₂ = z ∧
        Nat.card (MonoidHom.range c₂.toMul.1) = 2 * n := by
  rcases W.obstructed_lift z hwang hz hsign with ⟨c₂, hc₂⟩
  exact ⟨c₂, hc₂, W.obstructed_lift_exact_order z c₂ hwang hz hsign hc₂⟩

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
  classical
  have hS :=
    (D.archimedean_finite.union D.placesAboveN_finite).union c.property
  refine ⟨hS.toFinset, ?_⟩
  constructor
  · intro v hv
    exact hS.mem_toFinset.mpr (Or.inl (Or.inl hv))
  constructor
  · intro v hv
    exact hS.mem_toFinset.mpr (Or.inl (Or.inr hv))
  · intro v hv
    exact hS.mem_toFinset.mpr (Or.inr hv)

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

private theorem chapter06LocalGlobalLambdaValue_extend_to_finset
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
    (a : HMuGlobal) (S : Finset ι)
    (hS : ∀ v,
      (c v ∉ D.localData.unramified v ∨
        D.kummerRestriction v a ∉ D.localData.unramifiedDual v) → v ∈ S) :
    chapter06LocalGlobalLambdaValue D c a =
      ∑ v ∈ S, chapter06InvariantTargetInclusion n
        (D.localData.pairing v (c v) (D.kummerRestriction v a)) := by
  classical
  let T : Set ι := {v |
    c v ∉ D.localData.unramified v ∨
      D.kummerRestriction v a ∉ D.localData.unramifiedDual v}
  let hT : T.Finite := by
    dsimp [T]
    exact Set.Finite.union c.property (D.kummer_support_finite a)
  have hsub : hT.toFinset ⊆ S := by
    intro v hv
    apply hS v
    simpa [T] using hT.mem_toFinset.mp hv
  change hT.toFinset.sum (fun v =>
      chapter06InvariantTargetInclusion n
        (D.localData.pairing v (c v) (D.kummerRestriction v a))) = _
  apply Finset.sum_subset hsub
  intro v hvS hvT
  have hvT' : v ∉ T := by
    intro hv
    exact hvT (hT.mem_toFinset.mpr hv)
  have hc : c v ∈ D.localData.unramified v := by
    by_contra hc
    exact hvT' (by simpa [T] using Or.inl hc)
  have ha : D.kummerRestriction v a ∈ D.localData.unramifiedDual v := by
    by_contra ha
    exact hvT' (by simpa [T] using Or.inr ha)
  simp [D.localData.unramified_pairing_zero v (c v) hc
    (D.kummerRestriction v a) ha]

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
      map_zero' := by simp [chapter06LocalGlobalLambdaValue]
      map_add' := by
        intro a b
        classical
        let support : HMuGlobal → Set ι := fun a => {v |
          c v ∉ D.localData.unramified v ∨
            D.kummerRestriction v a ∉ D.localData.unramifiedDual v}
        have hsupport : ∀ a, (support a).Finite := by
          intro a
          dsimp [support]
          exact Set.Finite.union c.property (D.kummer_support_finite a)
        let S : Finset ι :=
          ((hsupport (a + b)).toFinset ∪ (hsupport a).toFinset) ∪
            (hsupport b).toFinset
        have h_ab : ∀ v,
            (c v ∉ D.localData.unramified v ∨
              D.kummerRestriction v (a + b) ∉
                D.localData.unramifiedDual v) → v ∈ S := by
          intro v hv
          by_cases hcv : c v ∉ D.localData.unramified v
          · apply Finset.mem_union.mpr
            exact Or.inl (Finset.mem_union.mpr (Or.inl
              ((hsupport (a + b)).mem_toFinset.mpr
                (by simpa [support] using Or.inl hcv))))
          · have hsum : D.kummerRestriction v (a + b) ∉
                D.localData.unramifiedDual v := by
              rcases hv with hcv' | hsum
              · exact (hcv hcv').elim
              · exact hsum
            by_cases hav : D.kummerRestriction v a ∉
                D.localData.unramifiedDual v
            · apply Finset.mem_union.mpr
              exact Or.inl (Finset.mem_union.mpr (Or.inr
                ((hsupport a).mem_toFinset.mpr
                  (by simpa [support] using Or.inr hav))))
            by_cases hbv : D.kummerRestriction v b ∉
                D.localData.unramifiedDual v
            · apply Finset.mem_union.mpr
              exact Or.inr ((hsupport b).mem_toFinset.mpr
                (by simpa [support] using Or.inr hbv))
            · exfalso
              apply hsum
              rw [map_add]
              exact (D.localData.unramifiedDual v).add_mem
                (not_not.mp hav) (not_not.mp hbv)
        have h_a : ∀ v,
            (c v ∉ D.localData.unramified v ∨
              D.kummerRestriction v a ∉
                D.localData.unramifiedDual v) → v ∈ S := by
          intro v hv
          apply Finset.mem_union.mpr
          exact Or.inl (Finset.mem_union.mpr (Or.inr
            ((hsupport a).mem_toFinset.mpr
              (by simpa [support] using hv))))
        have h_b : ∀ v,
            (c v ∉ D.localData.unramified v ∨
              D.kummerRestriction v b ∉
                D.localData.unramifiedDual v) → v ∈ S := by
          intro v hv
          apply Finset.mem_union.mpr
          exact Or.inr ((hsupport b).mem_toFinset.mpr
            (by simpa [support] using hv))
        rw [chapter06LocalGlobalLambdaValue_extend_to_finset D c (a + b) S h_ab,
          chapter06LocalGlobalLambdaValue_extend_to_finset D c a S h_a,
          chapter06LocalGlobalLambdaValue_extend_to_finset D c b S h_b]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        simp [map_add] }
  map_zero' := by
    ext a
    simp [chapter06LocalGlobalLambdaValue]
  map_add' := by
    intro c₁ c₂
    ext a
    classical
    let support :
        Chapter06RestrictedProduct ι HLocal D.localData.unramified → Set ι :=
      fun c' => {v |
        c' v ∉ D.localData.unramified v ∨
          D.kummerRestriction v a ∉ D.localData.unramifiedDual v}
    have hsupport : ∀ c', (support c').Finite := by
      intro c'
      dsimp [support]
      exact Set.Finite.union c'.property (D.kummer_support_finite a)
    let S : Finset ι :=
      ((hsupport (c₁ + c₂)).toFinset ∪ (hsupport c₁).toFinset) ∪
        (hsupport c₂).toFinset
    have hsum : ∀ v,
        ((c₁ + c₂) v ∉ D.localData.unramified v ∨
          D.kummerRestriction v a ∉ D.localData.unramifiedDual v) → v ∈ S := by
      intro v hv
      rcases hv with hcv | hav
      · by_cases h₁v : c₁ v ∉ D.localData.unramified v
        · apply Finset.mem_union.mpr
          exact Or.inl (Finset.mem_union.mpr (Or.inr
            ((hsupport c₁).mem_toFinset.mpr
              (by simpa [support] using Or.inl h₁v))))
        by_cases h₂v : c₂ v ∉ D.localData.unramified v
        · apply Finset.mem_union.mpr
          exact Or.inr ((hsupport c₂).mem_toFinset.mpr
            (by simpa [support] using Or.inl h₂v))
        · exfalso
          apply hcv
          change c₁ v + c₂ v ∈ D.localData.unramified v
          exact (D.localData.unramified v).add_mem
            (not_not.mp h₁v) (not_not.mp h₂v)
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_union.mpr (Or.inr
          ((hsupport c₁).mem_toFinset.mpr
            (by simpa [support] using Or.inr hav))))
    have h₁ : ∀ v,
        (c₁ v ∉ D.localData.unramified v ∨
          D.kummerRestriction v a ∉ D.localData.unramifiedDual v) → v ∈ S := by
      intro v hv
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_union.mpr (Or.inr
        ((hsupport c₁).mem_toFinset.mpr (by simpa [support] using hv))))
    have h₂ : ∀ v,
        (c₂ v ∉ D.localData.unramified v ∨
          D.kummerRestriction v a ∉ D.localData.unramifiedDual v) → v ∈ S := by
      intro v hv
      apply Finset.mem_union.mpr
      exact Or.inr ((hsupport c₂).mem_toFinset.mpr
        (by simpa [support] using hv))
    change chapter06LocalGlobalLambdaValue D (c₁ + c₂) a =
      chapter06LocalGlobalLambdaValue D c₁ a +
        chapter06LocalGlobalLambdaValue D c₂ a
    rw [chapter06LocalGlobalLambdaValue_extend_to_finset D (c₁ + c₂) a S hsum,
      chapter06LocalGlobalLambdaValue_extend_to_finset D c₁ a S h₁,
      chapter06LocalGlobalLambdaValue_extend_to_finset D c₂ a S h₂]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    simp [map_add]

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
  classical
  have h_range_subset :
      Set.range D.localization ⊆
        (chapter06LocalGlobalLambda D) ⁻¹'
          ({0} : Set (HMuGlobal →+ Chapter06QModZ)) := by
    intro c hc
    change chapter06LocalGlobalLambda D c = 0
    ext a
    change chapter06LocalGlobalLambdaValue D c a = 0
    rcases hc with ⟨x, hx⟩
    obtain ⟨S₀, hS₀⟩ := chapter06_admissible_finite_place_set_exists D c
    have hka : Set.Finite {v |
        D.kummerRestriction v a ∉ D.localData.unramifiedDual v} :=
      D.kummer_support_finite a
    let S : Finset ι := S₀ ∪ hka.toFinset
    have hS :
        chapter06AdmissibleFinitePlaceSet D.localData c D.placesAboveN S := by
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        change v ∈ S₀ ∪ hka.toFinset
        exact Finset.mem_union.mpr (Or.inl (hS₀.1 v hv))
      · intro v hv
        change v ∈ S₀ ∪ hka.toFinset
        exact Finset.mem_union.mpr (Or.inl (hS₀.2.1 v hv))
      · intro v hv
        change v ∈ S₀ ∪ hka.toFinset
        exact Finset.mem_union.mpr (Or.inl (hS₀.2.2 v hv))
    obtain ⟨F⟩ := D.finite_level_duality c S hS
    have hloc : F.duality.localization x =
        chapter06FiniteSRestriction c S := by
      funext v
      rw [F.localization_agrees x v, hx]
      rfl
    have hzeroF : F.duality.lambda (chapter06FiniteSRestriction c S) = 0 := by
      have hrange : F.duality.localization x ∈ Set.range F.duality.localization :=
        ⟨x, rfl⟩
      rw [F.duality.exact_at_middle] at hrange
      rw [← hloc]
      exact hrange
    have hvalue : chapter06LocalGlobalLambdaValue D c a =
        ∑ v ∈ S, chapter06InvariantTargetInclusion n
          (D.localData.pairing v (c v) (D.kummerRestriction v a)) :=
      chapter06LocalGlobalLambdaValue_extend_to_finset D c a S (by
        intro v hv
        rcases hv with hcv | hav
        · change v ∈ S₀ ∪ hka.toFinset
          exact Finset.mem_union.mpr (Or.inl (hS₀.2.2 v hcv))
        · change v ∈ S₀ ∪ hka.toFinset
          exact Finset.mem_union.mpr (Or.inr (hka.mem_toFinset.mpr hav)))
    rw [hvalue]
    have hsum_coe :
        (∑ v : S, chapter06InvariantTargetInclusion n
          (D.localData.pairing v.1 (c v.1) (D.kummerRestriction v.1 a))) =
          ∑ v ∈ S, chapter06InvariantTargetInclusion n
            (D.localData.pairing v (c v) (D.kummerRestriction v a)) := by
      exact Finset.sum_coe_sort S (fun v : ι =>
        chapter06InvariantTargetInclusion n
          (D.localData.pairing v (c v) (D.kummerRestriction v a)))
    rw [← hsum_coe]
    have hcond : ∀ v,
        D.kummerRestriction v a ∉ D.localData.unramifiedDual v → v ∈ S := by
      intro v hv
      change v ∈ S₀ ∪ hka.toFinset
      exact Finset.mem_union.mpr (Or.inr (hka.mem_toFinset.mpr hv))
    have hagree := F.lambda_agrees (chapter06FiniteSRestriction c S) a hcond
    have hfinitezero : F.duality.lambda (chapter06FiniteSRestriction c S) a = 0 := by
      simpa using congrArg (fun f => f a) hzeroF
    calc
      (∑ v : S, chapter06InvariantTargetInclusion n
        (D.localData.pairing v.1 (c v.1) (D.kummerRestriction v.1 a))) =
          F.duality.lambda (chapter06FiniteSRestriction c S) a := by
            symm
            simpa [chapter06FiniteSRestriction] using hagree
      _ = 0 := hfinitezero
  have h_injective : Function.Injective D.localization := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply D.component_separation
    intro v
    rw [← D.localization_formula (x - y) v, map_sub, hxy]
    simp
  constructor
  · apply Set.Subset.antisymm
    · exact h_range_subset
    · sorry
  · exact h_injective

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

/- The number-field-specific construction of the distinguished Wang class and
   its degree-2n lift is intentionally separate from the abstract sign
   calculation above; it requires the cyclotomic layer and local square-class
   data that are not parameters of this generic finite-S interface. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
