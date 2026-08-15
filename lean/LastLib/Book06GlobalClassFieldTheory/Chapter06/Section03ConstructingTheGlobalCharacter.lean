import LastLib.Book06GlobalClassFieldTheory.Chapter06.Section02FiniteLocalGlobalCharacterSequence

/- The local-to-global product below is indexed by the pointwise finite
   Kummer support supplied by Section 6.2's duality data. -/

namespace LastLib.Book06GlobalClassFieldTheory.Chapter06

open scoped BigOperators

noncomputable section

/-! # 6.3. Constructing the global character

This section records the coordinate choice, the local reciprocity
compatibility, the fixed-field construction, and the character form of
existence.  The local reciprocity maps themselves are represented by the
finite reciprocity witness from Dependencies.lean.
-/

/- A finite-order character together with a chosen coordinate in a finite
   cyclic coefficient module.  The image-identification field makes explicit
   that the coordinate is only an identification of the image, not a claim
   that the whole coefficient module is the image. -/
structure Chapter06FiniteOrderCoordinate
    (C : Type*) [CommGroup C] [TopologicalSpace C]
    (n : ℕ) (χ : C →* ℂˣ) where
  positive : 0 < n
  coordinate : C →* Multiplicative (Chapter06A n)
  realization : Multiplicative (Chapter06A n) →* ℂˣ
  realizes : χ = realization.comp coordinate
  faithful_realization : Function.Injective realization
  /- A normalized character of the invariant target.  Keeping this choice in
     the coordinate package prevents an arbitrary additive equivalence with
     ZMod n from silently changing the sign/Frobenius normalization. -/
  invariant_realization :
    Multiplicative (Chapter06OneOverNModOne n) →* ℂˣ
  faithful_invariant_realization : Function.Injective invariant_realization
  /- The invariant exponential is the same finite-image coordinate as the
     chosen character realization, transported across the normalized
     (1/n)Z/Z ≃ Z/nZ identification. -/
  invariant_coordinate :
    Multiplicative (Chapter06OneOverNModOne n) →* Multiplicative (Chapter06A n)
  invariant_coordinate_bijective : Function.Bijective invariant_coordinate
  invariant_realization_compatibility :
    invariant_realization = realization.comp invariant_coordinate
  image_identification :
    Nonempty (MonoidHom.range χ ≃* MonoidHom.range coordinate)

theorem chapter06_finite_order_character_has_coordinate
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (χ : Chapter06ContinuousFiniteOrderCharacter C) :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (Chapter06FiniteOrderCoordinate C n χ.hom) := by
  classical
  obtain ⟨n₀, hn₀, hχ⟩ := χ.finite_order
  have hle : MonoidHom.range χ.hom ≤ rootsOfUnity n₀ ℂ := by
    intro z hz
    rcases hz with ⟨c, rfl⟩
    change (χ.hom c : ℂˣ) ^ n₀ = 1
    exact hχ c
  have hcyclic : IsCyclic (MonoidHom.range χ.hom) := by
    let _ : NeZero n₀ := ⟨Nat.ne_of_gt hn₀⟩
    exact Subgroup.isCyclic_of_le hle
  have hfinite : Finite (MonoidHom.range χ.hom) := by
    let _ : NeZero n₀ := ⟨Nat.ne_of_gt hn₀⟩
    exact Finite.of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  let _ : Finite (MonoidHom.range χ.hom) := hfinite
  let n : ℕ := Nat.card (MonoidHom.range χ.hom)
  have hn : 0 < n := by
    exact Nat.card_pos
  let e : Multiplicative (Chapter06A n) ≃*
      MonoidHom.range χ.hom :=
    let _ : IsCyclic (MonoidHom.range χ.hom) := hcyclic
    zmodCyclicMulEquiv (inferInstance : IsCyclic (MonoidHom.range χ.hom))
  let coordinate : C →* Multiplicative (Chapter06A n) :=
    e.symm.toMonoidHom.comp χ.hom.rangeRestrict
  let realization : Multiplicative (Chapter06A n) →* ℂˣ :=
    (MonoidHom.range χ.hom).subtype.comp e.toMonoidHom
  let invariantEquiv :
      Multiplicative (Chapter06OneOverNModOne n) ≃*
        Multiplicative (Chapter06A n) :=
    (chapter06_oneOverNModOne_equiv_zmod n hn).toMultiplicative
  let invariantCoordinate :
      Multiplicative (Chapter06OneOverNModOne n) →*
        Multiplicative (Chapter06A n) := invariantEquiv.toMonoidHom
  let invariantRealization :
      Multiplicative (Chapter06OneOverNModOne n) →* ℂˣ :=
    realization.comp invariantCoordinate
  let f₀ : MonoidHom.range χ.hom →* Multiplicative (Chapter06A n) :=
    e.symm.toMonoidHom
  have hf₀ : ∀ z : MonoidHom.range χ.hom,
      f₀ z ∈ MonoidHom.range coordinate := by
    intro z
    rcases z.property with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hz : (⟨χ.hom c, ⟨c, rfl⟩⟩ : MonoidHom.range χ.hom) = z := by
      apply Subtype.ext
      exact hc
    change e.symm (χ.hom.rangeRestrict c) = e.symm z
    exact congrArg e.symm hz
  let f : MonoidHom.range χ.hom ≃* MonoidHom.range coordinate :=
    { toFun := fun z => ⟨f₀ z, hf₀ z⟩
      invFun := fun z => e (z : Multiplicative (Chapter06A n))
      left_inv := by
        intro z
        apply Subtype.ext
        simp [f₀, e]
      right_inv := by
        intro z
        apply Subtype.ext
        simp [f₀, e]
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp [f₀] }
  refine ⟨n, hn, ⟨{
    positive := hn
    coordinate := coordinate
    realization := realization
    realizes := by
      ext c
      simp [coordinate, realization]
    faithful_realization := by
      intro x y hxy
      apply e.injective
      apply Subtype.ext
      simpa [realization] using hxy
    invariant_realization := invariantRealization
    faithful_invariant_realization := by
      intro x y hxy
      apply invariantEquiv.injective
      apply e.injective
      apply Subtype.ext
      simpa [invariantRealization, invariantCoordinate, realization] using hxy
    invariant_coordinate := invariantCoordinate
    invariant_coordinate_bijective := invariantEquiv.bijective
    invariant_realization_compatibility := rfl
    image_identification := ⟨f⟩ }⟩⟩

/- Evaluation of an invariant in the chosen finite image.  This is the
   book's exponential of 2 pi i times the invariant, expressed through the
   chosen image identification rather than through representatives in Q/Z. -/
noncomputable def chapter06ExponentialOfInvariant
    (n : ℕ)
    (invariantRealization :
      Multiplicative (Chapter06OneOverNModOne n) →* ℂˣ)
    (x : Chapter06OneOverNModOne n) : ℂˣ :=
  invariantRealization (Multiplicative.ofAdd x)

/- The local reciprocity package attached to a chosen idele-class
   coordinate.  The two evaluations below expose the equality
   exp(2 pi i inv_v(c cup a)) = χ_v(a) from the text: exponentialEvaluation
   is the exponential of the invariant pairing and localEvaluation is the
   corresponding local character value. -/
structure Chapter06CharacterLocalReciprocityData
    (K Ks : Type*) [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    (ι : Type*) (n : ℕ)
    (HLocal HMu HBr HTate : ι → Type*)
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (coordinate :
      Chapter06FiniteOrderCoordinate (Chapter06C K) n χ.hom)
    (D : Chapter06FiniteLocalGlobalCharacterData
      (Chapter06AbsoluteGaloisGroup K Ks) (Chapter06A n) ι n
      HLocal HMu HBr HTate (Chapter06H1Mu K n)) where
  localCharacter :
    Chapter06RestrictedProduct ι HLocal D.localData.unramified
  localEvaluation : ∀ v, HLocal v → HMu v → ℂˣ
  exponentialEvaluation : ∀ v, HLocal v → HMu v → ℂˣ
  exponential_pairing_formula :
    ∀ v c (a : Chapter06H1Mu K n),
        exponentialEvaluation v c (D.kummerRestriction v a) =
        chapter06ExponentialOfInvariant n
          coordinate.invariant_realization
          (D.localData.pairing v c (D.kummerRestriction v a))
  exponential_formula :
    ∀ v c a, exponentialEvaluation v c a = localEvaluation v c a
  unramified_evaluation_one :
    ∀ v c, c ∈ D.localData.unramified v → ∀ a,
      D.kummerRestriction v a ∈ D.localData.unramifiedDual v →
      localEvaluation v c (D.kummerRestriction v a) = 1
  /- The local product is identified with the value of χ on the principal
     idele represented by the global Kummer class.  The separate triviality
     field is the principal-idèle hypothesis from the source; keeping both
     fields makes the orthogonality route explicit rather than assuming its
     additive conclusion. -/
  principal_idele :
    Multiplicative (Chapter06H1Mu K n) →* Chapter06C K
  principal_idele_trivial :
    χ.hom.comp principal_idele = 1
  local_product_eq_principal :
    ∀ a : Chapter06H1Mu K n,
      let s : Set ι := {v |
        localCharacter v ∉ D.localData.unramified v ∨
          D.kummerRestriction v a ∉ D.localData.unramifiedDual v}
      let hs : s.Finite := by
        have hu :
            ({v | localCharacter v ∉ D.localData.unramified v} ∪
              {v | D.kummerRestriction v a ∉ D.localData.unramifiedDual v}).Finite :=
          Set.Finite.union localCharacter.property (D.kummer_support_finite a)
        apply Set.Finite.subset hu
        intro v hv
        simpa only [s, Set.mem_union, Set.mem_ofPred_eq] using hv
      hs.toFinset.prod (fun v =>
        localEvaluation v (localCharacter v) (D.kummerRestriction v a)) =
        χ.hom (principal_idele (Multiplicative.ofAdd a))

/- LOCAL_DEPENDENCY_GUESS: The localEvaluation and exponentialEvaluation
   fields package the compatibility of the finite reciprocity map with the
   local cup-product invariant and norm-residue symbol.  The earlier
   chapters in this worktree do not yet expose a canonical local Artin map,
   so this is the weakest interface needed to prove orthogonality; the
   pointwise Kummer support field makes the displayed product finite. -/

/- The product of the local reciprocity values is trivial on every global
   Kummer class, hence the local family is orthogonal to the global dual. -/
theorem chapter06_idele_character_is_orthogonal
    {K Ks : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (coordinate :
      Chapter06FiniteOrderCoordinate (Chapter06C K) n χ.hom)
    (D : Chapter06FiniteLocalGlobalCharacterData
      (Chapter06AbsoluteGaloisGroup K Ks) (Chapter06A n) ι n
      HLocal HMu HBr HTate (Chapter06H1Mu K n))
    (R : Chapter06CharacterLocalReciprocityData
      K Ks ι n HLocal HMu HBr HTate χ coordinate D) :
    chapter06LocalGlobalLambda D R.localCharacter = 0 := by
  classical
  apply AddMonoidHom.ext
  intro a
  change chapter06LocalGlobalLambdaValue D R.localCharacter a = 0
  let s : Set ι := {v |
    R.localCharacter v ∉ D.localData.unramified v ∨
      D.kummerRestriction v a ∉ D.localData.unramifiedDual v}
  let hs : s.Finite := by
    have hu :
        ({v | R.localCharacter v ∉ D.localData.unramified v} ∪
          {v | D.kummerRestriction v a ∉ D.localData.unramifiedDual v}).Finite :=
      Set.Finite.union R.localCharacter.property (D.kummer_support_finite a)
    apply Set.Finite.subset hu
    intro v hv
    simpa only [s, Set.mem_union, Set.mem_ofPred_eq] using hv
  have hprod :
      hs.toFinset.prod (fun v =>
        R.localEvaluation v (R.localCharacter v)
          (D.kummerRestriction v a)) =
        χ.hom (R.principal_idele (Multiplicative.ofAdd a)) := by
    simpa [s, hs] using R.local_product_eq_principal a
  have hprincipal :
      χ.hom (R.principal_idele (Multiplicative.ofAdd a)) = 1 := by
    have h := congrArg (fun f => f (Multiplicative.ofAdd a))
      R.principal_idele_trivial
    simpa using h
  have hexpprod :
      hs.toFinset.prod (fun v =>
        coordinate.invariant_realization
          (Multiplicative.ofAdd
            (D.localData.pairing v (R.localCharacter v)
              (D.kummerRestriction v a)))) = 1 := by
    calc
      _ = hs.toFinset.prod (fun v =>
          R.localEvaluation v (R.localCharacter v)
            (D.kummerRestriction v a)) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [← R.exponential_formula v (R.localCharacter v)
          (D.kummerRestriction v a)]
        simp [R.exponential_pairing_formula, chapter06ExponentialOfInvariant]
      _ = χ.hom (R.principal_idele (Multiplicative.ofAdd a)) := hprod
      _ = 1 := hprincipal
  have hmul : ∀ T : Finset ι,
      T.prod (fun v =>
        coordinate.invariant_realization
          (Multiplicative.ofAdd
            (D.localData.pairing v (R.localCharacter v)
              (D.kummerRestriction v a)))) =
        coordinate.invariant_realization
          (Multiplicative.ofAdd
            (T.sum (fun v => D.localData.pairing v (R.localCharacter v)
              (D.kummerRestriction v a)))) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert v T hv ih =>
        rw [Finset.prod_insert hv, Finset.sum_insert hv, ih]
        simp
  let qsum : Chapter06OneOverNModOne n :=
    hs.toFinset.sum (fun v =>
      D.localData.pairing v (R.localCharacter v) (D.kummerRestriction v a))
  have hqsum_val : (qsum : Chapter06QModZ) =
      chapter06LocalGlobalLambdaValue D R.localCharacter a := by
    simp [qsum, chapter06LocalGlobalLambdaValue, s,
      chapter06InvariantTargetInclusion]
  have heval :
      coordinate.invariant_realization (Multiplicative.ofAdd qsum) = 1 := by
    rw [← hmul hs.toFinset]
    exact hexpprod
  have hqsum : qsum = 0 := by
    apply coordinate.faithful_invariant_realization
    change coordinate.invariant_realization (Multiplicative.ofAdd qsum) =
      coordinate.invariant_realization
        (Multiplicative.ofAdd (0 : Chapter06OneOverNModOne n))
    simpa using heval
  rw [hqsum] at hqsum_val
  simpa using hqsum_val.symm

/- The exact sequence gives a unique global degree-one class with these
   local restrictions. -/
theorem chapter06_unique_global_class_with_local_restrictions
    {K Ks : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (coordinate :
      Chapter06FiniteOrderCoordinate (Chapter06C K) n χ.hom)
    (D : Chapter06FiniteLocalGlobalCharacterData
      (Chapter06AbsoluteGaloisGroup K Ks) (Chapter06A n) ι n
      HLocal HMu HBr HTate (Chapter06H1Mu K n))
    (R : Chapter06CharacterLocalReciprocityData
      K Ks ι n HLocal HMu HBr HTate χ coordinate D) :
    ∃! c : Chapter06H1A (Chapter06AbsoluteGaloisGroup K Ks) n,
      D.localization c = R.localCharacter := by
  sorry

/- Fixed field of a complex-valued finite-image Galois character. -/
noncomputable def chapter06FixedFieldOfComplexCharacter
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    (ψ : Gal(Ks / K) →* ℂˣ) : IntermediateField K Ks :=
  IntermediateField.fixedField ψ.ker

/- The finite cyclic extension cut out by a global A_n-character.  Reciprocity
   is deliberately not stored here: it is a separate global Artin input, and
   putting it into this field-theoretic package would make the fixed-field
   construction circular. -/
structure Chapter06CyclicCharacterField
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    (n : ℕ)
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [DiscreteTopology (Chapter06A n)]
    (c : Chapter06H1A (Chapter06AbsoluteGaloisGroup K Ks) n) where
  positive : 0 < n
  field : IntermediateField K Ks
  [finite : FiniteDimensional K field]
  [abelian : IsAbelianGalois K field]
  [galoisFinite : Finite (Gal(field / K))]
  cyclic : IsCyclic (Gal(field / K))
  field_eq_fixed :
    field = chapter06FixedFieldOfCharacter c.toMul.1
  surjective_restriction :
    Function.Surjective
      (chapter06AbelianGaloisRestriction (K := K) field abelian)
  galoisCharacter :
    Gal(field / K) →* Multiplicative (Chapter06A n)
  faithful : Function.Injective galoisCharacter
  factorization :
    c.toMul.1 =
      galoisCharacter.comp
        (chapter06AbelianGaloisRestriction (K := K) field abelian)
  degree_eq_image :
    chapter06GaloisDegree (K := K) (L := field) =
      Nat.card (MonoidHom.range c.toMul.1)

theorem chapter06_global_class_fixed_field_is_cyclic
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ) (hn : 0 < n)
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    [DiscreteTopology (Chapter06A n)]
    (c : Chapter06H1A (Chapter06AbsoluteGaloisGroup K Ks) n) :
    Nonempty (Chapter06CyclicCharacterField K Ks n c) := by
  classical
  let φ : Gal(Ks / K) →* Multiplicative (Chapter06A n) := c.toMul.1
  let H : Subgroup (Gal(Ks / K)) := φ.ker
  have hopenH : IsOpen (H : Set (Gal(Ks / K))) := by
    change IsOpen (φ ⁻¹' ({1} : Set (Multiplicative (Chapter06A n))))
    exact IsOpen.preimage c.toMul.2 (isOpen_discrete _)
  have hclosedH : IsClosed (H : Set (Gal(Ks / K))) := by
    change IsClosed (φ ⁻¹' ({1} : Set (Multiplicative (Chapter06A n))))
    exact IsClosed.preimage c.toMul.2 (isClosed_discrete _)
  let _ : H.Normal := MonoidHom.normal_ker φ
  let Hclosed : ClosedSubgroup (Gal(Ks / K)) := ⟨H, hclosedH⟩
  let L : IntermediateField K Ks := IntermediateField.fixedField H
  have hfix : L.fixingSubgroup = H := by
    change (IntermediateField.fixedField H).fixingSubgroup = H
    exact InfiniteGalois.fixingSubgroup_fixedField Hclosed
  have hfiniteDimensional : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    rw [hfix]
    exact hopenH
  let _ : FiniteDimensional K L := hfiniteDimensional
  let _ : IsGalois K L := IsGalois.of_fixedField_normal_subgroup H
  let e : (Gal(Ks / K) ⧸ H) ≃* Gal(L / K) :=
    InfiniteGalois.normalAutEquivQuotient Hclosed
  let q : (Gal(Ks / K) ⧸ H) ≃* MonoidHom.range φ := by
    simpa [H] using (QuotientGroup.quotientKerEquivRange φ)
  have hcycRange : IsCyclic (MonoidHom.range φ) := by
    let _ : IsCyclic (Multiplicative (Chapter06A n)) := by
      infer_instance
    exact Subgroup.isCyclic_of_le (show MonoidHom.range φ ≤ ⊤ from le_top)
  let _ : IsCyclic (Gal(L / K)) := by
    apply isCyclic_of_surjective
      (e.toMonoidHom.comp q.symm.toMonoidHom)
    exact e.surjective.comp q.symm.surjective
  let _ : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  let galoisCharacter : Gal(L / K) →* Multiplicative (Chapter06A n) :=
    (MonoidHom.range φ).subtype.comp
      (q.toMonoidHom.comp e.symm.toMonoidHom)
  have hfactor :
      φ = galoisCharacter.comp
        (chapter06AbelianGaloisRestriction (K := K) L
          (inferInstance : IsAbelianGalois K L)) := by
    apply MonoidHom.ext
    intro σ
    change φ σ = galoisCharacter
      (chapter06AbelianGaloisRestriction (K := K) L
        (inferInstance : IsAbelianGalois K L) σ)
    have heq : e (QuotientGroup.mk' H σ) =
        chapter06AbelianGaloisRestriction (K := K) L
          (inferInstance : IsAbelianGalois K L) σ := by
      exact InfiniteGalois.normalAutEquivQuotient_apply Hclosed σ
    rw [← heq]
    dsimp [galoisCharacter]
    rw [e.symm_apply_apply]
    change φ σ = ((q (QuotientGroup.mk' H σ) : MonoidHom.range φ) :
      Multiplicative (Chapter06A n))
    have hq : q (QuotientGroup.mk' H σ) =
        (⟨φ σ, ⟨σ, rfl⟩⟩ : MonoidHom.range φ) := by
      rfl
    rw [hq]
  have hfaithful : Function.Injective galoisCharacter := by
    intro x y hxy
    apply e.symm.injective
    apply q.injective
    apply Subtype.ext
    exact hxy
  have hsurjective :
      Function.Surjective
        (chapter06AbelianGaloisRestriction (K := K) L
          (inferInstance : IsAbelianGalois K L)) := by
    simpa [chapter06AbelianGaloisRestriction, chapter06GaloisRestriction] using
      (AlgEquiv.restrictNormalHom_surjective
        (F := K) (K₁ := L) (E := Ks))
  refine ⟨{
    positive := hn
    field := L
    finite := hfiniteDimensional
    abelian := inferInstance
    galoisFinite := inferInstance
    cyclic := inferInstance
    field_eq_fixed := rfl
    surjective_restriction := hsurjective
    galoisCharacter := galoisCharacter
    faithful := hfaithful
    factorization := by simpa [φ] using hfactor
    degree_eq_image := by
      change Module.finrank K L = Nat.card (MonoidHom.range φ)
      calc
        Module.finrank K L = Nat.card (Gal(L / K)) :=
          (IsGalois.card_aut_eq_finrank K L).symm
        _ = Nat.card (Gal(Ks / K) ⧸ H) :=
          (Nat.card_congr e.toEquiv).symm
        _ = Nat.card (MonoidHom.range φ) := Nat.card_congr q.toEquiv
  }⟩

/- The intrinsic correspondence predicate for the finite-image character
   in Lemma 6.2.  It uses a C-valued finite reciprocity witness and a
   faithful character of its finite Galois group. -/
def chapter06GaloisCharacterCorresponds
    {K Ks : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (ψ : Chapter06ContinuousFiniteImageCharacter
      (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ) : Prop :=
  ∃ (R : Chapter06FiniteReciprocityWitness K Ks (Chapter06C K))
    (_cyclic : IsCyclic (Gal(R.extension.field / K)))
    (bar : Gal(R.extension.field / K) →* ℂˣ),
    R.extension.field = chapter06FixedFieldOfComplexCharacter ψ.hom ∧
      Function.Injective bar ∧
      Function.Surjective
        (chapter06FiniteExtensionRestriction R.extension) ∧
      ψ.hom =
        bar.comp (chapter06FiniteExtensionRestriction R.extension) ∧
      χ.hom = bar.comp R.artin ∧
      Nonempty (MonoidHom.range χ.hom ≃* MonoidHom.range ψ.hom) ∧
      χ.hom.ker = chapter06NormSubgroup R.extension.normMap

theorem chapter06_galois_character_correspondence_kernel
    {K Ks : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (ψ : Chapter06ContinuousFiniteImageCharacter
      (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ)
    (h : chapter06GaloisCharacterCorresponds χ ψ) :
    ∃ R : Chapter06FiniteReciprocityWitness K Ks (Chapter06C K),
      χ.hom.ker = chapter06NormSubgroup R.extension.normMap := by
  rcases h with
    ⟨R, cyclic, bar, hfield, hbar, hrestriction, hψ, hχ,
      himage, hnorm⟩
  exact ⟨R, hnorm⟩

theorem chapter06_character_image_orders_agree
    {K Ks : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (ψ : Chapter06ContinuousFiniteImageCharacter
      (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ)
    (h : chapter06GaloisCharacterCorresponds χ ψ) :
    Nonempty (MonoidHom.range χ.hom ≃* MonoidHom.range ψ.hom) := by
  rcases h with
    ⟨R, cyclic, bar, hfield, hbar, hrestriction, hψ, hχ,
      himage, hnorm⟩
  exact himage

/- Lemma 6.2: every continuous finite-order idele-class character has a
   unique finite-image character of the absolute Galois group. -/
theorem chapter06_lemma_6_2_character_existence
    {K Ks : Type*} [Field K] [NumberField K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    :
    ∃! ψ : Chapter06ContinuousFiniteImageCharacter
        (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ,
      chapter06GaloisCharacterCorresponds χ ψ := by
  sorry

/- Kummer radical presentation of a field generated by one nth root. -/
def Chapter06KummerRadicalPresentation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (a : K) : Prop :=
  ∃ α : L, α ^ n = algebraMap K L a ∧
    Algebra.adjoin K ({α} : Set L) = ⊤

structure Chapter06KummerRadicalField
    (K : Type*) [Field K] (n : ℕ) (a : K) where
  positive : 0 < n
  field : Type
  [fieldField : Field field]
  [fieldAlgebra : Algebra K field]
  [finite : FiniteDimensional K field]
  presentation : Chapter06KummerRadicalPresentation K field n a

/- The roots-of-unity specialization of the twisted Cartier-dual
   formulation. -/
structure Chapter06RootOfUnitySelfDuality
    (K : Type*) [Field K] (n : ℕ) (ι : Type*)
    (HLocal HMu : ι → Type*)
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    (U : ∀ v, AddSubgroup (HLocal v)) where
  positive : 0 < n
  primitive_root :
    ∃ ζ : Chapter06CartierDual K n, orderOf ζ = n
  self_duality :
    Nonempty (Chapter06A n ≃+ Additive (Chapter06CartierDual K n))
  hilbertSymbol : ∀ v, HLocal v → HMu v → ℂˣ
  unramifiedDual : ∀ v, AddSubgroup (HMu v)
  kummerRestriction :
    ∀ v, Chapter06KummerClassGroup K n → HMu v
  kummer_support_finite :
    ∀ a, Set.Finite {v | kummerRestriction v a ∉ unramifiedDual v}
  unramified_hilbertSymbol_one :
    ∀ v c, c ∈ U v → ∀ a,
      kummerRestriction v a ∈ unramifiedDual v →
      hilbertSymbol v c (kummerRestriction v a) = 1
  hilbert_symbol_product :
    ∀ (c : Chapter06RestrictedProduct ι HLocal U)
      (a : Chapter06KummerClassGroup K n),
      let s : Set ι := {v |
        c v ∉ U v ∨ kummerRestriction v a ∉ unramifiedDual v}
      let hs : s.Finite := by
        have hu :
            ({v | c v ∉ U v} ∪
              {v | kummerRestriction v a ∉ unramifiedDual v}).Finite :=
          Set.Finite.union c.property (kummer_support_finite a)
        apply Set.Finite.subset hu
        intro v hv
        simpa only [s, Set.mem_union, Set.mem_ofPred_eq] using hv
      hs.toFinset.prod (fun v =>
        hilbertSymbol v (c v) (kummerRestriction v a)) = 1
  kummer_field :
    ∀ a : K, Nonempty (Chapter06KummerRadicalField K n a)

/- The actual twisted dual is a Galois representation on the geometric
   roots-of-unity module.  No primitive root in K is needed; the base-field
   roots alias above remains reserved for the self-dual specialization. -/
abbrev Chapter06TwistedCartierDualCarrier
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks] (n : ℕ) :=
  Additive (Chapter06GeometricCartierDual K Ks n)

abbrev Chapter06TwistedCartierDual
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ) :=
  Representation ℤ (Gal(Ks / K)) (Chapter06TwistedCartierDualCarrier K Ks n)

noncomputable def chapter06TwistedCartierDualRepresentation
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ) :
    Chapter06TwistedCartierDual K Ks n :=
  chapter06GeometricCartierDualRepresentation K Ks n

@[simp]
theorem chapter06TwistedCartierDualRepresentation_apply
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ)
    (σ : Gal(Ks / K))
    (ζ : Chapter06GeometricCartierDual K Ks n) :
    chapter06TwistedCartierDualRepresentation K Ks n σ
        (Additive.ofMul ζ) =
      Additive.ofMul (restrictRootsOfUnity σ.toAlgHom n ζ) := by
  rfl

theorem chapter06_without_roots_of_unity_uses_twisted_dual
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [IsGalois K Ks] [IsSepClosed Ks] (n : ℕ) :
    Nonempty (Chapter06TwistedCartierDual K Ks n) :=
  ⟨chapter06TwistedCartierDualRepresentation K Ks n⟩

/- The coordinate, the local duality data, and the finite reciprocity witness
   are proof data for the construction; the theorem above states uniqueness
   only for the intrinsic C-valued Galois character. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
