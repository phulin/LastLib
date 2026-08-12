import LastLib.Book06GlobalClassFieldTheory.Chapter06.Section02FiniteLocalGlobalCharacterSequence

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
  image_identification :
    Nonempty (MonoidHom.range χ ≃* MonoidHom.range coordinate)

theorem chapter06_finite_order_character_has_coordinate
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (χ : Chapter06ContinuousFiniteOrderCharacter C) :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (Chapter06FiniteOrderCoordinate C n χ.hom) := by
  sorry

/- Evaluation of an invariant in the chosen finite image.  This is the
   book's exponential of 2 pi i times the invariant, expressed through the
   chosen image identification rather than through representatives in Q/Z. -/
noncomputable def chapter06ExponentialOfInvariant
    (n : ℕ) (hn : 0 < n)
    (realization : Multiplicative (Chapter06A n) →* ℂˣ)
    (x : Chapter06OneOverNModOne n) : ℂˣ :=
  realization
    (Multiplicative.ofAdd ((chapter06_oneOverNModOne_equiv_zmod n hn) x))

/- The local reciprocity package attached to a chosen idele-class
   coordinate.  The two evaluations below expose the equality
   exp(2 pi i inv_v(c cup a)) = χ_v(a) from the text: exponentialEvaluation
   is the exponential of the invariant pairing and localEvaluation is the
   corresponding local character value. -/
structure Chapter06CharacterLocalReciprocityData
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
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
        chapter06ExponentialOfInvariant n coordinate.positive
          coordinate.realization
          (D.localData.pairing v c (D.kummerRestriction v a))
  exponential_formula :
    ∀ v c a, exponentialEvaluation v c a = localEvaluation v c a
  unramified_evaluation_one :
    ∀ v c, c ∈ D.localData.unramified v → ∀ a,
      localEvaluation v c (D.kummerRestriction v a) = 1
  principal_product :
    ∀ a : Chapter06H1Mu K n,
      chapter06RestrictedProductProduct localCharacter
        (fun v cv => localEvaluation v cv (D.kummerRestriction v a))
        (by
          intro v cv hcv
          exact unramified_evaluation_one v cv hcv a) = 1

/- LOCAL_DEPENDENCY_GUESS: The localEvaluation and exponentialEvaluation
   fields package the compatibility of the finite reciprocity map with the
   local cup-product invariant and norm-residue symbol.  The earlier
   chapters in this worktree do not yet expose a canonical local Artin map,
   so this is the weakest interface needed to prove orthogonality. -/

/- The product of the local reciprocity values is trivial on every global
   Kummer class, hence the local family is orthogonal to the global dual. -/
theorem chapter06_idele_character_is_orthogonal
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
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
  sorry

/- The exact sequence gives a unique global degree-one class with these
   local restrictions. -/
theorem chapter06_unique_global_class_with_local_restrictions
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
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
    (ψ : Gal(Ks / K) →* ℂˣ) : IntermediateField K Ks :=
  IntermediateField.fixedField ψ.ker

/- The cyclic finite extension cut out by a global A_n-character. -/
structure Chapter06CyclicCharacterField
    (K Ks : Type*) [Field K] [Field Ks] [Algebra K Ks]
    [Chapter06IdeleClassGroup K] (n : ℕ)
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    (c : Chapter06H1A (Chapter06AbsoluteGaloisGroup K Ks) n) where
  extension : Chapter06FiniteCyclicExtension K Ks (Chapter06C K)
  field_eq_fixed :
    extension.extension.field = chapter06FixedFieldOfCharacter c.toMul.1
  restriction :
    Gal(Ks / K) →* Gal(extension.extension.field / K)
  galoisCharacter :
    Gal(extension.extension.field / K) →* Multiplicative (Chapter06A n)
  faithful : Function.Injective galoisCharacter
  factorization :
    c.toMul.1 = galoisCharacter.comp restriction
  degree_eq_image :
    chapter06GaloisDegree (K := K) (L := extension.extension.field) =
      Nat.card (MonoidHom.range c.toMul.1)
  reciprocity : Chapter06FiniteReciprocityWitness K Ks (Chapter06C K)
  reciprocity_field :
    reciprocity.extension.field = extension.extension.field

theorem chapter06_global_class_fixed_field_is_cyclic
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [Chapter06IdeleClassGroup K] (n : ℕ)
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    (c : Chapter06H1A (Chapter06AbsoluteGaloisGroup K Ks) n) :
    Nonempty (Chapter06CyclicCharacterField K Ks n c) := by
  sorry

/- The intrinsic correspondence predicate for the finite-image character
   in Lemma 6.2.  It uses a C-valued finite reciprocity witness and a
   faithful character of its finite Galois group. -/
def chapter06GaloisCharacterCorresponds
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (ψ : Chapter06ContinuousFiniteImageCharacter
      (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ) : Prop :=
  ∃ (R : Chapter06FiniteReciprocityWitness K Ks (Chapter06C K))
    (_cyclic : IsCyclic (Gal(R.extension.field / K)))
    (bar : Gal(R.extension.field / K) →* ℂˣ)
    (restriction :
      Gal(Ks / K) →* Gal(R.extension.field / K)),
    R.extension.field = chapter06FixedFieldOfComplexCharacter ψ.hom ∧
      Function.Injective bar ∧
      ψ.hom = bar.comp restriction ∧
      χ.hom = bar.comp R.artin ∧
      Nonempty (MonoidHom.range χ.hom ≃* MonoidHom.range ψ.hom) ∧
      χ.hom.ker = chapter06NormSubgroup R.extension.normMap

theorem chapter06_galois_character_correspondence_kernel
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (ψ : Chapter06ContinuousFiniteImageCharacter
      (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ)
    (h : chapter06GaloisCharacterCorresponds χ ψ) :
    ∃ R : Chapter06FiniteReciprocityWitness K Ks (Chapter06C K),
      χ.hom.ker = chapter06NormSubgroup R.extension.normMap := by
  rcases h with
    ⟨R, cyclic, bar, restriction, hfield, hbar, hψ, hχ, himage, hnorm⟩
  exact ⟨R, hnorm⟩

theorem chapter06_character_image_orders_agree
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [Chapter06IdeleClassGroup K]
    (χ : Chapter06IdeleClassCharacter K)
    (ψ : Chapter06ContinuousFiniteImageCharacter
      (Chapter06AbsoluteGaloisGroup K Ks) ℂˣ)
    (h : chapter06GaloisCharacterCorresponds χ ψ) :
    Nonempty (MonoidHom.range χ.hom ≃* MonoidHom.range ψ.hom) := by
  rcases h with
    ⟨R, cyclic, bar, restriction, hfield, hbar, hψ, hχ, himage, hnorm⟩
  exact himage

/- Lemma 6.2: every continuous finite-order idele-class character has a
   unique finite-image character of the absolute Galois group. -/
theorem chapter06_lemma_6_2_character_existence
    {K Ks : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [Chapter06IdeleClassGroup K]
    {ι : Type*} {n : ℕ}
    {HLocal HMu HBr HTate : ι → Type*}
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    [∀ v, AddCommGroup (HBr v)]
    [∀ v, AddCommGroup (HTate v)]
    [TopologicalSpace (Chapter06A n)]
    [IsTopologicalAddGroup (Chapter06A n)]
    (χ : Chapter06IdeleClassCharacter K)
    (coordinate :
      Chapter06FiniteOrderCoordinate (Chapter06C K) n χ.hom)
    (D : Chapter06FiniteLocalGlobalCharacterData
      (Chapter06AbsoluteGaloisGroup K Ks) (Chapter06A n) ι n
      HLocal HMu HBr HTate (Chapter06H1Mu K n))
    (R : Chapter06CharacterLocalReciprocityData
      K Ks ι n HLocal HMu HBr HTate χ coordinate D) :
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
  field : Type
  [fieldField : Field field]
  [fieldAlgebra : Algebra K field]
  presentation : Chapter06KummerRadicalPresentation K field n a

/- The roots-of-unity specialization of the twisted Cartier-dual
   formulation. -/
structure Chapter06RootOfUnitySelfDuality
    (K : Type*) [Field K] (n : ℕ) (ι : Type*)
    (HLocal HMu : ι → Type*)
    [∀ v, AddCommGroup (HLocal v)]
    [∀ v, AddCommGroup (HMu v)]
    (U : ∀ v, AddSubgroup (HLocal v)) where
  primitive_root :
    ∃ ζ : Chapter06CartierDual K n, orderOf ζ = n
  self_duality :
    Nonempty (Chapter06A n ≃+ Additive (Chapter06CartierDual K n))
  hilbertSymbol : ∀ v, HLocal v → HMu v → ℂˣ
  unramified_hilbertSymbol_one :
    ∀ v c, c ∈ U v → ∀ a, hilbertSymbol v c a = 1
  kummerRestriction :
    ∀ v, Chapter06KummerClassGroup K n → HMu v
  hilbert_symbol_product :
    ∀ (c : Chapter06RestrictedProduct ι HLocal U)
      (a : Chapter06KummerClassGroup K n),
      chapter06RestrictedProductProduct c
        (fun v cv => hilbertSymbol v cv (kummerRestriction v a))
        (by
          intro v cv hcv
          exact unramified_hilbertSymbol_one v cv hcv (kummerRestriction v a)) = 1
  kummer_field :
    ∀ a : K, Nonempty (Chapter06KummerRadicalField K n a)

/- The actual twisted dual module remains the roots-of-unity module even
   when no primitive root is chosen in K. -/
abbrev Chapter06TwistedCartierDual
    (K : Type*) [Field K] (n : ℕ) :=
  Additive (Chapter06CartierDual K n)

theorem chapter06_without_roots_of_unity_uses_twisted_dual
    {K : Type*} [Field K] (n : ℕ) :
    Chapter06TwistedCartierDual K n =
      Additive (Chapter06CartierDual K n) :=
  rfl

/- SOURCE_ISSUE: Section 6.3 says that, after identifying the image of χ
   with a subgroup of A_n, Lemma 6.2 gives a unique finite-image character
   of G_K.  The text does not say whether uniqueness is meant for the
   intrinsic C-valued character or for the chosen coordinate and its n.
   This API makes the coordinate explicit and states uniqueness for the
   intrinsic C-valued Galois character. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter06
