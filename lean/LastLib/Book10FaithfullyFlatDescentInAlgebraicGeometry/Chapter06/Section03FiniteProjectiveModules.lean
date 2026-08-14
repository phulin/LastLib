import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Section01FiniteGenerationAndPresentation
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Section02FlatModules

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v

/-! ## 6.3 Finite projective modules -/

/-- A finite projective module admits a split cover by a finite free module. -/
theorem finiteProjectiveWitness_of_finiteProjective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : FiniteProjective R M) :
    Nonempty (FiniteProjectiveWitness R M) := by
  letI : Module.Finite R M := hM.1
  letI : Module.Projective R M := hM.2
  obtain ⟨n, f, g, hf, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨⟨n, f, g, hf, hfg⟩⟩

/-- A split finite-free cover makes a module finite projective. -/
theorem finiteProjective_of_witness
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (w : FiniteProjectiveWitness R M) :
    FiniteProjective R M := by
  refine ⟨Module.Finite.of_surjective w.cover w.cover_surjective, ?_⟩
  letI : Module.Projective R (Fin w.index → R) := inferInstance
  exact Module.Projective.of_split w.sectionMap w.cover w.cover_section

theorem finiteProjective_iff_exists_split_finiteFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    FiniteProjective R M ↔ Nonempty (FiniteProjectiveWitness R M) := by
  constructor
  · exact finiteProjectiveWitness_of_finiteProjective
  · rintro ⟨w⟩
    exact finiteProjective_of_witness w

/-- Finite projectivity is equivalent to finite presentation plus flatness. -/
theorem finiteProjective_iff_finitePresentation_and_flat
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    FiniteProjective R M ↔
      Module.FinitePresentation R M ∧ Module.Flat R M := by
  constructor
  · intro hM
    letI : Module.Finite R M := hM.1
    letI : Module.Projective R M := hM.2
    exact ⟨Module.finitePresentation_of_projective R M, inferInstance⟩
  · rintro ⟨hfp, hflat⟩
    letI : Module.FinitePresentation R M := hfp
    letI : Module.Flat R M := hflat
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

theorem finiteProjective_of_finitePresentation_and_flat
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] :
    FiniteProjective R M := by
  exact (finiteProjective_iff_finitePresentation_and_flat (R := R) (M := M)).2
    ⟨inferInstance, inferInstance⟩

/-- The local freeness assertion at a prime used in the local proof. -/
theorem finitePresentation_flat_free_at_prime
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
    (p : PrimeSpectrum R) :
    Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := by
  sorry

/-- A finite free presentation remains exact after tensoring with a residue field. -/
theorem residueField_tensor_presentation_exact
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (n : ℕ) (f : (Fin n → R) →ₗ[R] M)
    (hf : Function.Surjective f) :
    Function.Exact
        ((LinearMap.ker f).subtype.rTensor (ResidueField R))
        (f.rTensor (ResidueField R)) ∧
      Function.Surjective (f.rTensor (ResidueField R)) := by
  sorry

/-- Over a local ring, a residue-field basis of a finite flat module lifts to a basis. -/
theorem finiteFlat_residue_basis_lifts_to_basis
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M]
    (n : ℕ) (b : Basis (Fin n) (ResidueField R)
      (ResidueField R ⊗[R] M)) :
    ∃ (v : Fin n → M) (e : Basis (Fin n) R M),
      (∀ i, TensorProduct.mk R (ResidueField R) M 1 (v i) = b i) ∧
        (∀ i, e i = v i) := by
  sorry

/-- Finite presentation plus flatness gives finite local freeness at every prime. -/
theorem finiteLocallyFree_of_finitePresentation_and_flat
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] :
    FiniteLocallyFree R M := by
  sorry

theorem finiteProjective_iff_finiteLocallyFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    FiniteProjective R M ↔ FiniteLocallyFree R M := by
  sorry

/-- Finite projectivity descends from a faithfully flat finite-projective base change.  The API is
intentionally finite; it makes no unrestricted projectivity-descent claim. -/
theorem finiteProjective_of_faithfullyFlat_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)]
    [Module.Flat B (B ⊗[A] M)] :
    FiniteProjective A M := by
  have hfp : Module.FinitePresentation A M :=
    module_finitePresentation_of_faithfullyFlat_baseChange (A := A) (B := B) (M := M)
  have hflat : Module.Flat A M :=
    flat_of_faithfullyFlat_tensorProduct (A := A) (B := B) (M := M)
  exact (finiteProjective_iff_finitePresentation_and_flat (R := A) (M := M)).2
    ⟨hfp, hflat⟩

theorem finiteProjective_of_faithfullyFlat_baseChange_of_hypothesis
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hB : FiniteProjective B (B ⊗[A] M)) :
    FiniteProjective A M := by
  letI : Module.Finite B (B ⊗[A] M) := hB.1
  letI : Module.Projective B (B ⊗[A] M) := hB.2
  letI : Module.FinitePresentation B (B ⊗[A] M) :=
    Module.finitePresentation_of_projective B (B ⊗[A] M)
  letI : Module.Flat B (B ⊗[A] M) := inferInstance
  exact finiteProjective_of_faithfullyFlat_baseChange (A := A) (B := B) (M := M)

/-- LOCAL_DEPENDENCY_GUESS: the preceding chapter supplies the effective descent-data category;
this object-level equivalence is the restriction of that equivalence to finite projectives. -/
theorem finiteProjective_baseChange_iff
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)]
    [Module.Flat B (B ⊗[A] M)] :
    FiniteProjective A M ↔ FiniteProjective B (B ⊗[A] M) := by
  sorry

/- The preceding equivalence is the object-level restriction of the effective module descent
equivalence.  The concrete descent-data category is supplied by the preceding chapter. -/

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
