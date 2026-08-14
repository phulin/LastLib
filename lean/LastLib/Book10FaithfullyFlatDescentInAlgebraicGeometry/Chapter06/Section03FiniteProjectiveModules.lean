import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Section01FiniteGenerationAndPresentation
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Section02FlatModules
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05.Section02ProofOfEffectivity

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct
open CategoryTheory
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter05

universe u v

/-! ## 6.3 Finite projective modules -/

/-- A finite projective module admits a split cover by a finite free module. -/
theorem finiteProjectiveWitness_of_finiteProjective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : FiniteProjective R M) :
    Nonempty (FiniteProjectiveWitness R M) := by
  have : Module.Finite R M := hM.1
  have : Module.Projective R M := hM.2
  obtain ⟨n, f, g, hf, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨⟨n, f, g, hf, hfg⟩⟩

/-- A split finite-free cover makes a module finite projective. -/
theorem finiteProjective_of_witness
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (w : FiniteProjectiveWitness R M) :
    FiniteProjective R M := by
  refine ⟨Module.Finite.of_surjective w.cover w.cover_surjective, ?_⟩
  have : Module.Projective R (Fin w.index → R) := inferInstance
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
    have : Module.Finite R M := hM.1
    have : Module.Projective R M := hM.2
    exact ⟨Module.finitePresentation_of_projective R M, inferInstance⟩
  · rintro ⟨hfp, hflat⟩
    have : Module.FinitePresentation R M := hfp
    have : Module.Flat R M := hflat
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
  exact Module.free_of_flat_of_isLocalRing

/-- A finite free presentation remains exact after tensoring with a residue field. -/
theorem residueField_tensor_presentation_exact
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (n : ℕ) (f : (Fin n → R) →ₗ[R] M)
    (hf : Function.Surjective f) :
    Function.Exact
        ((LinearMap.ker f).subtype.rTensor (IsLocalRing.ResidueField R))
        (f.rTensor (IsLocalRing.ResidueField R)) ∧
      Function.Surjective (f.rTensor (IsLocalRing.ResidueField R)) := by
  exact ⟨rTensor_exact (M := LinearMap.ker f)
      (IsLocalRing.ResidueField R) (LinearMap.exact_subtype_ker_map f) hf,
    LinearMap.rTensor_surjective (IsLocalRing.ResidueField R) hf⟩

/-- Over a local ring, a residue-field basis of a finite flat module lifts to a basis. -/
theorem finiteFlat_residue_basis_lifts_to_basis
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M]
    (n : ℕ) (b : Module.Basis (Fin n) (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M)) :
    ∃ (v : Fin n → M) (e : Module.Basis (Fin n) R M),
      (∀ i, TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 (v i) = b i) ∧
        (∀ i, e i = v i) := by
  let k := IsLocalRing.ResidueField R
  choose v hv using fun i : Fin n ↦
    (TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective) (b i)
  have hlin : Function.Bijective
      (Finsupp.linearCombination k (TensorProduct.mk R k M 1 ∘ v)) := by
    have hmap : Finsupp.linearCombination k (TensorProduct.mk R k M 1 ∘ v) =
        Finsupp.linearCombination k b := by
      ext x
      simp [Finsupp.linearCombination_single, hv x]
    rw [hmap]
    rw [← Module.Basis.coe_repr_symm b]
    exact b.repr.symm.bijective
  have hlinR : Function.Bijective (Finsupp.linearCombination R v) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat v hlin
  let e : Module.Basis (Fin n) R M :=
    Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination R v) hlinR).symm
  refine ⟨v, e, ?_, ?_⟩
  · simpa [k] using hv
  · intro i
    simp [e]

/-- Finite presentation plus flatness gives finite local freeness at every prime. -/
theorem finiteLocallyFree_of_finitePresentation_and_flat
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] :
    FiniteLocallyFree R M := by
  refine ⟨inferInstance, ?_⟩
  intro p
  exact finitePresentation_flat_free_at_prime p

theorem finiteProjective_iff_finiteLocallyFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    FiniteProjective R M ↔ FiniteLocallyFree R M := by
  constructor
  · intro hM
    have h := (finiteProjective_iff_finitePresentation_and_flat (R := R) (M := M)).1 hM
    have : Module.FinitePresentation R M := h.1
    have : Module.Flat R M := h.2
    exact finiteLocallyFree_of_finitePresentation_and_flat (R := R) (M := M)
  · rintro ⟨hfp, hfree⟩
    have : Module.FinitePresentation R M := hfp
    have hproj : Module.Projective R M := by
      apply (Module.freeLocus_eq_univ_iff (R := R) (M := M)).mp
      apply Set.eq_univ_iff_forall.mpr
      intro p
      exact Module.mem_freeLocus.mpr (hfree p)
    exact ⟨inferInstance, hproj⟩

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
  have : Module.Finite B (B ⊗[A] M) := hB.1
  have : Module.Projective B (B ⊗[A] M) := hB.2
  have : Module.FinitePresentation B (B ⊗[A] M) :=
    Module.finitePresentation_of_projective B (B ⊗[A] M)
  have : Module.Flat B (B ⊗[A] M) := inferInstance
  exact finiteProjective_of_faithfullyFlat_baseChange (A := A) (B := B) (M := M)

/-! The effective module-descent equivalence restricts to the finite-projective objects. -/
theorem finiteProjective_descent_restriction
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (D : DescentDatum A B) :
    (∃ M : ModuleCat A,
      FiniteProjective A M ∧
        Nonempty
          (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M) ≅ D)) ↔
      FiniteProjective B D.A := by
  let hff : RingHom.FaithfullyFlat (algebraMap A B) :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  constructor
  · rintro ⟨M, hM, ⟨e⟩⟩
    let _ : IsScalarTower A B
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
      IsScalarTower.of_compHom (R := A) (A := B)
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
    let eTensor :
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) ≃ₗ[B]
          (B ⊗[A] (M : Type _)) := by
      exact TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B B) (LinearEquiv.refl A (M : Type _))
    have hbase' : FiniteProjective B (B ⊗[A] (M : Type _)) := by
      have : Module.Finite A (M : Type _) := hM.1
      have : Module.Projective A (M : Type _) := hM.2
      exact ⟨inferInstance, inferInstance⟩
    have : Module.Finite B (B ⊗[A] (M : Type _)) := hbase'.1
    have : Module.Projective B (B ⊗[A] (M : Type _)) := hbase'.2
    have hbaseExt : FiniteProjective B
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
      ⟨Module.Finite.equiv eTensor.symm,
        Module.Projective.of_equiv' eTensor.symm⟩
    have hbase : FiniteProjective B
        (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A) := by
      rw [faithfullyFlatDescentFunctor_obj_underlying]
      exact hbaseExt
    have : Module.Finite B
        (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A) := hbase.1
    have : Module.Projective B
        (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A) := hbase.2
    have h₁ : e.hom.f.hom.comp e.inv.f.hom = LinearMap.id := by
      have h := congrArg (fun k => k.f.hom) e.inv_hom_id
      exact h
    have h₂ : e.inv.f.hom.comp e.hom.f.hom = LinearMap.id := by
      have h := congrArg (fun k => k.f.hom) e.hom_inv_id
      exact h
    let e' : (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A) ≃ₗ[B] D.A :=
      LinearEquiv.ofLinearMap e.hom.f.hom e.inv.f.hom h₁ h₂
    exact ⟨Module.Finite.equiv e', Module.Projective.of_equiv' e'⟩
  · intro hD
    obtain ⟨M, ⟨e⟩⟩ := faithfullyFlat_module_descent_essential_surjective hff D
    have : Module.Finite B D.A := hD.1
    have : Module.Projective B D.A := hD.2
    have h₁ : e.inv.f.hom.comp e.hom.f.hom = LinearMap.id := by
      have h := congrArg (fun k => k.f.hom) e.hom_inv_id
      exact h
    have h₂ : e.hom.f.hom.comp e.inv.f.hom = LinearMap.id := by
      have h := congrArg (fun k => k.f.hom) e.inv_hom_id
      exact h
    let e' : D.A ≃ₗ[B]
        (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A) :=
      LinearEquiv.ofLinearMap e.inv.f.hom e.hom.f.hom h₁ h₂
    have hbase : FiniteProjective B
        (((faithfullyFlatDescentFunctor (A := A) (B := B)).obj M).A) := by
      exact ⟨Module.Finite.equiv e', Module.Projective.of_equiv' e'⟩
    let _ : IsScalarTower A B
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
      IsScalarTower.of_compHom (R := A) (A := B)
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
    let eTensor :
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) ≃ₗ[B]
          (B ⊗[A] (M : Type _)) := by
      exact TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B B) (LinearEquiv.refl A (M : Type _))
    have hbaseExt : FiniteProjective B
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
      rw [← faithfullyFlatDescentFunctor_obj_underlying M]
      exact hbase
    have : Module.Finite B
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) := hbaseExt.1
    have : Module.Projective B
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) := hbaseExt.2
    have hbase' : FiniteProjective B (B ⊗[A] (M : Type _)) :=
      ⟨Module.Finite.equiv eTensor, Module.Projective.of_equiv' eTensor⟩
    refine ⟨M, finiteProjective_of_faithfullyFlat_baseChange_of_hypothesis hbase', ?_⟩
    exact ⟨e⟩

theorem finiteProjective_baseChange_iff
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    : FiniteProjective A M ↔ FiniteProjective B (B ⊗[A] M) := by
  constructor
  · intro hM
    have : Module.Finite A M := hM.1
    have : Module.Projective A M := hM.2
    exact ⟨inferInstance, inferInstance⟩
  · intro hB
    exact finiteProjective_of_faithfullyFlat_baseChange_of_hypothesis hB

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
