import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06

noncomputable section

open TensorProduct

universe u v

/-! ## 6.4 Rank and related invariants -/

theorem fiberRank_isLocallyConstant
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (fiberRank M) := by
  simpa [fiberRank] using
    (Module.isLocallyConstant_rankAtStalk (R := R) (M := M))

theorem prime_lies_over_of_faithfullyFlat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (p : PrimeSpectrum A) :
    ∃ q : PrimeSpectrum B, q.comap (algebraMap A B) = p := by
  exact (PrimeSpectrum.comap_surjective_of_faithfullyFlat p)

theorem fiberRank_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] (q : PrimeSpectrum B) :
    fiberRank (B ⊗[A] M) q = fiberRank M (q.comap (algebraMap A B)) := by
  simpa [fiberRank] using
    (Module.rankAtStalk_baseChange (R := A) (M := M) q)

theorem hasConstantRank_baseChange_iff
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (r : ℕ) :
    HasConstantRank (B ⊗[A] M) r ↔ HasConstantRank M r := by
  sorry

theorem hasRankIn_baseChange_iff
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (ranks : Set ℕ) :
    HasRankIn (B ⊗[A] M) ranks ↔ HasRankIn M ranks := by
  sorry

/-- The fiberwise rank locus of a module. -/
def fiberRankLocus
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (ranks : Set ℕ) : Set (PrimeSpectrum R) :=
  {p | fiberRank M p ∈ ranks}

theorem mem_fiberRankLocus_iff
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (ranks : Set ℕ) (p : PrimeSpectrum R) :
    p ∈ fiberRankLocus M ranks ↔ fiberRank M p ∈ ranks :=
  Iff.rfl

theorem fiberRankLocus_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] (ranks : Set ℕ) :
    fiberRankLocus (B ⊗[A] M) ranks =
      (PrimeSpectrum.comap (algebraMap A B)) ⁻¹' fiberRankLocus M ranks := by
  sorry

/-- Faithfully flat descent of rank loci. -/
theorem fiberRankLocus_descends_of_faithfullyFlat
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (ranks : Set ℕ) :
    (∀ q : PrimeSpectrum B, q ∈ fiberRankLocus (B ⊗[A] M) ranks) ↔
      ∀ p : PrimeSpectrum A, p ∈ fiberRankLocus M ranks := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib snapshot has no Fitting-ideal API.  This structure
records exactly the base-change interface needed by the textbook's Fitting-locus discussion. -/
structure FittingIdealBaseChangeSystem
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] where
  ideal : ∀ {B : Type*} [CommRing B] [Algebra A B], ℕ → Ideal B
  ideal_baseChange :
    ∀ {B : Type*} [CommRing B] [Algebra A B] (n : ℕ),
      ideal (B := B) n = (ideal (B := A) n).map (algebraMap A B)

theorem fittingIdeal_baseChange
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M]
    (F : FittingIdealBaseChangeSystem A M)
    {B : Type*} [CommRing B] [Algebra A B] (n : ℕ) :
    F.ideal (B := B) n = (F.ideal (B := A) n).map (algebraMap A B) := by
  exact F.ideal_baseChange n

theorem ideal_comap_map_eq_self_of_faithfullyFlat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The determinant criterion is stated as invertibility of the induced exterior-power map. -/
def IsDeterminantInvertible
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (r : ℕ) (f : M →ₗ[R] N) : Prop :=
  Function.Bijective (determinantMap r f)

theorem determinantMap_id
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (r : ℕ) :
    determinantMap r (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  sorry

theorem determinantMap_comp
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (r : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    determinantMap r (g ∘ₗ f) = determinantMap r g ∘ₗ determinantMap r f := by
  sorry

theorem finiteProjective_determinantMap_bijective_iff
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.FinitePresentation R M]
    [Module.FinitePresentation R N] [Module.Flat R M] [Module.Flat R N]
    (r : ℕ) (f : M →ₗ[R] N)
    (hM : HasConstantRank M r) (hN : HasConstantRank N r) :
    Function.Bijective f ↔ IsDeterminantInvertible r f := by
  sorry

def DeterminantBaseChangeWitness
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] (r : ℕ) : Prop :=
  Nonempty
    (B ⊗[A] determinantModule A M r ≃ₗ[B]
      determinantModule B (B ⊗[A] M) r)

theorem determinantModule_commutes_with_baseChange
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.Finite A M] [Module.Projective A M]
    (r : ℕ) :
    DeterminantBaseChangeWitness (A := A) (B := B) (M := M) r := by
  sorry

theorem determinantMap_commutes_with_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Algebra A B] [Module A M] [Module A N]
    [Module.Finite A M] [Module.Projective A M]
    [Module.Finite A N] [Module.Projective A N]
    (r : ℕ) (f : M →ₗ[A] N) :
    ∃ (eM : B ⊗[A] determinantModule A M r ≃ₗ[B]
        determinantModule B (B ⊗[A] M) r)
      (eN : B ⊗[A] determinantModule A N r ≃ₗ[B]
        determinantModule B (B ⊗[A] N) r),
      determinantMap r (f.baseChange B) ∘ₗ eM.toLinearMap =
        eN.toLinearMap ∘ₗ (determinantMap r f).baseChange B := by
  sorry

theorem determinant_invertible_detected_after_faithfullyFlat_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Algebra A B] [Module A M] [Module A N]
    [Module.FaithfullyFlat A B] [Module.FinitePresentation A M]
    [Module.FinitePresentation A N] [Module.Flat A M] [Module.Flat A N]
    (r : ℕ) (f : M →ₗ[A] N) :
    IsDeterminantInvertible r f ↔
      IsDeterminantInvertible r (f.baseChange B) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter06
