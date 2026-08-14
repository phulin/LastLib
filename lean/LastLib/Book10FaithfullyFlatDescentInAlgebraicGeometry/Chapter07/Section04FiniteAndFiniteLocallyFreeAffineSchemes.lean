import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Section03AffineDescent

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u

/-- Affine algebra formulations of the three finiteness notions in §7.4. -/
def Chapter07FiniteAffineAlgebra (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] : Prop :=
  Module.Finite A R

def Chapter07FinitePresentationAffineAlgebra (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] : Prop :=
  Algebra.FinitePresentation A R

def Chapter07FiniteLocallyFreeAffineAlgebra (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] : Prop :=
  Chapter07FiniteLocallyFreeModule A R

theorem chapter07_finite_affine_algebra_iff (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] :
    Chapter07FiniteAffineAlgebra A R ↔ Module.Finite A R := by
  rfl

theorem chapter07_finite_presentation_affine_algebra_iff (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] :
    Chapter07FinitePresentationAffineAlgebra A R ↔ Algebra.FinitePresentation A R := by
  rfl

theorem chapter07_finite_locally_free_affine_algebra_iff (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] :
    Chapter07FiniteLocallyFreeAffineAlgebra A R ↔
      Module.Finite A R ∧ Module.Flat A R := by
  rfl

/-- The rank of the fiber of a finite module at a prime of the base. -/
def chapter07FiberRank (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M]
    (p : PrimeSpectrum A) : ℕ :=
  Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M)

theorem chapter07_fiber_rank_eq_finrank (A M : Type u) [CommRing A] [AddCommGroup M]
    [Module A M] (p : PrimeSpectrum A) :
    chapter07FiberRank A M p =
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) := by
  rfl

def Chapter07FiniteLocallyFreeModuleOfRank
    (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M] (r : ℕ) : Prop :=
  Chapter07FiniteLocallyFreeModule A M ∧
    ∀ p : PrimeSpectrum A, chapter07FiberRank A M p = r

def Chapter07FiniteLocallyFreeAffineAlgebraOfRank
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] (r : ℕ) : Prop :=
  Chapter07FiniteLocallyFreeModuleOfRank A R r

theorem chapter07_constant_fiber_rank_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (r : ℕ)
    (h : ∀ q : PrimeSpectrum B, chapter07FiberRank B (B ⊗[A] M) q = r) :
    ∀ p : PrimeSpectrum A, chapter07FiberRank A M p = r := by
  sorry

theorem chapter07_fiber_rank_is_preserved_under_residue_field_base_change
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap A B) q = p) :
    chapter07FiberRank A M p = chapter07FiberRank B (B ⊗[A] M) q := by
  sorry

/- The source's “rank r” formulation is the conjunction of finite-flatness and the fiber-rank
condition above. -/
theorem chapter07_finite_locally_free_rank_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (r : ℕ)
    (hfinite : Module.Finite B (B ⊗[A] M))
    (hflat : Module.Flat B (B ⊗[A] M))
    (hrank : ∀ q : PrimeSpectrum B, chapter07FiberRank B (B ⊗[A] M) q = r) :
    Chapter07FiniteLocallyFreeModuleOfRank A M r := by
  sorry

theorem chapter07_finite_module_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hfinite : Module.Finite B (B ⊗[A] M)) : Module.Finite A M := by
  sorry

theorem chapter07_finite_type_algebra_descends
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B]
    (hfinite : Algebra.FiniteType B (B ⊗[A] R)) : Algebra.FiniteType A R := by
  sorry

theorem chapter07_finite_presentation_algebra_descends
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B]
    (hfinite : Algebra.FinitePresentation B (B ⊗[A] R)) :
    Algebra.FinitePresentation A R := by
  sorry

theorem chapter07_flat_module_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hflat : Module.Flat B (B ⊗[A] M)) : Module.Flat A M := by
  sorry

theorem chapter07_finite_flat_module_descends
    {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra A B] [Module A M] [Module.FaithfullyFlat A B]
    (hfinite : Module.Finite B (B ⊗[A] M))
    (hflat : Module.Flat B (B ⊗[A] M)) :
    Chapter07FiniteLocallyFreeModule A M := by
  exact ⟨chapter07_finite_module_descends hfinite, chapter07_flat_module_descends hflat⟩

theorem chapter07_finite_flat_module_is_free_over_local_ring
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] [IsLocalRing R]
    [Module.Finite R M] [Module.Flat R M] : Module.Free R M := by
  exact Module.free_of_flat_of_isLocalRing

/-- Scheme-level names for the affine finiteness profiles. -/
def Chapter07FiniteAffineMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsAffineHom f ∧ IsFinite f

def Chapter07FinitePresentationAffineMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsAffineHom f ∧ LocallyOfFinitePresentation f

def Chapter07FiniteLocallyFreeAffineMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsAffineHom f ∧ IsFinite f ∧ Flat f

def Chapter07FiniteLocallyFreeAffineMorphismOfRank
    {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) : Prop :=
  Chapter07FiniteLocallyFreeAffineMorphism f ∧ ∀ s : S, Scheme.Hom.finrank f s = r

theorem chapter07_finite_flat_is_finite_locally_free
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hfinite : IsFinite f) (hflat : Flat f) :
    Chapter07FiniteLocallyFreeAffineMorphism f := by
  sorry

theorem chapter07_finite_affine_descent
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R : Chapter07AffineDescentResult D)
    (hfinite : IsFinite D.map) : IsFinite R.map := by
  sorry

theorem chapter07_finite_presentation_affine_descent
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R : Chapter07AffineDescentResult D)
    (hfinitePresentation : LocallyOfFinitePresentation D.map) :
    LocallyOfFinitePresentation R.map := by
  sorry

theorem chapter07_finite_flat_affine_descent
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R : Chapter07AffineDescentResult D)
    (hfinite : IsFinite D.map) (hflat : Flat D.map) :
    Chapter07FiniteLocallyFreeAffineMorphism R.map := by
  sorry

theorem chapter07_finite_locally_free_affine_rank_descends
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R : Chapter07AffineDescentResult D)
    (r : ℕ) (hfinite : IsFinite D.map) (hflat : Flat D.map)
    (hrank : ∀ t : T, Scheme.Hom.finrank D.map t = r) :
    Chapter07FiniteLocallyFreeAffineMorphismOfRank R.map r := by
  sorry

theorem chapter07_surjective_base_change_algebraMap_descends
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B]
    (h : Function.Surjective (algebraMap B (B ⊗[A] R))) :
    Function.Surjective (algebraMap A R) := by
  sorry

theorem chapter07_surjective_base_change_algebraMap_iff
    {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Module.FaithfullyFlat A B] :
    Function.Surjective (algebraMap A R) ↔
      Function.Surjective (algebraMap B (B ⊗[A] R)) := by
  sorry

theorem chapter07_spec_map_finite_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsFinite (Scheme.Spec.map f) ↔ f.hom.Finite := by
  sorry

theorem chapter07_spec_map_finite_presentation_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    LocallyOfFinitePresentation (Scheme.Spec.map f) ↔ f.hom.FinitePresentation := by
  sorry

theorem chapter07_spec_map_flat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Flat (Scheme.Spec.map f) ↔ f.hom.Flat := by
  sorry

theorem chapter07_closed_immersion_of_surjective_affine_map
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (h : Function.Surjective (algebraMap A B)) :
    IsClosedImmersion
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  sorry

theorem chapter07_spec_map_closed_immersion_iff_surjective
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsClosedImmersion (Scheme.Spec.map f) ↔ Function.Surjective f.hom := by
  sorry

theorem chapter07_closed_immersion_descends
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R : Chapter07AffineDescentResult D)
    (hclosed : IsClosedImmersion D.map) : IsClosedImmersion R.map := by
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
