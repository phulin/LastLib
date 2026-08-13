import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section01SeparatingBranchesByCompletion

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

noncomputable section

open Function Ideal IsLocalRing Polynomial
open Filter Topology
open scoped BigOperators TensorProduct WithZero Polynomial

universe u

/-! # Chapter 12: Completion and finite extensions

This file is a statement-generation pass for §§12.1--12.8 of Book 1.  The
declarations deliberately record the interfaces and relationships used in the
chapter; proofs are postponed.
-/

/-! # Book 1, Chapter 12, Section 12.3: Completion of a Localization
-/

/-! ## 12.3. Completion of a localization -/

/-- The completed localization of a Dedekind-domain prime. -/
abbrev completedLocalization
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] : Type u :=
  AdicCompletion
    (Ideal.map (algebraMap R (Localization.AtPrime p)) p)
    (Localization.AtPrime p)

/-- The fraction field of the completed localization at `p`. -/
abbrev localizationFractionField
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] : Type u :=
  FractionRing (completedLocalization R p)

/-- The two completed local-global dictionaries for a finite extension. -/
theorem dedekind_local_completion_product
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
    [Algebra (FractionRing R) (FractionRing S)]
    [Algebra R (FractionRing S)]
    [IsScalarTower R S (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    {g : ℕ} (p : Ideal R) [p.IsPrime] (P : Fin g → Ideal S)
    (hp : p ≠ ⊥)
    (hfinite : Module.Finite R S) (hfree : Module.Free R S)
    (hlies : ∀ i, (P i).LiesOver p)
    [hprime : ∀ i, (P i).IsPrime]
    (hP_exhaustive :
      ∀ (q : Ideal S), q.IsPrime → q.LiesOver p → ∃ i, P i = q)
    (hP_distinct : Function.Injective P) :
    Nonempty
      (S ⊗[R] completedLocalization R p ≃+*
        (∀ i, branchCompletion S (P i))) := by
  sorry

/-- Fraction-field form of the localization/completion dictionary. -/
theorem dedekind_local_fraction_field_product
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
    {g : ℕ} (p : Ideal R) [p.IsPrime] (P : Fin g → Ideal S)
    (hp : p ≠ ⊥)
    [Algebra (FractionRing R) (FractionRing S)]
    [Algebra R (FractionRing S)]
    [IsScalarTower R S (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    [Algebra (FractionRing R) (localizationFractionField R p)]
    (hfinite : Module.Finite R S) (hfree : Module.Free R S)
    (hlies : ∀ i, (P i).LiesOver p)
    [hprime : ∀ i, (P i).IsPrime]
    (hP_exhaustive :
      ∀ (q : Ideal S), q.IsPrime → q.LiesOver p → ∃ i, P i = q)
    (hP_distinct : Function.Injective P) :
    Nonempty
      (FractionRing S ⊗[FractionRing R] localizationFractionField R p ≃+*
        (∀ i, branchFractionField S (P i))) := by
  sorry

/-- Tensoring with a completed base records all primes above the chosen base prime. -/
theorem tensor_product_remembers_all_local_choices
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {g : ℕ} (p : Ideal R) [p.IsPrime] (P : Fin g → Ideal S)
    [hprime : ∀ i, (P i).IsPrime]
    (hproduct : Nonempty
      (S ⊗[R] completedLocalization R p ≃+*
        (∀ i, branchCompletion S (P i)))) :
    ∃ proj : ∀ i, (S ⊗[R] completedLocalization R p) →+* branchCompletion S (P i),
      ∀ i, Function.Surjective (proj i) := by
  let e := Classical.choice hproduct
  refine ⟨fun i => (Pi.evalRingHom (fun i => branchCompletion S (P i)) i).comp e.toRingHom, ?_⟩
  intro i
  exact (Pi.evalRingHom (fun i => branchCompletion S (P i)) i).surjective.comp e.surjective


end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
