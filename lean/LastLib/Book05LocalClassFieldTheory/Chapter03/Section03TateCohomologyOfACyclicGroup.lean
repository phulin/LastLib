import LastLib.Book05LocalClassFieldTheory.Chapter03.Section02Hilbert90
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open CategoryTheory
open scoped BigOperators

/-! ## 3.3. Tate cohomology of a cyclic group -/

/-- Tate cohomology in an arbitrary integer degree, using Mathlib's canonical complex. -/
abbrev chapter03TateCohomology
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (r : ℤ) : ModuleCat ℤ :=
  tateCohomology A r

abbrev chapter03TateH0
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) : ModuleCat ℤ :=
  chapter03TateCohomology A 0

abbrev chapter03TateHMinusOne
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) : ModuleCat ℤ :=
  chapter03TateCohomology A (-1)

/-- The alternating norm and difference maps used by the cyclic model. -/
abbrev chapter03TateNormMap
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) :=
  letI : Module ℤ A.V := A.hV2
  A.norm.hom.toLinearMap

abbrev chapter03TateDifferenceMap
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :=
  letI : Module ℤ A.V := A.hV2
  (A.applyAsHom σ - 𝟙 A).hom.toLinearMap

theorem chapter03_tate_norm_range_le_difference_kernel
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    LinearMap.range (chapter03TateNormMap A) ≤
      LinearMap.ker (chapter03TateDifferenceMap A σ) := by
  sorry

theorem chapter03_tate_difference_range_le_norm_kernel
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    letI : Module ℤ A.V := A.hV2
    LinearMap.range (chapter03TateDifferenceMap A σ) ≤
      LinearMap.ker (chapter03TateNormMap A) := by
  sorry

/-- The concrete quotient model for `A^G / N_G A` supplied by the short-complex API. -/
abbrev chapter03TateH0Concrete
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) : ModuleCat ℤ :=
  (Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).homology

/-- The concrete quotient model for `ker(N_G) / D A`. -/
abbrev chapter03TateHMinusOneConcrete
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) : ModuleCat ℤ :=
  (Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).homology

/-- The quotient implementation of `A^G/N_GA`, with its kernel/range data exposed. -/
noncomputable def chapter03_tate_h0_concrete_quotient_iso
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    chapter03TateH0Concrete A σ ≅
      (Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).moduleCatLeftHomologyData.H :=
  (Rep.FiniteCyclicGroup.normHomCompSub (k := ℤ) (G := G) A σ).moduleCatHomologyIso

/-- The quotient implementation of `ker(N_G)/D A`, with its kernel/range data exposed. -/
noncomputable def chapter03_tate_hminusone_concrete_quotient_iso
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G) :
    chapter03TateHMinusOneConcrete A σ ≅
      (Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).moduleCatLeftHomologyData.H :=
  (Rep.FiniteCyclicGroup.subCompNormHom (k := ℤ) (G := G) A σ).moduleCatHomologyIso

/-- The canonical two-periodicity isomorphism for cyclic Tate cohomology. -/
noncomputable def chapter03_tate_periodicity
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) (r : ℤ) :
    chapter03TateCohomology A (r + 2) ≅ chapter03TateCohomology A r := by
  sorry

noncomputable def chapter03_tate_h0_cyclic_formula
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    chapter03TateH0 A ≅ chapter03TateH0Concrete A σ := by
  sorry

noncomputable def chapter03_tate_hminusone_cyclic_formula
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (σ : G)
    (hσ : ∀ τ : G, τ ∈ Subgroup.zpowers σ) :
    chapter03TateHMinusOne A ≅ chapter03TateHMinusOneConcrete A σ := by
  sorry

/-- The multiplicative Galois module `Lˣ` used in the local-field specialization. -/
abbrev chapter03MultiplicativeGaloisModule
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  Rep.ofAlgebraAutOnUnits K L

attribute [local instance] IsCyclic.commGroup in
noncomputable def chapter03_tate_h0_multiplicative_norm_quotient
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] [Fintype Gal(L/K)]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    chapter03TateH0 (chapter03MultiplicativeGaloisModule K L) ≅
      ModuleCat.of ℤ (Additive (chapter03NormQuotient K L)) := by
  sorry

attribute [local instance] IsCyclic.commGroup in
theorem chapter03_tate_hminusone_multiplicative_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] [Fintype Gal(L/K)]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    Subsingleton (chapter03TateHMinusOne (chapter03MultiplicativeGaloisModule K L)) := by
  sorry

/-- Hilbert 90 written as the vanishing of the first ordinary cohomology group. -/
theorem chapter03_group_cohomology_h1_multiplicative_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Subsingleton (groupCohomology.H1 (chapter03MultiplicativeGaloisModule K L)) := by
  exact chapter03_hilbert90_h1_subsingleton K L

attribute [local instance] IsCyclic.commGroup in
/-- Periodicity identifies the second ordinary group cohomology with the norm quotient. -/
noncomputable def chapter03_group_cohomology_h2_multiplicative_norm_quotient
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] [Fintype Gal(L/K)]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    groupCohomology (chapter03MultiplicativeGaloisModule K L) 2 ≅
      ModuleCat.of ℤ (Additive (chapter03NormQuotient K L)) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
