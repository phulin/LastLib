import Mathlib.Algebra.Module.ZMod
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-!
### 5.3. The class-formation isomorphism
-/

structure Chapter05TateNakayamaHypotheses
    (G : Type) [Group G] [Fintype G] (C : Rep ℤ G)
    (u : chapter05GroupCohomology G C 2) where
  hH1 : ∀ H : Subgroup G,
    IsZero (chapter05GroupCohomology H (Rep.res H.subtype C) 1)
  hH2 : ∀ H : Subgroup G,
    Chapter05CyclicGroupOfOrder
      (chapter05GroupCohomology H (Rep.res H.subtype C) 2) (Nat.card H)
  hres_generates : ∀ H : Subgroup G,
    chapter05Generates
      (chapter05GroupCohomology H (Rep.res H.subtype C) 2)
      (chapter05RestrictTwoClass H u)

/- LOCAL_DEPENDENCY_GUESS: the local invariant, Hilbert--90, and subgroup
restriction results are the inputs supplied by the preceding local-field
chapters.  This record contains only those hypotheses, not the desired cap
product isomorphisms. -/
structure Chapter05LocalBrauerInvariantSystem
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (u : chapter05GroupCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 2) where
  invariant : ∀ H : Subgroup (Gal(L / K)),
    (chapter05GroupCohomology H
      (Rep.res H.subtype (chapter05CoefficientRep K L)) 2) →+
      chapter05RationalResidue
  h2_cyclic : ∀ H : Subgroup (Gal(L / K)),
    Chapter05CyclicGroupOfOrder
      (chapter05GroupCohomology H
        (Rep.res H.subtype (chapter05CoefficientRep K L)) 2) (Nat.card H)
  invariant_injective : ∀ H : Subgroup (Gal(L / K)),
    Function.Injective (invariant H)
  invariant_range : ∀ H : Subgroup (Gal(L / K)),
    (invariant H).range =
      AddSubgroup.zmultiples (chapter05RationalResidueOneOver (Nat.card H))
  restriction_formula : ∀ H : Subgroup (Gal(L / K)),
    invariant H (chapter05RestrictTwoClass H u) =
      chapter05RationalResidueOneOver (Nat.card H)

/- The exact sequence and the typed connecting family are kept together here.
   The connecting family is required to be the canonical composite of the two
   Tate connecting morphisms attached to `extension`; the comparison with the
   chosen cap product is recorded below. -/
structure Chapter05TwoExtensionRepresentative
    (G : Type) [Group G] [Fintype G] (C : Rep ℤ G)
    (u : chapter05GroupCohomology G C 2)
    (P : Chapter05CapProduct G C u) where
  extension : Chapter05TwoExtension G C
  connecting : ∀ (H : Subgroup G) (r : ℤ),
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) r ⟶
      chapter05TateCohomology H (Rep.res H.subtype C) (r + 2)
  connecting_is_canonical : ∀ (H : Subgroup G) (r : ℤ),
    connecting H r = chapter05TwoExtensionConnecting extension H r
  connecting_eq_cap : ∀ (H : Subgroup G) (r : ℤ),
    connecting H r = P.cap H r

/- LOCAL_DEPENDENCY_GUESS: this is the minimal book-facing package assembled
from the preceding local Brauer, Hilbert--90, and degree-zero norm results.
Its fields are hypotheses for the induction theorem, not an encoded
reciprocity equivalence. -/
structure Chapter05LocalClassFormationData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] where
  fundamentalClass : Chapter05FundamentalTwoClass
    (Gal(L / K)) (chapter05CoefficientRep K L)
  localInvariant : Chapter05LocalBrauerInvariantSystem K L fundamentalClass.value
  capProduct : Chapter05CapProduct (Gal(L / K))
    (chapter05CoefficientRep K L) fundamentalClass.value
  twoExtensionRepresentative :
    Chapter05TwoExtensionRepresentative (Gal(L / K))
      (chapter05CoefficientRep K L) fundamentalClass.value capProduct
  topRestriction : Chapter05TopRestrictionTateIso (Gal(L / K))
    (chapter05CoefficientRep K L)
  topRestrictionTrivial :
    Chapter05TopRestrictionTrivialTateIso (Gal(L / K))
  nakayama : Chapter05TateNakayamaHypotheses (Gal(L / K))
    (chapter05CoefficientRep K L) fundamentalClass.value
  degreeZeroNorm :
    chapter05TateCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 0 ≃+
      Additive (chapter05NormQuotient K L)

noncomputable def chapter05LocalInvariantRangeEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    {u : chapter05GroupCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 2}
    (I : Chapter05LocalBrauerInvariantSystem K L u)
    (H : Subgroup (Gal(L / K))) :
    (chapter05GroupCohomology H
      (Rep.res H.subtype (chapter05CoefficientRep K L)) 2) ≃+
      (I.invariant H).range := by
  sorry

theorem chapter05_tate_nakayama_induction
    {G : Type} [Group G] [Fintype G] {C : Rep ℤ G}
    {u : chapter05GroupCohomology G C 2}
    (P : Chapter05CapProduct G C u)
    (T : Chapter05TwoExtensionRepresentative G C u P)
    (HYP : Chapter05TateNakayamaHypotheses G C u) :
    ∀ (H : Subgroup G) (r : ℤ), IsIso (P.cap H r) := by
  sorry

theorem chapter05_lemma_5_2_tate_nakayama
    {G : Type} [Group G] [Fintype G] {C : Rep ℤ G}
    {u : chapter05GroupCohomology G C 2}
    (P : Chapter05CapProduct G C u)
    (T : Chapter05TwoExtensionRepresentative G C u P)
    (HYP : Chapter05TateNakayamaHypotheses G C u) :
    ∀ (H : Subgroup G) (r : ℤ), IsIso (P.cap H r) := by
  exact chapter05_tate_nakayama_induction P T HYP

theorem chapter05_class_formation_isomorphism
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    ∀ (H : Subgroup (Gal(L / K))) (r : ℤ),
      IsIso (D.capProduct.cap H r) := by
  exact chapter05_tate_nakayama_induction D.capProduct
    D.twoExtensionRepresentative D.nakayama

theorem chapter05_theorem_5_1_fundamental_class_isomorphism
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    ∀ (H : Subgroup (Gal(L / K))) (r : ℤ),
      IsIso (D.capProduct.cap H r) := by
  exact chapter05_class_formation_isomorphism D

theorem chapter05_galois_group_card_eq_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] :
    Nat.card (Gal(L / K)) = Module.finrank K L := by
  sorry

def chapter05SubgroupFixedField
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (Gal(L / K))) : IntermediateField K L :=
  IntermediateField.fixedField H

def chapter05RestrictionInvariantFraction
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (Gal(L / K))) : ℚ :=
  (Module.finrank K (chapter05SubgroupFixedField K L H) : ℚ) /
    (Module.finrank K L : ℚ)

theorem chapter05_restriction_invariant_fraction
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] (H : Subgroup (Gal(L / K))) :
    chapter05RestrictionInvariantFraction K L H =
      (1 : ℚ) / (Nat.card H : ℚ) := by
  sorry

theorem chapter05_restriction_invariant_fraction_mod_integer
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] (H : Subgroup (Gal(L / K))) :
    chapter05RationalResidueMk (chapter05RestrictionInvariantFraction K L H) =
      chapter05RationalResidueOneOver (Nat.card H) := by
  sorry

theorem chapter05_local_invariant_restriction_formula
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    {u : chapter05GroupCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 2}
    (I : Chapter05LocalBrauerInvariantSystem K L u)
    (H : Subgroup (Gal(L / K))) :
    I.invariant H (chapter05RestrictTwoClass H u) =
      chapter05RationalResidueOneOver (Nat.card H) := by
  exact I.restriction_formula H

theorem chapter05_class_formation_top_isomorphism
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) (r : ℤ) :
    IsIso (D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) r) := by
  sorry

theorem chapter05_regular_representation_tate_zero
    (G : Type) [Group G] [Fintype G] (H : Subgroup G) (r : ℤ) :
    IsZero (chapter05TateCohomology H
      (Rep.res H.subtype (Rep.ofMulAction ℤ G (Fin 1 → G))) r) := by
  sorry

theorem chapter05_trivial_tate_minus_one_zero
    (H : Type) [Group H] [Fintype H] :
    IsZero (chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-1)) := by
  sorry

theorem chapter05_degree_zero_connecting_iso
    {G : Type} [Group G] [Fintype G] {C : Rep ℤ G}
    (H : Subgroup G) (u : chapter05GroupCohomology G C 2)
    (hcyclic : Chapter05CyclicGroupOfOrder
      (chapter05GroupCohomology H (Rep.res H.subtype C) 2) (Nat.card H))
    (hgen : chapter05Generates
      (chapter05GroupCohomology H (Rep.res H.subtype C) 2)
      (chapter05RestrictTwoClass H u)) :
    ∃ e : ZMod (Nat.card H) ≃+
        chapter05GroupCohomology H (Rep.res H.subtype C) 2,
      e 1 = chapter05RestrictTwoClass H u := by
  sorry

theorem chapter05_middle_two_extension_vanishing
    {G : Type} [Group G] [Fintype G] {C : Rep ℤ G}
    {u : chapter05GroupCohomology G C 2}
    (P : Chapter05CapProduct G C u)
    (T : Chapter05TwoExtensionRepresentative G C u P)
    (HYP : Chapter05TateNakayamaHypotheses G C u)
    (H : Subgroup G) :
    IsZero (chapter05TateCohomology H (Rep.res H.subtype T.extension.middle) 0) ∧
      IsZero (chapter05TateCohomology H (Rep.res H.subtype T.extension.middle) 1) := by
  sorry

theorem chapter05_cohomological_triviality_criterion
    {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (h0 : ∀ H : Subgroup G,
      IsZero (chapter05TateCohomology H (Rep.res H.subtype A) 0))
    (h1 : ∀ H : Subgroup G,
      IsZero (chapter05TateCohomology H (Rep.res H.subtype A) 1)) :
    ∀ (H : Subgroup G) (r : ℤ),
      IsZero (chapter05TateCohomology H (Rep.res H.subtype A) r) := by
  sorry

theorem chapter05_two_extension_connecting_isomorphism
    {G : Type} [Group G] [Fintype G] {C : Rep ℤ G}
    {u : chapter05GroupCohomology G C 2}
    (P : Chapter05CapProduct G C u)
    (T : Chapter05TwoExtensionRepresentative G C u P)
    (h0 : ∀ H : Subgroup G,
      IsZero (chapter05TateCohomology H (Rep.res H.subtype T.extension.middle) 0))
    (h1 : ∀ H : Subgroup G,
      IsZero (chapter05TateCohomology H (Rep.res H.subtype T.extension.middle) 1)) :
    ∀ (H : Subgroup G) (r : ℤ), IsIso (T.connecting H r) := by
  sorry

theorem chapter05_local_hilbert90
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] (H : Subgroup (Gal(L / K))) :
    IsZero (chapter05GroupCohomology H
      (Rep.res H.subtype (chapter05CoefficientRep K L)) 1) := by
  sorry

theorem chapter05_local_H2_cyclic
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    {u : chapter05GroupCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 2}
    (I : Chapter05LocalBrauerInvariantSystem K L u)
    (H : Subgroup (Gal(L / K))) :
    Chapter05CyclicGroupOfOrder
      (chapter05GroupCohomology H
        (Rep.res H.subtype (chapter05CoefficientRep K L)) 2) (Nat.card H) := by
  exact I.h2_cyclic H

theorem chapter05_local_restriction_generates
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    {u : chapter05GroupCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 2}
    (I : Chapter05LocalBrauerInvariantSystem K L u)
    (H : Subgroup (Gal(L / K))) :
    chapter05Generates
      (chapter05GroupCohomology H
        (Rep.res H.subtype (chapter05CoefficientRep K L)) 2)
      (chapter05RestrictTwoClass H u) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
