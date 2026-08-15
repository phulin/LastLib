import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
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
  /- The extension must represent the chosen class `u`, not merely have a
     connecting family which has been declared equal to the cap product.  The
     two additive equivalences below are the degree-zero Tate/ordinary
     cohomology bridges; the last field is the normalization on the
     distinguished class. -/
  degree_zero_source : ∀ (H : Subgroup G),
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) 0 ≃+
      ZMod (Nat.card H)
  degree_zero_target : ∀ (H : Subgroup G),
    chapter05TateCohomology H (Rep.res H.subtype C) 2 ≃+
      chapter05GroupCohomology H (Rep.res H.subtype C) 2
  degree_zero_connecting : ∀ (H : Subgroup G),
    degree_zero_target H
        ((connecting H 0) ((degree_zero_source H).symm 1)) =
      chapter05RestrictTwoClass H u

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
  exact AddMonoidHom.ofInjective (I.invariant_injective H)

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
  exact IsGalois.card_aut_eq_finrank K L

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
  unfold chapter05RestrictionInvariantFraction
  have hdim := Module.finrank_mul_finrank K
    (chapter05SubgroupFixedField K L H) L
  unfold chapter05SubgroupFixedField at hdim
  rw [IntermediateField.finrank_fixedField_eq_card H] at hdim
  have hcard : (Nat.card H : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card H ≠ 0)
  have hL : (Module.finrank K L : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hdimq :
      (Module.finrank K (chapter05SubgroupFixedField K L H) : ℚ) *
          (Nat.card H : ℚ) = (Module.finrank K L : ℚ) := by
    exact_mod_cast hdim
  apply (div_eq_div_iff hL hcard).2
  simpa using hdimq

theorem chapter05_restriction_invariant_fraction_mod_integer
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] (H : Subgroup (Gal(L / K))) :
    chapter05RationalResidueMk (chapter05RestrictionInvariantFraction K L H) =
      chapter05RationalResidueOneOver (Nat.card H) := by
  simpa [chapter05RationalResidueOneOver] using
    congrArg chapter05RationalResidueMk
      (chapter05_restriction_invariant_fraction K L H)

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
  exact chapter05_class_formation_isomorphism D ⊤ r

theorem chapter05_regular_representation_tate_zero
    (G : Type) [Group G] [Fintype G] (H : Subgroup G) (r : ℤ) :
    IsZero (chapter05TateCohomology H
      (Rep.res H.subtype (Rep.ofMulAction ℤ G (Fin 1 → G))) r) := by
  sorry

theorem chapter05_trivial_tate_minus_one_zero
    (H : Type) [Group H] [Fintype H] :
    IsZero (chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-1)) := by
  change IsZero ((tateComplex (Rep.trivial ℤ H ℤ)).homology (-1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.exactAt_iff'
    (K := tateComplex (Rep.trivial ℤ H ℤ))
    (i := (-2 : ℤ)) (j := (-1 : ℤ)) (k := (0 : ℤ))
    (by norm_num) (by norm_num)).2
  apply (ShortComplex.exact_iff_mono _ ?_).2
  · change Mono (Rep.trivial ℤ H ℤ).tateNorm
    rw [ModuleCat.mono_iff_injective]
    rw [Rep.tateNorm_eq]
    intro x y hxy
    apply Finsupp.ext
    intro i
    have hi : i = (default : Fin 0 → H) := Subsingleton.elim _ _
    subst i
    have hx : x = Finsupp.single (default : Fin 0 → H) (x default) := by
      apply Finsupp.ext
      intro j
      have hj : j = (default : Fin 0 → H) := Subsingleton.elim _ _
      subst j
      simp
    have hy : y = Finsupp.single (default : Fin 0 → H) (y default) := by
      apply Finsupp.ext
      intro j
      have hj : j = (default : Fin 0 → H) := Subsingleton.elim _ _
      subst j
      simp
    have hxy' := congrFun hxy (default : Fin 0 → H)
    rw [hx, hy] at hxy'
    apply nsmul_right_injective (n := Fintype.card H)
    · simp
    · simpa [Finsupp.lsum_single, LinearMap.pi_apply, Representation.norm,
        Finset.sum_const] using hxy'
  · change (groupHomology.inhomogeneousChains (Rep.trivial ℤ H ℤ)).d 1 0 = 0
    apply (cancel_mono (groupHomology.chainsIso₀ (Rep.trivial ℤ H ℤ)).hom).1
    rw [← groupHomology.comp_d₁₀_eq (Rep.trivial ℤ H ℤ),
      groupHomology.d₁₀_eq_zero_of_isTrivial]
    simp

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
  have hg : ∀ y : chapter05GroupCohomology H (Rep.res H.subtype C) 2,
      y ∈ AddSubgroup.zmultiples (chapter05RestrictTwoClass H u) := by
    intro y
    rw [AddSubgroup.mem_zmultiples_iff]
    have hy : y ∈ Submodule.span ℤ {chapter05RestrictTwoClass H u} := by
      rw [hgen]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨k, ?_⟩
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
      (chapter05GroupCohomology H (Rep.res H.subtype C) 2)) k
      (chapter05RestrictTwoClass H u)]
    exact hk
  refine ⟨zmodAddEquivOfGenerator hg hcyclic.card_eq, ?_⟩
  exact zmodAddEquivOfGenerator_apply_one hg hcyclic.card_eq

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
  let e : H ≃* Gal(L / IntermediateField.fixedField H) :=
    IntermediateField.subgroupEquivAlgEquiv H
  let e' : (Rep.res H.subtype (chapter05CoefficientRep K L)).V ≃ₗ[ℤ]
      (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) L).V :=
    LinearEquiv.refl ℤ _
  have he : ∀ h : H,
      e'.toLinearMap ∘ₗ (Rep.res H.subtype (chapter05CoefficientRep K L)).ρ h =
        (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) L).ρ (e h) ∘ₗ
          e'.toLinearMap := by
    intro h
    ext x
    rfl
  let E : chapter05GroupCohomology H
      (Rep.res H.subtype (chapter05CoefficientRep K L)) 1 ≅
      chapter05GroupCohomology (Gal(L / IntermediateField.fixedField H))
        (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) L) 1 :=
    groupCohomology.mapIso e e' he 1
  have hunique : Unique (groupCohomology.H1
      (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) L)) :=
    groupCohomology.H1ofAutOnUnitsUnique
      (IntermediateField.fixedField H) L
  have hinj : Function.Injective E.hom :=
    (ModuleCat.mono_iff_injective E.hom).mp (inferInstance : Mono E.hom)
  have htarget : Subsingleton (chapter05GroupCohomology
      (Gal(L / IntermediateField.fixedField H))
      (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField H) L) 1) :=
    ⟨fun x y => (hunique.uniq x).trans (hunique.uniq y).symm⟩
  have hsource : Subsingleton (chapter05GroupCohomology H
      (Rep.res H.subtype (chapter05CoefficientRep K L)) 1) :=
    ⟨fun x y => hinj (@Subsingleton.elim _ htarget (E.hom x) (E.hom y))⟩
  exact (ModuleCat.isZero_iff_subsingleton).2 hsource

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
  unfold chapter05Generates
  apply top_unique
  intro y hy
  have hyinv : I.invariant H y ∈ (I.invariant H).range := ⟨y, rfl⟩
  rw [I.invariant_range H] at hyinv
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hyinv
  have hinv :
      I.invariant H (k • chapter05RestrictTwoClass H u) = I.invariant H y := by
    rw [map_zsmul, I.restriction_formula H, hk]
  have heq : k • chapter05RestrictTwoClass H u = y :=
    I.invariant_injective H hinv
  apply Submodule.mem_span_singleton.mpr
  refine ⟨k, ?_⟩
  change (ModuleCat.isModule
      (chapter05GroupCohomology H
        (Rep.res H.subtype (chapter05CoefficientRep K L)) 2)).smul k
      (chapter05RestrictTwoClass H u) = y
  rw [int_smul_eq_zsmul (ModuleCat.isModule
      (chapter05GroupCohomology H
        (Rep.res H.subtype (chapter05CoefficientRep K L)) 2)) k
      (chapter05RestrictTwoClass H u)]
  exact heq

/- The three local inputs used in the source proof assemble into the exact
   subgroup-wise hypotheses required by Tate--Nakayama.  Keeping this package
   explicit prevents the class-formation theorem from silently treating those
   local-field facts as an unrelated conclusion. -/
theorem chapter05_local_tate_nakayama_hypotheses
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    {u : chapter05GroupCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 2}
    (I : Chapter05LocalBrauerInvariantSystem K L u) :
    Chapter05TateNakayamaHypotheses (Gal(L / K))
      (chapter05CoefficientRep K L) u := by
  refine
    { hH1 := fun H => chapter05_local_hilbert90 K L H
      hH2 := fun H => chapter05_local_H2_cyclic K L I H
      hres_generates := fun H => chapter05_local_restriction_generates K L I H }

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
