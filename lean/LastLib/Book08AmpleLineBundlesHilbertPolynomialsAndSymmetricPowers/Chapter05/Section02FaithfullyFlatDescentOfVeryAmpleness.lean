import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies

/-!
# 5.2 Faithfully flat descent of very ampleness

The base-changed line bundle in this section is always the pullback of a line bundle already on
`X`.  The separate `IsBaseChangeOf` interface records the descent-data warning from the text.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

theorem injective_iff_faithfullyFlat_lTensor
    {R S M N : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Algebra R S] [Module R M] [Module R N] [Module.FaithfullyFlat R S]
    (u : M →ₗ[R] N) :
    Function.Injective (u.lTensor S) ↔ Function.Injective u := by
  sorry

theorem surjective_iff_faithfullyFlat_lTensor
    {R S M N : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Algebra R S] [Module R M] [Module R N] [Module.FaithfullyFlat R S]
    (u : M →ₗ[R] N) :
    Function.Surjective (u.lTensor S) ↔ Function.Surjective u := by
  sorry

theorem bijective_iff_faithfullyFlat_lTensor
    {R S M N : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Algebra R S] [Module R M] [Module R N] [Module.FaithfullyFlat R S]
    (u : M →ₗ[R] N) :
    Function.Bijective (u.lTensor S) ↔ Function.Bijective u := by
  sorry

/- The target of this proposition is the Lean presentation of
`Γ(X, L^n) ⊗_A A' ≃ Γ(X_{S'}, L_{S'}^n)`.  The module structures are induced by the two
affine structure morphisms, so the displayed identity is visible without adding a fake global
sections API. -/
noncomputable def affine_degree_zero_sections_base_change
    {X : Scheme.{u}} {A A' : Type u} [CommRing A] [CommRing A']
    (f : X ⟶ Spec (.of A)) (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (φ : A →+* A') (hφ : RingHom.Flat φ) (L : LineBundle X)
    (P : LineBundlePowers L) (n : ℕ) :
    let g : Spec (.of A') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
    let f' := baseChangeToBase f g
    let A_to_X : A →+* Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
    let A'_to_X' : A' →+* Γ(baseChange f g, ⊤) :=
      ((Scheme.ΓSpecIso (.of A')).inv ≫ f'.appTop).hom
    letI : Module A Γ((P.power n).sheaf, ⊤) := Module.compHom _ A_to_X
    letI : Module A' Γ((baseChangeLineBundle f g (P.power n)).sheaf, ⊤) :=
      Module.compHom _ A'_to_X'
    ((ModuleCat.extendScalars φ).obj
      (ModuleCat.of A Γ((P.power n).sheaf, ⊤)) ≅
      ModuleCat.of A' Γ((baseChangeLineBundle f g (P.power n)).sheaf, ⊤)) := by sorry

theorem veryAmple_faithfullyFlat_descent
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hL : IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)) :
    IsVeryAmple f L := by sorry

theorem veryAmple_faithfullyFlat_descent_of_descended_line_bundle
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (M : LineBundle (baseChange f g)) (hM : IsBaseChangeOf f g L M)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hMvery : IsVeryAmple (baseChangeToBase f g) M) :
    IsVeryAmple f L := by sorry

theorem immersion_iff_faithfullyFlat_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g) :
    IsImmersion f ↔ IsImmersion (baseChangeToBase f g) := by sorry

theorem immersion_faithfullyFlat_descent
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (h : IsImmersion (baseChangeToBase f g)) :
    IsImmersion f := by sorry

theorem closedImmersion_of_proper_immersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hproper : IsProper f) (himmersion : IsImmersion f) :
    IsClosedImmersion f := by sorry

theorem veryAmple_faithfullyFlat_descent_with_finiteness
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hproper : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hL : IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)) :
    ∃ w : RelativeVeryAmpleWitness f L,
      IsClosedImmersion w.embedding ∧
        IsFiniteDimensionalLocallyOnBase w.projectiveBundle := by sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
