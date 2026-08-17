import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Transfer

import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

open CategoryTheory
open LastLib.Book05LocalClassFieldTheory.Chapter05
open scoped BigOperators

/-!
## 9.3 Multiplicative inclusion corresponds to transfer
-/

/-- The canonical equivalence between a group and the range of an injective hom. -/
noncomputable def chapter09RangeEquiv
    {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) : H ≃* f.range :=
  (Subgroup.topEquiv.symm.trans
      (Subgroup.equivMapOfInjective (⊤ : Subgroup H) f hf)).trans
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_map f).symm)

theorem chapter09RangeEquiv_apply
    {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) (x : H) :
    (chapter09RangeEquiv f hf x : G) = f x := by
  simp [chapter09RangeEquiv]

/-- Transfer to a subgroup, followed by passage to the abelianization. -/
noncomputable def chapter09Transfer
    {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    Abelianization G →* Abelianization H :=
  Abelianization.lift
    (MonoidHom.transfer (Abelianization.of : H →* Abelianization H))

theorem chapter09Transfer_of
    {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] (g : G) :
    chapter09Transfer H (Abelianization.of g) =
      MonoidHom.transfer (Abelianization.of : H →* Abelianization H) g := by
  simp [chapter09Transfer]

/-- Transfer along an injective homomorphism, with the range identified with its domain. -/
noncomputable def chapter09TransferAlong
    {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f)
    (hfinite : f.range.FiniteIndex) :
    Abelianization G →* Abelianization H := by
  letI : f.range.FiniteIndex := hfinite
  exact
    (Abelianization.map (chapter09RangeEquiv f hf).symm.toMonoidHom).comp
      (chapter09Transfer f.range)

/-- The element of the subgroup attached to a chosen right transversal representative. -/
noncomputable def chapter09RightCosetTransferFactor
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (T : H.RightTransversal) (g : G) (r : (T : Set G)) : H :=
  ⟨(r : G) * g * (T.2.toRightFun ((r : G) * g) : G)⁻¹,
    T.2.mul_inv_toRightFun_mem ((r : G) * g)⟩

theorem chapter09RightCosetTransferFactor_spec
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (T : H.RightTransversal) (g : G) (r : (T : Set G)) :
    (chapter09RightCosetTransferFactor T g r : G) *
        (T.2.toRightFun ((r : G) * g) : G) = (r : G) * g := by
  simp [chapter09RightCosetTransferFactor, mul_assoc]

/-- The transfer product for a chosen right transversal, viewed in `Hᵃᵇ`. -/
noncomputable def chapter09RightCosetTransferProduct
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (T : H.RightTransversal) (g : G) : Abelianization H := by
  let _ : Finite (T : Set G) := T.2.finite_right
  let _ : Fintype (T : Set G) := Fintype.ofFinite (T : Set G)
  exact ∏ r : (T : Set G), Abelianization.of (chapter09RightCosetTransferFactor T g r)

/-- The right-coset product computes the abelianized transfer. -/
theorem chapter09_transfer_eq_rightCoset_product
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (T : H.RightTransversal) (g : G) :
    chapter09Transfer H (Abelianization.of g) =
      chapter09RightCosetTransferProduct T g := by
  classical
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  let f : G ⧸ H → G := fun q =>
    (T.2.rightQuotientEquiv (e.symm q) : G)⁻¹
  have hf : ∀ q, (f q : G ⧸ H) = q := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    dsimp [f]
    have he : e.symm (Quotient.mk'' x) = Quotient.mk'' x⁻¹ := by
      rfl
    rw [he]
    let r : G := T.2.rightQuotientEquiv (Quotient.mk'' x⁻¹)
    have hr : Quotient.mk'' r = Quotient.mk'' x⁻¹ :=
      T.2.mk''_rightQuotientEquiv (Quotient.mk'' x⁻¹)
    have hrel : x⁻¹ * r⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact' hr)
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    simpa [r] using H.inv_mem hrel
  let S : H.LeftTransversal :=
    ⟨Set.range f, Subgroup.isComplement_range_left hf⟩
  have hα (q : G ⧸ H) :
      (S.2.leftQuotientEquiv q : G) = f q :=
    Subgroup.IsComplement.leftQuotientEquiv_apply hf q
  have hβf (q : G ⧸ H) :
      ((g * f (g⁻¹ • q) : G) : G ⧸ H) = q := by
    change g • (f (g⁻¹ • q) : G ⧸ H) = q
    rw [hf]
    simp
  have hβ (q : G ⧸ H) :
      (g • S).2.leftQuotientEquiv q =
        ⟨g * f (g⁻¹ • q), by
          exact ⟨f (g⁻¹ • q), ⟨g⁻¹ • q, rfl⟩, rfl⟩⟩ := by
    apply (g • S).2.leftQuotientEquiv.symm.injective
    have hb :
        (g • S).2.leftQuotientEquiv.symm
            ⟨g * f (g⁻¹ • q), by
              exact ⟨f (g⁻¹ • q), ⟨g⁻¹ • q, rfl⟩, rfl⟩⟩ =
          ((g * f (g⁻¹ • q) : G) : G ⧸ H) := by
      rfl
    simpa only [Equiv.symm_apply_apply, hb] using (hβf q).symm
  let er : (T : Set G) ≃ G ⧸ H := T.2.rightQuotientEquiv.symm.trans e
  have hfr (r : (T : Set G)) : f (er r) = (r : G)⁻¹ := by
    dsimp [f, er]
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have hshift (r : (T : Set G)) :
      f (g⁻¹ • er r) =
        (T.2.toRightFun ((r : G) * g) : G)⁻¹ := by
    have hq :
        e.symm (g⁻¹ • er r) = Quotient.mk'' ((r : G) * g) := by
      apply e.injective
      dsimp [er]
      rw [e.apply_symm_apply]
      dsimp [e, QuotientGroup.quotientRightRelEquivQuotientLeftRel]
      have hr :
          T.2.rightQuotientEquiv.symm r = Quotient.mk'' (r : G) := by
        simpa using
          (T.2.mk''_rightQuotientEquiv (T.2.rightQuotientEquiv.symm r)).symm
      rw [hr]
      simp
    dsimp [f]
    rw [hq]
    rfl
  rw [chapter09Transfer_of]
  rw [MonoidHom.transfer_def (Abelianization.of : H →* Abelianization H) S g]
  simp only [Subgroup.leftTransversals.diff, chapter09RightCosetTransferProduct]
  simp only [hα, hβ]
  let _ : Finite (T : Set G) := T.2.finite_right
  let _ : Fintype (T : Set G) := Fintype.ofFinite (T : Set G)
  let _ := H.fintypeQuotientOfFiniteIndex
  rw [← Fintype.prod_equiv er]
  intro r
  simp only [hfr, hshift, chapter09RightCosetTransferFactor, inv_inv]
  exact congrArg (fun z : H => Abelianization.of z)
    (Subtype.ext (mul_assoc (r : G) g
      (T.2.toRightFun ((r : G) * g) : G)⁻¹))

/-- Changing the chosen right-transversal representatives changes the product only by a
commutator, hence not in the abelianization. -/
theorem chapter09_rightCosetTransferProduct_independent
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {T U : H.RightTransversal} (g : G) :
    chapter09RightCosetTransferProduct T g =
      chapter09RightCosetTransferProduct U g := by
  rw [← chapter09_transfer_eq_rightCoset_product T g,
    ← chapter09_transfer_eq_rightCoset_product U g]

/-- The transfer attached to the Galois inclusion in the common closure. -/
noncomputable def chapter09GaloisTransfer
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks) :
    Abelianization (Gal(Ks / K)) →* Abelianization (Gal(Ks / L)) :=
  chapter09TransferAlong
    (chapter09GaloisInclusion K L Ks)
    (chapter09_galoisInclusion_injective K L Ks)
    T.galoisInclusion_finiteIndex

/--
Theorem 9.2 (inclusion–transfer compatibility).

This is the equality represented by the second reciprocity square:
`rec_L ∘ ι = Ver_{L/K} ∘ rec_K`.
-/
theorem chapter09_inclusion_transfer_compatibility
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T) :
    R.recL.reciprocity.comp (chapter09FieldInclusionHom K L) =
      (chapter09GaloisTransfer K L Ks T).comp R.recK.reciprocity := by
  sorry

theorem chapter09_inclusion_transfer_compatibility_apply
    (K L Ks : Type) [Field K] [Field L] [Field Ks]
    [Algebra K L] [Algebra K Ks] [Algebra L Ks]
    [IsScalarTower K L Ks] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (T : Chapter09FiniteSeparableExtension K L Ks)
    (R : Chapter09ReciprocitySystem K L Ks T) (x : Kˣ) :
    R.recL.reciprocity (chapter09FieldInclusionHom K L x) =
      chapter09GaloisTransfer K L Ks T (R.recK.reciprocity x) := by
  exact DFunLike.congr_fun
    (chapter09_inclusion_transfer_compatibility K L Ks T R) x

/-!
The finite-level proof uses restriction on degree zero and on complete
resolutions.  The following record keeps the degree `-2` cap maps after the
same top-subgroup identifications used in Section 9.2, and records the exact
homology-transfer and cap-naturality identities from Section 5.2.
-/

structure Chapter09FiniteRestrictionTransferData
    (G : Type) [Group G] [Fintype G]
    (H : Subgroup G) [H.FiniteIndex] (A : Rep ℤ G) where
  fundamentalClassG : chapter05GroupCohomology G A 2
  fundamentalClassH :
    chapter05GroupCohomology H (Rep.res H.subtype A) 2
  capProductG :
    chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2) ⟶
      chapter05TateCohomology G A 0
  capProductH :
    chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-2) ⟶
      chapter05TateCohomology H (Rep.res H.subtype A) 0
  restrictionMinusTwo :
    chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2) ⟶
      chapter05TateCohomology H (Rep.trivial ℤ H ℤ) (-2)
  restrictionZero :
    chapter05TateCohomology G A 0 ⟶
      chapter05TateCohomology H (Rep.res H.subtype A) 0
  fundamentalClass_restriction :
    chapter05RestrictTwoClass H fundamentalClassG = fundamentalClassH
  restrictionMinusTwo_on_H1 :
    ∀ z : chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1,
      (chapter05H1AbelianizationIso H)
          ((chapter05_tate_minus_two_is_homology H).hom
            (restrictionMinusTwo
              ((chapter05_tate_minus_two_is_homology G).inv z))) =
        Additive.ofMul
          (chapter09Transfer H
            (Additive.toMul ((chapter05H1AbelianizationIso G) z)))
  cap_naturality :
    ∀ z : chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2),
      restrictionZero (capProductG z) =
        capProductH (restrictionMinusTwo z)

theorem chapter09_finite_restriction_fundamental_class
    {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} [H.FiniteIndex] {A : Rep ℤ G}
    (D : Chapter09FiniteRestrictionTransferData G H A) :
    chapter05RestrictTwoClass H D.fundamentalClassG = D.fundamentalClassH :=
  D.fundamentalClass_restriction

theorem chapter09_finite_restriction_on_H1_is_transfer
    {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} [H.FiniteIndex] {A : Rep ℤ G}
    (D : Chapter09FiniteRestrictionTransferData G H A)
    (z : chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1) :
    (chapter05H1AbelianizationIso H)
        ((chapter05_tate_minus_two_is_homology H).hom
          (D.restrictionMinusTwo
            ((chapter05_tate_minus_two_is_homology G).inv z))) =
      Additive.ofMul
        (chapter09Transfer H
          (Additive.toMul ((chapter05H1AbelianizationIso G) z))) :=
  D.restrictionMinusTwo_on_H1 z

theorem chapter09_finite_restriction_cap_naturality
    {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} [H.FiniteIndex] {A : Rep ℤ G}
    (D : Chapter09FiniteRestrictionTransferData G H A)
    (z : chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2)) :
    D.restrictionZero (D.capProductG z) =
      D.capProductH (D.restrictionMinusTwo z) :=
  D.cap_naturality z

/- Restriction in degree zero is the field inclusion on multiplicative
groups, so it is well defined on the norm quotients used by reciprocity. -/

structure Chapter09FiniteDegreeZeroInclusionData
    (K L : Type*) [Field K] [Field L] [Algebra K L] where
  restriction : Kˣ →* Lˣ
  restriction_is_inclusion : restriction = chapter09FieldInclusionHom K L

theorem chapter09_finite_degree_zero_restriction_is_inclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (D : Chapter09FiniteDegreeZeroInclusionData K L) :
    D.restriction = chapter09FieldInclusionHom K L :=
  D.restriction_is_inclusion

/- For an unramified extension, transfer sends the arithmetic Frobenius class
downstairs, while inclusion identifies that class with the `d`th power of the
base Frobenius. -/

structure Chapter09UnramifiedTransferFrobeniusData
    (G_K G_L : Type) [Group G_K] [Group G_L] where
  degree : ℕ
  transfer : Abelianization G_K →* Abelianization G_L
  inclusion : G_L →* G_K
  arithmeticFrobeniusK : G_K
  arithmeticFrobeniusL : G_L
  transfer_frobenius :
    transfer (Abelianization.of arithmeticFrobeniusK) =
      Abelianization.of arithmeticFrobeniusL
  inclusion_frobenius_power :
    inclusion arithmeticFrobeniusL = arithmeticFrobeniusK ^ degree

theorem chapter09_unramified_transfer_frobenius
    {G_K G_L : Type} [Group G_K] [Group G_L]
    (D : Chapter09UnramifiedTransferFrobeniusData G_K G_L) :
    D.transfer (Abelianization.of D.arithmeticFrobeniusK) =
        Abelianization.of D.arithmeticFrobeniusL ∧
      D.inclusion D.arithmeticFrobeniusL =
        D.arithmeticFrobeniusK ^ D.degree :=
  ⟨D.transfer_frobenius, D.inclusion_frobenius_power⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
