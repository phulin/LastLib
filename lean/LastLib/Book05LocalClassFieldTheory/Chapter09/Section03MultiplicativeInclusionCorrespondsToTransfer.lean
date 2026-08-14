import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Transfer

import LastLib.Book05LocalClassFieldTheory.Chapter09.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

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
  letI : Finite (T : Set G) := T.2.finite_right
  letI := Fintype.ofFinite (T : Set G)
  exact ∏ r : (T : Set G), Abelianization.of (chapter09RightCosetTransferFactor T g r)

/-- The right-coset product computes the abelianized transfer. -/
theorem chapter09_transfer_eq_rightCoset_product
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    (T : H.RightTransversal) (g : G) :
    chapter09Transfer H (Abelianization.of g) =
      chapter09RightCosetTransferProduct T g := by
  sorry

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

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
