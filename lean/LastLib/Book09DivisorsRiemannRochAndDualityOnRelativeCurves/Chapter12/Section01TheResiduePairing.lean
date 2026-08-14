import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

/-! ### 12.1 The residue pairing -/

/-- Every cohomology class admits a Čech representative on the chosen affine cover. -/
theorem chapter12_cech_representative_exists
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    ∀ c : chapter12DivisorHOne K D,
      Nonempty (Chapter12CechRepresentative K D A W P) := by
  intro c
  exact ⟨{g := P.representative c, class := c, class_represented_by_g := rfl}⟩

/-- Formula (12.1), with the finite support of the residue sum explicit. -/
theorem chapter12_residue_pairing_formula
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) :
    chapter12ResiduePairing P c η =
      ∑ x in P.residueSupport (P.representative c) η,
        P.residue x (P.multiply (P.representative c) η) := by
  rfl

/-- The global residue theorem used to compare a chosen partial sum with its
complement. -/
theorem chapter12_global_residue_theorem
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (h : P.rationalDifferential) :
    ∑ x in P.globalResidueSupport h, P.residue x h = 0 := by
  exact P.global_residue_theorem h

theorem chapter12_regular_left_extension_has_zero_residue
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (u : P.leftExtension)
    (η : chapter12DivisorOmegaHZero K W D) :
    ∑ x in P.globalResidueSupport (P.multiply (P.leftToOverlap u) η),
      P.residue x (P.multiply (P.leftToOverlap u) η) = 0 := by
  exact P.left_extension_residue_zero u η

/-- Changing a representative by functions extending from U and V does not
change the residue pairing. -/
theorem chapter12_residue_pairing_well_defined_under_extensions
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D)
    (u : P.leftExtension) (v : P.rightExtension) :
    chapter12ResiduePairing P c η =
      chapter12ResidueSum P (P.modify (P.representative c) u v) η := by
  simpa [chapter12ResiduePairing, chapter12ResidueSum] using
    P.modify_invariant (P.representative c) u v η

/-- The residue sum is bilinear in the Čech class and the differential. -/
theorem chapter12_residue_pairing_bilinear
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    ∃ B : chapter12DivisorHOne K D →ₗ[k]
        chapter12DivisorOmegaHZero K W D →ₗ[k] k,
      ∀ c η, B c η = chapter12ResiduePairing P c η := by
  refine ⟨P.residuePairingLinear, ?_⟩
  intro c η
  simpa [chapter12ResiduePairing, chapter12ResidueSum] using
    P.residuePairingLinear_apply c η

/-- The Čech residue formula equals cup product followed by the dualizing
trace, giving the sheaf-theoretic map (12.2). -/
theorem chapter12_residue_pairing_eq_cup_product_trace
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) :
    chapter12ResiduePairing P c η = P.cupProductTrace c η := by
  simpa [chapter12ResiduePairing, chapter12ResidueSum] using
    (P.cupProductTrace_eq_residueSum c η).symm

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
