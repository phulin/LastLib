import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
open scoped BigOperators

/-! ### 12.1 The residue pairing -/

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
      ∑ x ∈ P.residueSupport (chapter12ResidueRepresentative K D A W P c) η,
        P.residue x (P.multiply (chapter12ResidueRepresentative K D A W P c) η) := by
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
    chapter08_residue_sum k P.globalResidues h = 0 := by
  sorry

theorem chapter12_regular_left_extension_has_zero_residue
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (u : R.RegularFunction A.U)
    (η : chapter12DivisorOmegaHZero K W D) :
    ∑ x ∈ P.globalResidueSupport (P.multiply (P.leftToOverlap u) η),
      P.residue x (P.multiply (P.leftToOverlap u) η) = 0 := by
  sorry

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
    (u : R.RegularFunction A.U) (v : R.RegularFunction A.V) :
    chapter12ResiduePairing P c η =
      chapter12ResidueSum P
        (P.modify (chapter12ResidueRepresentative K D A W P c) u v) η := by
  sorry

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
  sorry

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
  sorry

/-! The named cup-product trace is the actual dualizing trace, rather than an
arbitrary scalar-valued placeholder. -/
theorem chapter12_residue_pairing_eq_dualizing_trace
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) :
    chapter12ResiduePairing P c η = W.trace (P.cupProduct c η) := by
  exact (chapter12_residue_pairing_eq_cup_product_trace K D A W P c η).trans
    (P.cupProductTrace_eq_trace c η)

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
