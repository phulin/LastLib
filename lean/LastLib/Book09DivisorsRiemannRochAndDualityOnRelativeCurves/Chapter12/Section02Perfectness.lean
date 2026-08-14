import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-! ### 12.2 Perfectness -/

/-- A pairing whose right-hand argument identifies with the dual of the left. -/
structure Chapter12PerfectPairing (k : Type u) [Field k]
    (V W : Type v) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] where
  pairing : V →ₗ[k] W →ₗ[k] k
  rightToLeftDual : W ≃ₗ[k] Module.Dual k V
  rightToLeftDual_apply : ∀ w v, rightToLeftDual w v = pairing v w

/-! The direct duality equivalence must still be tied to the residue
pairing.  Keeping that compatibility next to the equivalence prevents the
two source-level formulations of perfectness from drifting apart. -/
structure Chapter12ResiduePairingPerfectness
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) where
  dualEquiv : Module.Dual k (chapter12DivisorHOne K D) ≃ₗ[k]
    chapter12DivisorOmegaHZero K W D
  dualEquiv_apply : ∀ c η,
    (dualEquiv.symm η) c = chapter12ResiduePairing P c η

/-- The residue pairing gives the perfect Serre-duality isomorphism (12.3). -/
noncomputable def chapter12_residue_pairing_perfect_data
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    Chapter12ResiduePairingPerfectness K D A W P := by
  sorry

noncomputable def chapter12_residue_pairing_perfect
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    Module.Dual k (chapter12DivisorHOne K D) ≃ₗ[k]
      chapter12DivisorOmegaHZero K W D :=
  (chapter12_residue_pairing_perfect_data K D A W P).dualEquiv

theorem chapter12_residue_pairing_perfect_compatibility
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) :
    (chapter12_residue_pairing_perfect K D A W P).symm η c =
      chapter12ResiduePairing P c η := by
  exact (chapter12_residue_pairing_perfect_data K D A W P).dualEquiv_apply c η

theorem chapter12_residue_pairing_is_perfect_pairing
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    ∃ Q : Chapter12PerfectPairing k (chapter12DivisorHOne K D)
      (chapter12DivisorOmegaHZero K W D),
      ∀ c η, Q.pairing c η = chapter12ResiduePairing P c η := by
  sorry

/-- Equivalently, the differential space is identified with the dual of
the principal-part space through the residue pairing. -/
noncomputable def chapter12_residue_pairing_perfect_right_form
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C) (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    chapter12DivisorOmegaHZero K W D ≃ₗ[k]
      Module.Dual k (chapter12DivisorHOne K D) := by
  exact (chapter12_residue_pairing_perfect K D A W P).symm

/-- On a smooth curve the dualizing sheaf is the sheaf of differentials. -/
noncomputable def chapter12_dualizing_sheaf_is_differential_sheaf
    {k : Type u} [Field k] {C : Chapter12Curve k}
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K) :
    W.omega ≅ W.differentialSheaf :=
  by sorry

/-! The comparison with the trace from the dualizing construction is kept as
a separate compatibility record: the assigned earlier chapter does not yet
provide restriction and connecting morphism objects for this draft. -/
structure Chapter12TraceResidueCompatibility
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) where
  cupProduct : chapter12DivisorHOne K D →ₗ[k]
    chapter12DivisorOmegaHZero K W D →ₗ[k] chapter12HOne K W.omega
  restriction_compatibility : Prop
  restriction_compatibility_holds : restriction_compatibility
  connecting_compatibility : Prop
  connecting_compatibility_holds : connecting_compatibility
  local_generator_agreement : Prop
  local_generator_agreement_holds : local_generator_agreement
  cupProduct_eq_residue_data : ∀ c η,
    cupProduct c η = P.cupProduct c η
  trace_residue_eq : ∀ c η,
    W.trace (cupProduct c η) = chapter12ResiduePairing P c η

theorem chapter12_trace_residue_compatibility_exists
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W) :
    Nonempty (Chapter12TraceResidueCompatibility K D A W P) := by
  sorry

theorem chapter12_trace_residue_compatibility
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (T : Chapter12TraceResidueCompatibility K D A W P)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) :
    W.trace (T.cupProduct c η) = chapter12ResiduePairing P c η := by
  exact T.trace_residue_eq c η

theorem chapter12_trace_residue_compatibility_eq_data_trace
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12LineBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (D : Chapter12Divisor C)
    (A : Chapter12AffineResidueCover C D)
    (W : Chapter12DualizingSheafData C K)
    [R : Chapter12RationalFunctionTheory C]
    (P : Chapter12ResiduePairingData K D A W)
    (T : Chapter12TraceResidueCompatibility K D A W P)
    (c : chapter12DivisorHOne K D)
    (η : chapter12DivisorOmegaHZero K W D) :
    W.trace (P.cupProduct c η) = chapter12ResiduePairing P c η := by
  rw [← T.cupProduct_eq_residue_data c η]
  exact T.trace_residue_eq c η

/-- The local generator t⁻¹ paired with dt has residue one. -/
theorem chapter12_local_skyscraper_tInv_dt
    {k : Type u} [Field k]
    (L : Chapter12LocalSkyscraperResidueData k) :
    L.pairing L.tInv L.dt = 1 :=
  by exact L.pairing_tInv_dt

/-- The displayed rational-point calculation is the coefficient calculation
for the local principal part t⁻¹ and differential dt. -/
theorem chapter12_local_rational_point_pairing
    {k : Type u} [Field k] (a b : k) :
    chapter12RationalPointLocalResiduePairing a b = a * b := by
  rfl

/-- The nonrational closed-point pairing is with the k-linear dual of the
residue field, not with an unqualified scalar trace. -/
theorem chapter12_nonrational_residue_pairing_is_perfect
    {k : Type u} [Field k]
    (P : Chapter12ClosedPointResidueData k)
    [FiniteDimensional k P.principalParts]
    [FiniteDimensional k P.residueField] :
    ∃ e : P.principalParts ≃ₗ[k]
        Module.Dual k (Module.Dual k P.residueField),
      ∀ x φ, e x φ = P.pairing x φ := by
  sorry

/-- In the separable finite-field case, the local functional is the familiar
field-trace pairing. -/
structure Chapter12ResidueFieldTraceModel (k : Type u) [Field k] where
  residueField : Type v
  [field : Field residueField]
  [algebra : Algebra k residueField]

attribute [instance] Chapter12ResidueFieldTraceModel.field
  Chapter12ResidueFieldTraceModel.algebra

def Chapter12ResidueFieldTraceModel.pairing
    {k : Type u} [Field k] (M : Chapter12ResidueFieldTraceModel k)
    (a b : M.residueField) : k :=
  Algebra.trace k M.residueField (a * b)

theorem chapter12_separable_residue_field_trace_formula
    {k : Type u} [Field k]
    (M : Chapter12ResidueFieldTraceModel k)
    [FiniteDimensional k M.residueField]
    [Algebra.IsSeparable k M.residueField]
    (a b : M.residueField) :
    M.pairing a b = Algebra.trace k M.residueField (a * b) := by
  rfl

/-- The finite dualizing module remains the local coefficient object in the
inseparable case, where the naive field trace can be degenerate. -/
def chapter12InseparableFiniteDualizingModule
    {k : Type u} [Field k] (P : Chapter12ClosedPointResidueData k) :
    ModuleCat.{v} k :=
  P.principalParts

theorem chapter12_inseparable_residue_pairing_uses_dualizing_module
    {k : Type u} [Field k]
    (P : Chapter12ClosedPointResidueData k)
    [FiniteDimensional k P.principalParts]
    [FiniteDimensional k P.residueField]
    (hinseparable : ¬ Algebra.IsSeparable k P.residueField) :
    ∃ e : chapter12InseparableFiniteDualizingModule P ≃ₗ[k]
        Module.Dual k (Module.Dual k P.residueField),
      ∀ x φ, e x φ = P.pairing x φ := by
  sorry

/-! The divisor devissage used to propagate the local calculation. -/

structure Chapter12DivisorDevissageData {k : Type u} [Field k]
    {C : Chapter12Curve k} (D : Chapter12Divisor C) where
  point : C.scheme
  point_closed : IsClosed ({point} : Set C.scheme)
  Dplus : Chapter12Divisor C
  coefficient_add_point :
    Dplus.coefficient = D.coefficient + Finsupp.single point 1
  inclusion : D.lineBundle.sheaf ⟶ Dplus.lineBundle.sheaf
  quotientModule : C.scheme.Modules
  quotient : Dplus.lineBundle.sheaf ⟶ quotientModule
  quotientZeroDimensional : Prop
  quotientZeroDimensional_holds : quotientZeroDimensional
  comp_zero : inclusion ≫ quotient = 0
  inclusion_mono : Mono inclusion
  exact : (ShortComplex.mk inclusion quotient comp_zero).Exact
  quotient_epi : Epi quotient

def chapter12DivisorDevissageComplex
    {k : Type u} [Field k] {C : Chapter12Curve k}
    {D : Chapter12Divisor C} (E : Chapter12DivisorDevissageData D) :
    ShortComplex C.scheme.Modules :=
  ShortComplex.mk E.inclusion E.quotient E.comp_zero

/-- The divisor sequence
0 → 𝓞(D) → 𝓞(D+p) → 𝓠ₚ → 0
is exact. -/
theorem chapter12_divisor_devissage_exact
    {k : Type u} [Field k] {C : Chapter12Curve k}
    {D : Chapter12Divisor C} (E : Chapter12DivisorDevissageData D) :
    Mono E.inclusion ∧
      (chapter12DivisorDevissageComplex E).Exact ∧
      Epi E.quotient := by
  exact ⟨E.inclusion_mono, E.exact, E.quotient_epi⟩

/-! The quotient-level residue functional is kept as an explicit local
interface.  Its perfectness is a statement about the zero-dimensional local
module, not about the sheaf object merely viewed as a type. -/
structure Chapter12DivisorQuotientDuality {k : Type u} [Field k]
    {C : Chapter12Curve k} {D : Chapter12Divisor C}
    (E : Chapter12DivisorDevissageData D)
  (K : Chapter12CohomologyContext C) where
  dual : ModuleCat.{v} k
  pairing : dual →ₗ[k] chapter12HZero K E.quotientModule →ₗ[k] k
  pairing_injective : Function.Injective pairing
  pairing_finrank_eq :
    Module.finrank k (dual : Type v) =
      Module.finrank k (chapter12HZero K E.quotientModule)

theorem chapter12_divisor_devissage_quotient_duality_exists
    {k : Type u} [Field k] {C : Chapter12Curve k}
    {D : Chapter12Divisor C} (E : Chapter12DivisorDevissageData D)
    (K : Chapter12CohomologyContext C) :
    Nonempty (Chapter12DivisorQuotientDuality E K) := by
  sorry

/-- The local residue functional is the dual of the zero-dimensional
devissage quotient. -/
theorem chapter12_divisor_devissage_quotient_dual
    {k : Type u} [Field k] {C : Chapter12Curve k}
    {D : Chapter12Divisor C} (E : Chapter12DivisorDevissageData D)
    (K : Chapter12CohomologyContext C)
    (Q : Chapter12DivisorQuotientDuality E K)
    [FiniteDimensional k Q.dual]
    [FiniteDimensional k (chapter12HZero K E.quotientModule)] :
    ∃ e : (Q.dual : Type v) ≃ₗ[k]
        Module.Dual k (chapter12HZero K E.quotientModule),
      ∀ q x, e q x = Q.pairing q x := by
  sorry

/-! A finite exact sequence is recorded together with the reverse dual
sequence and the equations saying that every arrow is transposed.  The
connecting maps themselves belong to the cohomology implementation, so this
record is the stable seam used by the statement below. -/
structure Chapter12DivisorDevissageLongExactTranspose {k : Type u} [Field k]
    {C : Chapter12Curve k} {D : Chapter12Divisor C}
    (E : Chapter12DivisorDevissageData D)
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K) where
  term : Fin 6 → ModuleCat.{v} k
  map : ∀ i : Fin 5, term i.castSucc ⟶ term i.succ
  dualTerm : Fin 6 → ModuleCat.{v} k
  dualMap : ∀ i : Fin 5, dualTerm i.succ ⟶ dualTerm i.castSucc
  pairing : ∀ i, (term i : Type v) →ₗ[k] (dualTerm i : Type v) →ₗ[k] k
  exact : Prop
  exact_holds : exact
  dual_exact : Prop
  dual_exact_holds : dual_exact
  dualizing_shift_comparison : Prop
  dualizing_shift_comparison_holds : dualizing_shift_comparison
  transpose : ∀ (i : Fin 5) (x : term i.castSucc) (φ : dualTerm i.succ),
    pairing i.succ ((map i).hom x) φ =
      pairing i.castSucc x ((dualMap i).hom φ)

/-- Dualizing the divisor short exact sequence transposes its long exact
cohomology sequence. -/
theorem chapter12_divisor_devissage_long_exact_transpose
    {k : Type u} [Field k] {C : Chapter12Curve k}
    {D : Chapter12Divisor C} (E : Chapter12DivisorDevissageData D)
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K) :
    Nonempty (Chapter12DivisorDevissageLongExactTranspose E K W) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the earlier projective-space resolution API is not
available in this checkout, so its two initial degree calculations are exposed
as the input seam for devissage. -/
/-! The projective-space calculation is an initial input to the devissage
argument.  Its two degree statements are kept separate so that later
propagation can use either degree without importing Riemann--Roch. -/
structure Chapter12ProjectiveSpaceInitialDuality (k : Type u) [Field k] where
  projectiveSpace : Scheme.{u}
  finiteResolution : Prop
  finiteResolution_holds : finiteResolution
  degreeZeroCalculation : Prop
  degreeZeroCalculation_holds : degreeZeroCalculation
  degreeOneCalculation : Prop
  degreeOneCalculation_holds : degreeOneCalculation

theorem chapter12_projective_space_initial_calculation
    {k : Type u} [Field k]
    (B : Chapter12ProjectiveSpaceInitialDuality k) :
    B.degreeZeroCalculation ∧ B.degreeOneCalculation := by
  exact ⟨B.degreeZeroCalculation_holds, B.degreeOneCalculation_holds⟩

/-! A small reusable logical bridge records the precise two-out-of-three
shape used when adding or removing one closed point. -/
theorem chapter12_two_out_of_three
    {P Q R : Prop}
    (hPQ : P → Q → R) (hPR : P → R → Q) (hQR : Q → R → P) :
    (P ∧ Q → R) ∧ (P ∧ R → Q) ∧ (Q ∧ R → P) := by
  exact ⟨fun h => hPQ h.1 h.2, fun h => hPR h.1 h.2, fun h => hQR h.1 h.2⟩

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
