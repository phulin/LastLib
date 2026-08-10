import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section07ExplicitUnramifiedNormEquations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open scoped Polynomial

/-! ## 11.8. Explicit norm equations in a tame totally ramified extension

The valuation coordinate is separated from the residue-unit coordinate.  The
resulting set is the elementary tame norm-equation obstruction; the stronger
principal-unit hypotheses are kept visible in the theorem that identifies it
with the actual norm image.
-/

/- The full set of tame norm-equation candidates: powers of a chosen norm
   uniformizer times a unit whose residue is an `e`th power.  Choosing the
   uniformizer itself in the norm image avoids hiding its unit factor in the
   residue obstruction. -/
def chapter11TameNormEquationSet
    {K k : Type*} [Field K] [Field k]
    (vK : AddValuation K (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k) (πK : K) (e : ℕ) : Set K :=
  {a | ∃ r : ℤ, ∃ u : K,
    u ∈ chapter11ResidueConditionSet vK ρK
      (chapter11ResidueUnitPowerImage k e) ∧
      a = πK ^ r * u}

/- The norm image of units already lying in the base field. -/
def chapter11BaseUnitNormImage
    (K L : Type*) [Field K] [Field L] [Algebra K L] (e : ℕ) : Set K :=
  Set.range (fun u : Kˣ => (u : K) ^ e)

/- The elementary valuation coordinate in tame total ramification is
   surjective, although a particular target unit may still have a residue
   obstruction. -/
theorem chapter11_tame_total_norm_valuation_coordinate_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hfres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hext = 1)
    (πL : L) (hπ : chapter11IsUniformizer vL πL) (r : ℤ) :
    ∃ x : L, x ≠ 0 ∧ vK (Algebra.norm K x) = (r : WithTop ℤ) := by
  sorry

/- In the tame totally ramified situation, the valuation and residue-unit
   conditions together characterize the nonzero norm equations. -/
theorem chapter11_tame_total_norm_equation_iff
    (K L k : Type*) [Field K] [Field L] [Field k] [Fintype k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (he : 0 < e) (htame : chapter11TameAtResidueCharacteristic e p)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1))
    (hdegree : Module.finrank K L = e)
    (hfres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hext = 1)
    (πK : K) (hπK : chapter11IsUniformizer vK πK)
    (πL : L) (hπL : chapter11IsUniformizer vL πL)
    (hnormπ : Algebra.norm K πL = πK)
    (a : K) (ha : a ≠ 0) :
    chapter11NormEquationSolution K L a ↔
      a ∈ chapter11TameNormEquationSet vK ρK πK e := by
  sorry

/- A Kummer polynomial records the example in which a totally ramified
   uniformizer is an `e`th root of the base uniformizer. -/
def chapter11KummerPolynomial {K : Type*} [Field K] (π : K) (e : ℕ) : K[X] :=
  Polynomial.X ^ e - Polynomial.C π

/- All `e`th roots of unity in a chosen algebraic closure already come from
   the base field; this is the formal version of `μ_e ⊂ K`. -/
def chapter11ContainsEThRootsOfUnity
    (K E : Type*) [Field K] [Field E] [Algebra K E] (e : ℕ) : Prop :=
  ∀ ζ : E, ζ ^ e = 1 → ∃ z : K, algebraMap K E z = ζ

/- The constant coefficient of the Kummer polynomial gives the norm sign. -/
theorem chapter11_kummer_uniformizer_norm
    (K L E : Type*) [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [IsAlgClosed E] [FiniteDimensional K L] (π : K) (root : L) (e : ℕ)
    (hroots : chapter11ContainsEThRootsOfUnity K E e)
    (hminpoly : minpoly K root = chapter11KummerPolynomial π e)
    (hdegree : Module.finrank K L = e) :
    Algebra.norm K root = (-1 : K) ^ (e + 1) * π := by
  have hrootint : IsIntegral K root := IsIntegral.of_finite K root
  have htop : K⟮root⟯ = ⊤ := by
    apply (Field.primitive_element_iff_minpoly_natDegree_eq K root).2
    rw [hminpoly, chapter11KummerPolynomial, natDegree_X_pow_sub_C, hdegree]
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop' hrootint htop
  have hgen : pb.gen = root := by
    simpa [pb] using (PowerBasis.ofAdjoinEqTop'_gen hrootint htop)
  have hdim : pb.dim = e := by
    simp [pb, hminpoly, chapter11KummerPolynomial]
  have hepos : 0 < e := by
    rw [← hdim]
    exact PowerBasis.dim_pos pb
  have hnorm := PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hgen, hminpoly, hdim] at hnorm
  simpa [chapter11KummerPolynomial, hepos.ne', pow_succ, mul_assoc] using hnorm

/- Norms of elements embedded from the base field are powers by the extension
   degree. -/
theorem chapter11_norm_of_base_unit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (e : ℕ)
    (hdegree : Module.finrank K L = e) (u : K) :
    Algebra.norm K (algebraMap K L u) = u ^ e := by
  simpa [hdegree] using (Algebra.norm_algebraMap (R := K) (S := L) u)

/- The base-unit formula gives an inclusion in the full unit norm image; it
   does not identify that image with the base-field power image. -/
-- STATEMENT_NEEDS_UPDATE: `chapter11BaseUnitNormImage` ranges over all field units `Kˣ`, while the target `chapter11NormImage ... 0` only ranges over valuation-ring units in `L`; no hypothesis restricts a source unit to `U^0_K`.  Replace the source set by the valuation-ring unit group (or add that membership premise) before asserting the inclusion.
theorem chapter11_base_unit_norm_image_subset
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (hdegree : Module.finrank K L = e) :
    chapter11BaseUnitNormImage K L e ⊆ chapter11NormImage K L vL 0 := by
  sorry

/- The finite-residue tame quotient is the residue-unit obstruction, with no
   additional valuation index because a norm of a uniformizer has valuation
   one. -/
theorem chapter11_tame_total_norm_unit_quotient_index
    (k : Type*) [Field k] [Fintype k] (e : ℕ) :
    Nat.card (kˣ ⧸ chapter11PowerSubgroup k e) =
      Nat.gcd e (Fintype.card k - 1) := by
  exact chapter11_tame_residue_power_quotient_index k e

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
