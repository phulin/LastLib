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

/- The unit factor contributed by a chosen uniformizer.  The quotient is the
   source's `c = N(π_L) / π_K`; the equation API below keeps it explicit. -/
def chapter11TameNormUniformizerFactor
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (πK : K) (πL : L) : K :=
  Algebra.norm K πL / πK

theorem chapter11_tame_norm_uniformizer_factor_spec
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (πK : K) (πL : L) (hπK : πK ≠ 0) :
    chapter11TameNormUniformizerFactor K L πK πL * πK = Algebra.norm K πL := by
  unfold chapter11TameNormUniformizerFactor
  field_simp [hπK]

/- The full set of tame norm-equation candidates: powers of a chosen
   uniformizer times a unit whose residue, after correcting by `c⁻ʳ`, is an
   `e`th power. -/
def chapter11TameNormEquationSet
    {K k : Type*} [Field K] [Field k]
    (vK : AddValuation K (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k) (πK c : K) (e : ℕ) : Set K :=
  {a | ∃ r : ℤ, ∃ u : K,
    u ∈ chapter11UnitFiltration vK 0 ∧
      u * c ^ (-r) ∈ chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitPowerImage k e) ∧
      a = πK ^ r * u}

/- The norm image of units already lying in the base field. -/
def chapter11BaseUnitNormImage
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (e : ℕ) : Set K :=
  Set.range (fun u : (chapter11ValuationRing vK)ˣ =>
    ((u : chapter11ValuationRing vK) : K) ^ e)

theorem chapter11_mem_base_unit_norm_image_iff
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (e : ℕ) (x : K) :
    x ∈ chapter11BaseUnitNormImage K vK e ↔
      ∃ u : (chapter11ValuationRing vK)ˣ,
        ((u : chapter11ValuationRing vK) : K) ^ e = x := Iff.rfl

/- The elementary valuation coordinate in tame total ramification is
   surjective, although a particular target unit may still have a residue
   obstruction.  The displayed norm-value hypothesis is the missing bridge
   from a chosen uniformizer to the valuation formula. -/
-- SOURCE_ISSUE: The source suppresses the norm-valuation compatibility of a
-- chosen extension uniformizer.  It is stated explicitly here because the
-- valuation branch interface alone does not determine the norm of `πL`.
theorem chapter11_tame_total_norm_valuation_coordinate_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πL : L) (hπ : chapter11IsUniformizer vL πL)
    (hnormπ : vK (Algebra.norm K πL) = (1 : WithTop ℤ)) (r : ℤ) :
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
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1))
    (hdegree : Module.finrank K L = e)
    (hfres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hext = 1)
    (πK : K) (hπK : chapter11IsUniformizer vK πK)
    (πL : L) (hπL : chapter11IsUniformizer vL πL)
    (c : K) (hc : c ∈ chapter11UnitFiltration vK 0)
    (hcdef : c = chapter11TameNormUniformizerFactor K L πK πL)
    (hnormπ : Algebra.norm K πL = c * πK)
    (a : K) (ha : a ≠ 0) :
    chapter11NormEquationSolution K L a ↔
      a ∈ chapter11TameNormEquationSet vK ρK πK c e := by
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
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (π : K) (root : L) (e : ℕ)
    (hminpoly : minpoly K root = chapter11KummerPolynomial π e)
    (hgenerates : Algebra.adjoin K ({root} : Set L) = ⊤)
    (hdegree : Module.finrank K L = e) :
    Algebra.norm K root = (-1 : K) ^ (e + 1) * π := by
  sorry

/- Norms of elements embedded from the base field are powers by the extension
   degree. -/
theorem chapter11_norm_of_base_unit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (e : ℕ)
    (hdegree : Module.finrank K L = e) (u : K) :
    Algebra.norm K (algebraMap K L u) = u ^ e := by
  sorry

/- The base-unit formula gives an inclusion in the full unit norm image; it
   does not identify that image with the base-field power image.  The source
   units are restricted to the valuation-ring unit group so the target really
   is a zeroth unit layer. -/
theorem chapter11_base_unit_norm_image_subset
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (hscale : chapter11ValuationScaling vK vL e)
    (hdegree : Module.finrank K L = e) :
    chapter11BaseUnitNormImage K vK e ⊆ chapter11NormImage K L vL 0 := by
  sorry

/- The finite-residue tame quotient is the residue-unit obstruction, with no
   additional valuation index because a norm of a uniformizer has valuation
   one. -/
theorem chapter11_tame_total_norm_unit_quotient_index
    (k : Type*) [Field k] [Fintype k] (e : ℕ) :
    Nat.card (kˣ ⧸ chapter11PowerSubgroup k e) =
      Nat.gcd e (Fintype.card k - 1) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
