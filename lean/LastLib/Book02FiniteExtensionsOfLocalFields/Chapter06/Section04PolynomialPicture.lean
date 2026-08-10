import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section03CompatibilityInTowers
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

/-! ## 6.4. A polynomial picture -/

/-
The data of an irreducible separable residue polynomial and a monic lift over
`ℤ_[p]`.  The explicit reduction equality records which lift is being used.
-/
def chapter06PadicPolynomialLift
    (p f : ℕ) [Fact p.Prime] (gbar : (ZMod p)[X])
    (g : (PadicInt p)[X]) : Prop :=
  gbar.Monic ∧ g.Monic ∧
    g.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = gbar ∧
    Irreducible gbar ∧ gbar.Separable ∧ gbar.natDegree = f

/- A residue element is a root of the displayed residue polynomial. -/
def chapter06ResidueRootOfPolynomial
    {B l : Type*} (p : ℕ) [Fact p.Prime] [CommRing B] [Field l]
    [Algebra (ZMod p) l] (res : B →+* l) (gbar : (ZMod p)[X])
    (θ : B) : Prop :=
  eval₂ (algebraMap (ZMod p) l) (res θ) gbar = 0

/-
An irreducible residue polynomial with a monic `p`-adic lift gives the
unramified profile predicted by the book.  The generation and degree
hypotheses make the chosen root the intended field generator.
-/
theorem chapter06_padic_irreducible_lift_is_unramified
    (p f : ℕ) [Fact p.Prime] {L : Type*} [Field L]
    [Algebra (Padic p) L] [FiniteDimensional (Padic p) L]
    [Algebra (PadicInt p) L]
    [IsScalarTower (PadicInt p) (Padic p) L]
    (gbar : (ZMod p)[X]) (g : (PadicInt p)[X]) (θ : L)
    (hlift : chapter06PadicPolynomialLift p f gbar g)
    (hroot : eval₂ (algebraMap (PadicInt p) L) θ g = 0)
    (hgenerates : Algebra.adjoin (Padic p) ({θ} : Set L) = ⊤)
    (hdegree : Module.finrank (Padic p) L = f) :
    ∃ profile : Chapter10FiniteExtensionProfile,
      profile.degree = f ∧ profile.ramificationIndex = 1 ∧
        profile.residueDegree = f ∧ Chapter10Unramified profile := by
  sorry

/- The residue of the chosen root is acted on by `p`-power Frobenius. -/
theorem chapter06_padic_residue_frobenius_on_root
    (p : ℕ) [Fact p.Prime] {l : Type*} [Field l] [Fintype l]
    [Algebra (ZMod p) l] [Algebra.IsAlgebraic (ZMod p) l]
    (θbar : l) :
    chapter06ArithmeticFrobenius (ZMod p) l θbar = θbar ^ p := by
  sorry

/- In a Henselian unramified situation, the residue Frobenius has exactly one
    lift in the Galois group; this is the uniqueness used for a lifted root. -/
theorem chapter06_henselian_residue_frobenius_lift_unique
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) :
    ∃! σ : Gal(L/K),
      D.reduction σ = chapter06ArithmeticFrobenius k l := by
  exact chapter06_unramified_arithmetic_frobenius_unique D

/-
The canonical statement about a lifted root is a residue congruence.  The
literal equality below is intentionally a separate, choice-dependent
predicate; it is not silently identified with the residue statement.
-/
def chapter06ResidueFrobeniusCongruence
    {B l L : Type*} [CommRing B] [Field l] [Field L]
    [Algebra B L] (res : B →+* l) (σB : B ≃+* B) (σL : L ≃+* L)
    (τ : l ≃+* l) (θ : B) : Prop :=
  res (σB θ) = τ (res θ)

/- The noncanonical literal root formula `σ(θ) = θ^p`. -/
def chapter06LiteralRootPowerEquality
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (σB : B ≃+* B) (σL : L ≃+* L) (θ : B) (p : ℕ) : Prop :=
  σL (algebraMap B L (σB θ)) = (algebraMap B L θ) ^ p

/- Compatibility of an automorphism of an integral model with its field action. -/
def chapter06IntegralModelAutomorphismCompatibility
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (σB : B ≃+* B) (σL : L ≃+* L) : Prop :=
  ∀ x : B, algebraMap B L (σB x) = σL (algebraMap B L x)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
