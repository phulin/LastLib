import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section01WhyFrobeniusIsCanonical
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import Mathlib.NumberTheory.Padics.RingHoms

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

/-! ## 6.4. A polynomial picture -/

/-
The data of an irreducible residue polynomial and a monic lift over `ℤ_[p]`.
Irreducibility over the finite residue field already supplies separability; the
explicit reduction equality records which lift is being used.
-/
def chapter06PadicPolynomialLift
    (p f : ℕ) [Fact p.Prime] (gbar : (ZMod p)[X])
    (g : (PadicInt p)[X]) : Prop :=
  g.Monic ∧
    g.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = gbar ∧
    Irreducible gbar ∧ gbar.natDegree = f

/- An irreducible polynomial over the finite residue field is separable. -/
theorem chapter06_padic_residue_polynomial_is_separable
    (p : ℕ) [Fact p.Prime] (gbar : (ZMod p)[X])
    (hirr : Irreducible gbar) : gbar.Separable := by
  exact PerfectField.separable_of_irreducible hirr

/- A residue element is a root of the displayed residue polynomial. -/
def chapter06ResidueRootOfPolynomial
    {B l : Type*} (p : ℕ) [Fact p.Prime] [CommRing B] [Field l]
    [Algebra (ZMod p) l] (res : B →+* l) (gbar : (ZMod p)[X])
    (θ : B) : Prop :=
  eval₂ (algebraMap (ZMod p) l) (res θ) gbar = 0

/-
SOURCE_ISSUE: The source suppresses the valuation on the generated field and
the identification of its integral closure with a valuation ring.  A bare
numerical profile is not enough to conclude that the displayed extension is
unramified, so the corrected interface below records the valuation branch and
realizes the profile by that branch.  The stronger generic bridge is supplied
by the earlier `chapter10_unramified_lift_profile` interface.
-/

/-
An irreducible residue polynomial with a monic `p`-adic lift gives the
unramified profile predicted by the book.  The generation and degree
hypotheses make the chosen root the intended field generator.
-/
theorem chapter06_padic_irreducible_lift_is_unramified
    (p f : ℕ) [Fact p.Prime] {L ΓK ΓL : Type*} [Field L]
    [Algebra (Padic p) L] [FiniteDimensional (Padic p) L]
    [Algebra (PadicInt p) L]
    [IsScalarTower (PadicInt p) (Padic p) L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (gbar : (ZMod p)[X]) (g : (PadicInt p)[X]) (θ : L)
    (hlift : chapter06PadicPolynomialLift p f gbar g)
    (hroot : eval₂ (algebraMap (PadicInt p) L) θ g = 0)
    (hgenerates : Algebra.adjoin (Padic p) ({θ} : Set L) = ⊤)
    (hdegree : Module.finrank (Padic p) L = f)
    (hres : ∃ e : IsLocalRing.ResidueField (PadicInt p) ≃+* ZMod p,
      e.toRingHom.comp (IsLocalRing.residue (PadicInt p)) =
        (PadicInt.toZMod : PadicInt p →+* ZMod p))
    (v : Valuation (Padic p) ΓK) (w : Valuation L ΓL)
    (hA : v.Integers (PadicInt p))
    (hext : v.IsEquiv (w.comap (algebraMap (Padic p) L))) :
    ∃ d : Chapter10HeterogeneousExtensionData v w hext,
      ∃ profile : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d profile ∧
          Irreducible g ∧ profile.degree = f ∧
          profile.ramificationIndex = 1 ∧ profile.residueDegree = f ∧
          Chapter10Unramified profile ∧
          (g.map (PadicInt.toZMod : PadicInt p →+* ZMod p)).Separable := by
  rcases hlift with ⟨hgmonic, hmap, hirr, hdegree'⟩
  have hred : Chapter10IrreducibleSeparableReduction
      (PadicInt.toZMod : PadicInt p →+* ZMod p) g f := by
    dsimp [Chapter10IrreducibleSeparableReduction]
    refine ⟨hgmonic, ?_, ?_, ?_, ?_⟩
    · simpa [hmap] using hgmonic.map (PadicInt.toZMod : PadicInt p →+* ZMod p)
    · simpa [hmap] using hdegree'
    · simpa [hmap] using hirr
    · simpa [hmap] using chapter06_padic_residue_polynomial_is_separable p gbar hirr
  obtain ⟨d, profile, hreal, hirr', hdegree'', he, hf, hunram, _hbranch, hsep⟩ :=
    chapter10_unramified_lift_profile
      (A := PadicInt p) (K := Padic p) (L := L) (k := ZMod p)
      (res := PadicInt.toZMod) (P := g) f hred hres θ hroot hgenerates
      hdegree v w hA hext
  exact ⟨d, profile, hreal, hirr', hdegree'', he, hf, hunram, hsep⟩

/- The valuation-level form with the suppressed local hypotheses restored. -/
theorem chapter06_padic_unramified_lift_profile
    {L ΓK ΓL : Type*} (p f : ℕ) [Fact p.Prime]
    [Field L] [Algebra (Padic p) L]
    [FiniteDimensional (Padic p) L]
    [Algebra (PadicInt p) L]
    [IsScalarTower (PadicInt p) (Padic p) L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (res : PadicInt p →+* ZMod p) (P : (PadicInt p)[X])
    (hred : Chapter10IrreducibleSeparableReduction res P f)
    (hres : ∃ e : IsLocalRing.ResidueField (PadicInt p) ≃+* ZMod p,
      e.toRingHom.comp (IsLocalRing.residue (PadicInt p)) = res)
    (α : L) (hroot : eval₂ (algebraMap (PadicInt p) L) α P = 0)
    (hgen : Algebra.adjoin (Padic p) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (Padic p) L = f)
    (v : Valuation (Padic p) ΓK) (w : Valuation L ΓL)
    (hA : v.Integers (PadicInt p))
    (hext : v.IsEquiv (w.comap (algebraMap (Padic p) L))) :
    ∃ d : Chapter10HeterogeneousExtensionData v w hext,
      ∃ profile : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d profile ∧
          Irreducible P ∧ profile.degree = f ∧
          profile.ramificationIndex = 1 ∧ profile.residueDegree = f ∧
          Chapter10Unramified profile ∧ (P.map res).Separable := by
  obtain ⟨d, profile, hreal, hirr, hdegree', he, hf, hunram, _hbranch, hsep⟩ :=
    chapter10_unramified_lift_profile
      (A := PadicInt p) (K := Padic p) (L := L) (k := ZMod p)
      (res := res) (P := P) f hred hres α hroot hgen
      hdegree v w hA hext
  exact ⟨d, profile, hreal, hirr, hdegree', he, hf, hunram, hsep⟩

/- The residue of the chosen root is acted on by `p`-power Frobenius. -/
theorem chapter06_padic_residue_frobenius_on_root
    (p : ℕ) [Fact p.Prime] {l : Type*} [Field l] [Fintype l]
    [Algebra (ZMod p) l] [Algebra.IsAlgebraic (ZMod p) l]
    (θbar : l) :
    chapter06ArithmeticFrobenius (ZMod p) l θbar = θbar ^ p := by
  simp [chapter06ArithmeticFrobenius, ZMod.card] 

/- A lifted polynomial root reduces to a root of the reduced polynomial. -/
theorem chapter06_residue_of_padic_lifted_root
    (p : ℕ) [Fact p.Prime] {B l : Type*} [CommRing B] [Field l]
    [Algebra (ZMod p) l]
    (res : B →+* l) (coeffLift : PadicInt p →+* B)
    (gbar : (ZMod p)[X]) (g : (PadicInt p)[X]) (θ : B)
    (hres : res.comp coeffLift =
      (algebraMap (ZMod p) l : ZMod p →+* l).comp
        (PadicInt.toZMod : PadicInt p →+* ZMod p))
    (hmap : g.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = gbar)
    (hroot : eval₂ coeffLift θ g = 0) :
    chapter06ResidueRootOfPolynomial p res gbar θ := by
  change eval₂ (algebraMap (ZMod p) l) (res θ) gbar = 0
  rw [← hmap, eval₂_map, ← hres, ← hom_eval₂, hroot, map_zero]

/-
The canonical statement about a lifted root is a residue congruence.  The
literal equality below is intentionally a separate, choice-dependent
predicate; it is not silently identified with the residue statement.
-/
def chapter06ResidueFrobeniusCongruence
    {B l : Type*} [CommRing B] [Field l]
    (res : B →+* l) (σB : B ≃+* B)
    (τ : l ≃+* l) (θ : B) : Prop :=
  res (σB θ) = τ (res θ)

/- The noncanonical literal root formula `σ(θ) = θ^p`. -/
def chapter06LiteralRootPowerEquality
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (σL : L ≃+* L) (θ : B) (p : ℕ) : Prop :=
  σL (algebraMap B L θ) = (algebraMap B L θ) ^ p

/- Compatibility of an automorphism of an integral model with its field action. -/
def chapter06IntegralModelAutomorphismCompatibility
    {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (σB : B ≃+* B) (σL : L ≃+* L) : Prop :=
  ∀ x : B, algebraMap B L (σB x) = σL (algebraMap B L x)

/- The concrete `p`-power form of the residue congruence. -/
theorem chapter06_padic_residue_frobenius_congruence_iff
    (p : ℕ) [Fact p.Prime] {B l : Type*} [CommRing B] [Field l]
    [Fintype l] [Algebra (ZMod p) l]
    [Algebra.IsAlgebraic (ZMod p) l]
    (res : B →+* l) (σB : B ≃+* B) (θ : B) :
    chapter06ResidueFrobeniusCongruence res σB
        (chapter06ArithmeticFrobeniusRingEquiv (ZMod p) l) θ ↔
      res (σB θ) = (res θ) ^ p := by
  simp [chapter06ResidueFrobeniusCongruence,
    chapter06ArithmeticFrobeniusRingEquiv, chapter06ArithmeticFrobenius, ZMod.card]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
