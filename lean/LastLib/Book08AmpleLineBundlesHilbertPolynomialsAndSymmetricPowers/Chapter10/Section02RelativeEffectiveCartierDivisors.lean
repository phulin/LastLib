import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Dependencies
import Mathlib.RingTheory.MvPolynomial

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits SheafOfModules
open scoped AlgebraicGeometry

universe u

/-! ## 10.2. Relative effective Cartier divisors -/

def Chapter10LocallyRegularPrincipal {X : Scheme}
    (D : Chapter10ClosedSubscheme X) : Prop :=
  ∀ U : X.affineOpens, ∃ a : Γ(X, U),
    D.ideal U = Ideal.span {a} ∧ IsRegular a

structure Chapter10EffectiveCartierDivisor (X : Scheme) where
  ideal : Chapter10ClosedSubscheme X
  locallyRegularPrincipal : Chapter10LocallyRegularPrincipal ideal

def chapter10EffectiveCartierDivisorAsClosedSubscheme {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) : Chapter10ClosedSubscheme X :=
  D.ideal

theorem chapter10_effectiveCartierDivisor_ext {X : Scheme}
    (D E : Chapter10EffectiveCartierDivisor X) (h : D.ideal = E.ideal) : D = E := by
  sorry

/-!
The ideal-sheaf-to-line-bundle comparison and the vanishing ideal of a
section are isolated as a named interface.  This is the natural missing
Cartier/Picard construction in the pinned snapshot, and makes the later
statements express the textbook's canonical section without pretending that
the construction is already present in Mathlib.
-/

/- LOCAL_DEPENDENCY_GUESS (10.2): `Chapter10IdealDualAPI` and
`Chapter10SectionVanishingIdealAPI` stand for the missing construction of
`𝓘_D⁻¹` and the ideal of a section of an invertible sheaf. -/

class Chapter10SectionVanishingIdealAPI (X : Scheme) where
  vanishingIdeal : ∀ {L : Chapter10LineBundle X},
    Chapter10LineBundleSection L → Chapter10ClosedSubscheme X

def chapter10SectionVanishingIdeal {X : Scheme} [Chapter10SectionVanishingIdealAPI X]
    {L : Chapter10LineBundle X} (s : Chapter10LineBundleSection L) :
    Chapter10ClosedSubscheme X :=
  Chapter10SectionVanishingIdealAPI.vanishingIdeal s

structure Chapter10CartierLineBundleData {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10SectionVanishingIdealAPI X] [Chapter10IdealDualAPI X] where
  lineBundle : Chapter10LineBundle X
  lineBundle_is_inverseIdeal :
    lineBundle = Chapter10IdealDualAPI.inverseIdeal D.ideal
  canonicalSection : Chapter10LineBundleSection lineBundle
  vanishingIdeal_eq : chapter10SectionVanishingIdeal canonicalSection = D.ideal

theorem chapter10_effectiveCartier_has_lineBundle {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10SectionVanishingIdealAPI X] [Chapter10IdealDualAPI X] :
    Nonempty (Chapter10CartierLineBundleData D) := by
  sorry

noncomputable def chapter10OofD {X : Scheme} (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10SectionVanishingIdealAPI X] [Chapter10IdealDualAPI X] : Chapter10LineBundle X :=
  (Classical.choice (chapter10_effectiveCartier_has_lineBundle D)).lineBundle

noncomputable def chapter10OofD_section {X : Scheme} (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10SectionVanishingIdealAPI X] [Chapter10IdealDualAPI X] :
    Chapter10LineBundleSection (chapter10OofD D) :=
  (Classical.choice (chapter10_effectiveCartier_has_lineBundle D)).canonicalSection

theorem chapter10OofD_section_vanishingIdeal {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10SectionVanishingIdealAPI X] [Chapter10IdealDualAPI X] :
    chapter10SectionVanishingIdeal (chapter10OofD_section D) = D.ideal := by
  sorry

theorem chapter10OofD_is_inverseIdeal {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10SectionVanishingIdealAPI X] [Chapter10IdealDualAPI X] :
    chapter10OofD D = Chapter10IdealDualAPI.inverseIdeal D.ideal := by
  sorry

structure Chapter10CartierExactSequence {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) where
  OminusD : X.Modules
  OD : X.Modules
  inclusion : OminusD ⟶ chapter10StructureSheaf X
  quotient : chapter10StructureSheaf X ⟶ OD
  comp_zero : inclusion ≫ quotient = 0
  mono_inclusion : Mono inclusion
  epi_quotient : Epi quotient
  exact : (ShortComplex.mk inclusion quotient comp_zero).Exact

theorem chapter10_cartier_exact_sequence_exists {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) :
    Nonempty (Chapter10CartierExactSequence D) := by
  sorry

structure Chapter10RelativeEffectiveCartierDivisor {C T : Scheme}
    (c : C ⟶ T) (d : ℕ) where
  divisor : Chapter10EffectiveCartierDivisor C
  finiteLocallyFree :
    Chapter10FiniteLocallyFreeProfile (divisor.ideal.subschemeι ≫ c) d

theorem chapter10_relative_effectiveCartierDivisor_ext {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D E : Chapter10RelativeEffectiveCartierDivisor c d)
    (h : D.divisor.ideal = E.divisor.ideal) : D = E := by
  sorry

def chapter10RelativeDivisorProjection {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter10RelativeEffectiveCartierDivisor c d) : D.divisor.ideal.subscheme ⟶ T :=
  D.divisor.ideal.subschemeι ≫ c

theorem chapter10_relative_divisor_is_finiteLocallyFree {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter10RelativeEffectiveCartierDivisor c d) :
    Chapter10FiniteLocallyFreeProfile (chapter10RelativeDivisorProjection D) d :=
  D.finiteLocallyFree

theorem chapter10_relativeDivisor_degree {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter10RelativeEffectiveCartierDivisor c d) (t : T) :
    Chapter10FiberLength (chapter10RelativeDivisorProjection D) t = d := by
  exact D.finiteLocallyFree.rank t

/- SOURCE_ISSUE (10.2, "If `C → T` is flat, fiber length `d` plus the Cartier
condition implies finite local freeness"): fiberwise finite length and the
Cartier/local-flatness argument do not by themselves imply that the closed
subscheme is finite over a non-proper base.  The smallest correction is to add
properness of the divisor over `T` (equivalently, in the intended proper-curve
setting, assume the ambient curve is proper). -/

theorem chapter10_cartier_fiber_length_implies_finiteLocallyFree
    {C T : Scheme} (c : C ⟶ T) [Flat c]
    (D : Chapter10EffectiveCartierDivisor C) (d : ℕ)
    [IsProper (D.ideal.subschemeι ≫ c)]
    (hfiber : ∀ t : T,
      Scheme.Hom.finrank (D.ideal.subschemeι ≫ c) t = d) :
    Chapter10FiniteLocallyFreeProfile (D.ideal.subschemeι ≫ c) d := by
  sorry

/-!
The singular-curve warning is recorded by the standard affine node model.
The ideal generated by the two branches is the image of `(x,y)` in the node
ring and is explicitly required to be non-principal.
-/

abbrev chapter10NodePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

abbrev chapter10NodeRing (k : Type u) [Field k] :=
  chapter10NodePolynomialRing k ⧸
    Ideal.span ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
      Set (chapter10NodePolynomialRing k))

def chapter10NodeIdeal (k : Type u) [Field k] :
    Ideal (chapter10NodeRing k) :=
  Ideal.map (Ideal.Quotient.mk
      (Ideal.span ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
        Set (chapter10NodePolynomialRing k)))) <|
    Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (chapter10NodePolynomialRing k))

theorem chapter10_node_ideal_is_not_principal (k : Type u) [Field k] :
    ¬ ∃ a : chapter10NodeRing k,
      chapter10NodeIdeal k = Ideal.span ({a} : Set (chapter10NodeRing k)) := by
  sorry

def Chapter10NodePointLengthOneProfile (k : Type u) [Field k] : Prop :=
  Module.Finite k (chapter10NodeRing k ⧸ chapter10NodeIdeal k) ∧
    Module.Flat k (chapter10NodeRing k ⧸ chapter10NodeIdeal k) ∧
    Module.finrank k (chapter10NodeRing k ⧸ chapter10NodeIdeal k) = 1

theorem chapter10_node_point_has_length_one (k : Type u) [Field k] :
    Chapter10NodePointLengthOneProfile k := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
