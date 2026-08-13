import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Dependencies
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.MvPolynomial

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits SheafOfModules
open scoped AlgebraicGeometry

universe u

/-! ## 10.2. Relative effective Cartier divisors -/

def chapter10EffectiveCartierDivisorAsClosedSubscheme {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) : Chapter10ClosedSubscheme X :=
  D.ideal

/- LOCAL_DEPENDENCY_GUESS (10.2): the pinned Mathlib snapshot has the
  local-freeness predicate but not the inverse-line-bundle constructor for a
  Cartier divisor.  Restricting the operation to effective Cartier divisors
  records the weakest domain needed by the source's `𝓘_D⁻¹` construction. -/
class Chapter10IdealDualAPI (X : Scheme) where
  inverseIdeal : Chapter10EffectiveCartierDivisor X → Chapter10LineBundle X

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

class Chapter10SectionVanishingIdealAPI (X : Scheme) [Chapter10IdealDualAPI X] where
  vanishingIdeal : ∀ {L : Chapter10LineBundle X},
    Chapter10LineBundleSection L → Chapter10ClosedSubscheme X
  canonicalSection : ∀ D : Chapter10EffectiveCartierDivisor X,
    Chapter10LineBundleSection (Chapter10IdealDualAPI.inverseIdeal D)
  canonicalSection_vanishingIdeal : ∀ D : Chapter10EffectiveCartierDivisor X,
    vanishingIdeal (canonicalSection D) = D.ideal

def chapter10SectionVanishingIdeal {X : Scheme} [Chapter10IdealDualAPI X]
    [Chapter10SectionVanishingIdealAPI X]
    {L : Chapter10LineBundle X} (s : Chapter10LineBundleSection L) :
    Chapter10ClosedSubscheme X :=
  Chapter10SectionVanishingIdealAPI.vanishingIdeal s

structure Chapter10CartierLineBundleData {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] [Chapter10SectionVanishingIdealAPI X] where
  canonicalSection :
    Chapter10LineBundleSection (Chapter10IdealDualAPI.inverseIdeal D)
  canonicalSection_eq :
    canonicalSection = Chapter10SectionVanishingIdealAPI.canonicalSection D
  vanishingIdeal_eq : chapter10SectionVanishingIdeal canonicalSection = D.ideal

theorem chapter10_effectiveCartier_has_lineBundle {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] [Chapter10SectionVanishingIdealAPI X] :
    Nonempty (Chapter10CartierLineBundleData D) :=
  ⟨{ canonicalSection := Chapter10SectionVanishingIdealAPI.canonicalSection D
     canonicalSection_eq := rfl
     vanishingIdeal_eq := Chapter10SectionVanishingIdealAPI.canonicalSection_vanishingIdeal D }⟩

noncomputable def chapter10OofD {X : Scheme} (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] : Chapter10LineBundle X :=
  Chapter10IdealDualAPI.inverseIdeal D

noncomputable def chapter10OofD_section {X : Scheme} (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] [Chapter10SectionVanishingIdealAPI X] :
    Chapter10LineBundleSection (chapter10OofD D) :=
  Chapter10SectionVanishingIdealAPI.canonicalSection D

theorem chapter10OofD_section_vanishingIdeal {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] [Chapter10SectionVanishingIdealAPI X] :
    chapter10SectionVanishingIdeal (chapter10OofD_section D) = D.ideal := by
  exact Chapter10SectionVanishingIdealAPI.canonicalSection_vanishingIdeal D

def chapter10OofD_is_inverseIdeal {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] :
    Chapter10LineBundleIso (chapter10OofD D)
      (Chapter10IdealDualAPI.inverseIdeal D) :=
  chapter10_lineBundleIso_refl _

/-!
The quotient in the Cartier sequence is the pushforward of the structure
sheaf of the closed subscheme.  Using the canonical map induced by the
closed immersion prevents the exact-sequence witness from becoming an
unrelated short exact sequence merely carrying `D` as a parameter.
-/
noncomputable def chapter10CartierQuotientModule {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) : X.Modules :=
  (Scheme.Modules.pushforward D.ideal.subschemeι).obj
    (chapter10StructureSheaf D.ideal.subscheme)

noncomputable def chapter10CartierQuotient {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) :
    chapter10StructureSheaf X ⟶ chapter10CartierQuotientModule D :=
  SheafOfModules.unitToPushforwardObjUnit D.ideal.subschemeι.toRingCatSheafHom

noncomputable def chapter10CartierOminusD {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) : X.Modules :=
  kernel (chapter10CartierQuotient D)

noncomputable def chapter10CartierInclusion {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) :
    chapter10CartierOminusD D ⟶ chapter10StructureSheaf X :=
  kernel.ι (chapter10CartierQuotient D)

theorem chapter10_cartier_inclusion_comp_quotient {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) :
    chapter10CartierInclusion D ≫ chapter10CartierQuotient D = 0 :=
  kernel.condition _

structure Chapter10CartierExactSequence {X : Scheme}
    (D : Chapter10EffectiveCartierDivisor X) where
  comp_zero : chapter10CartierInclusion D ≫ chapter10CartierQuotient D = 0
  mono_inclusion : Mono (chapter10CartierInclusion D)
  epi_quotient : Epi (chapter10CartierQuotient D)
  exact : (ShortComplex.mk (chapter10CartierInclusion D)
    (chapter10CartierQuotient D) comp_zero).Exact

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

theorem chapter10_cartier_fiber_length_implies_finiteLocallyFree
    {C T : Scheme} (c : C ⟶ T) [Flat c] [LocallyOfFinitePresentation c] [QuasiCompact c]
    [QuasiSeparated c]
    (D : Chapter10EffectiveCartierDivisor C) (d : ℕ)
    [IsProper (D.ideal.subschemeι ≫ c)]
    (hfiber : ∀ t : T,
      Chapter10FiniteLocallyFreeProfile
        ((D.ideal.comap (c.fiberι t)).subschemeι ≫ c.fiberToSpecResidueField t) d)
    (hfiber_cartier : ∀ t : T,
      Chapter10LocallyRegularPrincipal
        (D.ideal.comap (c.fiberι t))) :
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
