import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section08PrimeToP_RadicalExtensions

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped BigOperators

/-! # 8.9. A mixed extension in coordinates -/

/-- A finite residue field of cardinality `q`. -/
def chapter08FiniteResidueFieldOfCardinality
    (k : Type*) [Field k] [Fintype k] (q : ℕ) : Prop :=
  Fintype.card k = q

/-- Book §8.9: the unramified stage has degree `f`, ramification index one,
and residue degree `f`. -/
theorem chapter08_unramified_stage_profile
    {K Kf : Type*} [Field K] [Field Kf] [Algebra K Kf]
    [FiniteDimensional K Kf]
    (f : ℕ) (hdegree : Module.finrank K Kf = f) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = f ∧ q.ramificationIndex = 1 ∧ q.residueDegree = f ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q := by
  sorry

/-- Book §8.9: adjoining a root of `varpi^e = π_K` over the unramified stage
produces the ramified degree-`e` stage. -/
theorem chapter08_ramified_stage_profile
    {K Kf L : Type*} [Field K] [Field Kf] [Field L]
    [Algebra K Kf] [Algebra Kf L] [Algebra K L]
    [IsScalarTower K Kf L]
    [FiniteDimensional K Kf] [FiniteDimensional Kf L]
    [FiniteDimensional K L]
    (e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (πK : K) (varpi : L)
    (hroot : algebraMap Kf L (algebraMap K Kf πK) = varpi ^ e)
    (hgen : Algebra.adjoin Kf ({varpi} : Set L) = ⊤)
    (hdegree : Module.finrank Kf L = e)
    (hbaseDegree : Module.finrank K Kf = f) :
    Module.finrank K L = e * f ∧
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        q.degree = e * f ∧ q.ramificationIndex = e ∧
          q.residueDegree = f := by
  sorry

/-- The coordinate term `θ^j varpi^i` in the mixed integral basis. -/
def chapter08MixedIntegralBasisTerm
    {A B L : Type*} [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Algebra B L]
    (θ varpi : B) (j i : ℕ) : L :=
  algebraMap B L (θ ^ j * varpi ^ i)

/-- The integral-basis predicate for the coordinate family in Book §8.9. -/
def chapter08MixedIntegralBasis
    {A B L : Type*} [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Algebra B L]
    (e f : ℕ) (θ varpi : B) : Prop :=
    ∃ b : Module.Basis (Fin f × Fin e) A B,
    ∀ ji : Fin f × Fin e,
      algebraMap B L (b ji) =
        chapter08MixedIntegralBasisTerm (A := A) (B := B) (L := L)
          θ varpi ji.1 ji.2

/-- Book §8.9: the two-stage power basis gives the displayed integral basis.
The spanning and independence hypotheses are the algebraic content of the
unramified residue basis and the Eisenstein power basis. -/
theorem chapter08_mixed_extension_has_integral_basis
    {A B L : Type*} [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Algebra B L] [Module.Free A B] [Module.Finite A B]
    (e f : ℕ) (θ varpi : B)
    (hspan : ∀ x : B, ∃ c : Fin f × Fin e → A,
      x = ∑ ji, c ji • (θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ)))
    (hindependent : LinearIndependent A
      (fun ji : Fin f × Fin e =>
        θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ))) :
    chapter08MixedIntegralBasis (A := A) (B := B) (L := L) e f θ varpi := by
  sorry

/-- The root-of-unity condition needed for the ramified stage to be Kummer
Galois over the unramified field. -/
def chapter08AllRelevantRootsOfUnity
    (K : Type*) [Field K] (e : ℕ) : Prop :=
  (primitiveRoots e K).Nonempty

/-- Book §8.9: if the relevant roots of unity lie in `K_f`, the ramified stage
is Galois over `K_f`. -/
theorem chapter08_mixed_ramified_stage_is_galois_when_roots_are_present
    {Kf : Type*} [Field Kf]
    {a : Kf} {e : ℕ} [NeZero e]
    [Fact (Irreducible (chapter08KummerPolynomial a e))]
    (hroots : chapter08AllRelevantRootsOfUnity Kf e) :
    IsGalois Kf (chapter08KummerRadicalField Kf a e) ∧
      Nonempty
        (rootsOfUnity e Kf ≃*
          (chapter08KummerRadicalField Kf a e ≃ₐ[Kf]
            chapter08KummerRadicalField Kf a e)) := by
  sorry

/-- The numerical data `(e,f)` for a mixed local extension. -/
def chapter08MixedExtensionProfile (e f : ℕ) : Prop :=
  0 < e ∧ 0 < f

/-- Book §8.9: normality is additional data beyond the numerical `(e,f)`
profile. -/
def chapter08MixedExtensionGaloisProfile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (e f : ℕ) : Prop :=
  chapter08MixedExtensionProfile e f ∧ IsGalois K L

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
