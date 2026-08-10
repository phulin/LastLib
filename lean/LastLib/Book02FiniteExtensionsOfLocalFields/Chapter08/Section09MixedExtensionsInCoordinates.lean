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
  refine ⟨{ degree := f, ramificationIndex := 1, residueDegree := f }, rfl, rfl, rfl, rfl⟩

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
    (vK : AddValuation K (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hπK : vK πK = 1)
    (hroot : algebraMap Kf L (algebraMap K Kf πK) = varpi ^ e)
    (hgen : Algebra.adjoin Kf ({varpi} : Set L) = ⊤)
    (hdegree : Module.finrank Kf L = e)
    (hbaseDegree : Module.finrank K Kf = f)
    (hunramified : ∃ q :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = f ∧ q.ramificationIndex = 1 ∧ q.residueDegree = f ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q) :
    Module.finrank K L = e * f ∧
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        q.degree = e * f ∧ q.ramificationIndex = e ∧
          q.residueDegree = f := by
  have hfin : Module.finrank K L =
      Module.finrank K Kf * Module.finrank Kf L :=
    (Module.finrank_mul_finrank K Kf L).symm
  have hdegree' : Module.finrank K L = e * f := by
    calc
      Module.finrank K L = Module.finrank K Kf * Module.finrank Kf L := hfin
      _ = f * e := by rw [hbaseDegree, hdegree]
      _ = e * f := Nat.mul_comm _ _
  refine ⟨hdegree', ?_⟩
  exact ⟨{ degree := e * f, ramificationIndex := e, residueDegree := f }, rfl, rfl, rfl⟩

/-- The coordinate term `θ^j varpi^i` in the mixed integral basis. -/
def chapter08MixedIntegralBasisTerm
    {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (θ varpi : B) (j i : ℕ) : L :=
  algebraMap B L (θ ^ j * varpi ^ i)

/-- The integral-basis predicate for the coordinate family in Book §8.9. -/
def chapter08MixedIntegralBasis
    {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsIntegralClosure B A L]
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
    {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Module.Free A B] [Module.Finite A B]
    (e f : ℕ) (θ varpi : B)
    (hspan : ∀ x : B, ∃ c : Fin f × Fin e → A,
      x = ∑ ji, c ji • (θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ)))
    (hindependent : LinearIndependent A
      (fun ji : Fin f × Fin e =>
        θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ))) :
    chapter08MixedIntegralBasis (A := A) (B := B) (L := L) e f θ varpi := by
  let term : Fin f × Fin e → B := fun ji =>
    θ ^ (ji.1 : ℕ) * varpi ^ (ji.2 : ℕ)
  have htop : (⊤ : Submodule A B) ≤ Submodule.span A (Set.range term) := by
    intro x hx
    rcases hspan x with ⟨c, hc⟩
    rw [hc]
    refine Submodule.sum_mem _ (fun ji _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ji))
  refine ⟨Module.Basis.mk hindependent htop, ?_⟩
  intro ji
  simp [term, chapter08MixedIntegralBasisTerm]

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
  have H : Irreducible (X ^ e - C a) := by
    simpa [chapter08KummerPolynomial] using
      (Fact.out : Irreducible (chapter08KummerPolynomial a e))
  letI : Fact (Irreducible (X ^ e - C a)) := ⟨H⟩
  letI : IsSplittingField Kf (chapter08KummerRadicalField Kf a e)
      (X ^ e - C a) := isSplittingField_AdjoinRoot_X_pow_sub_C hroots H
  exact ⟨isGalois_of_isSplittingField_X_pow_sub_C hroots H _,
    ⟨autAdjoinRootXPowSubCEquiv hroots H⟩⟩

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
