import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section04TheMultiplicativePicture

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial

/-! ## 12.5. Nearby polynomials define the same extension -/

/-- The degree comparison used after applying Krasner's lemma: the generated
field inclusion and the common polynomial degree force equality. -/
theorem chapter12_nearby_root_has_same_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f g : K[X]) (α β : L) (d : ℕ)
    (hf_monic : f.Monic) (hf_irreducible : Irreducible f)
    (hf_separable : f.Separable) (hf_degree : f.natDegree = d)
    (hαroot : aeval α f = 0)
    (hg_monic : g.Monic) (hg_degree : g.natDegree = d)
    (hβroot : aeval β g = 0)
    (hcontain : IntermediateField.adjoin K ({α} : Set L) ≤
      IntermediateField.adjoin K ({β} : Set L)) :
    Irreducible g ∧
      IntermediateField.adjoin K ({α} : Set L) =
        IntermediateField.adjoin K ({β} : Set L) := by
  sorry

/-- Local constancy in the fixed-degree monic coefficient space.  The
conclusion is stated for every root available in the chosen algebraic
overfield; the matched-root argument gives the displayed field isomorphism. -/
theorem chapter12_local_constancy_of_generated_field
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedField L] [NormedAlgebra K L]
    [FiniteDimensional K L]
    (f : K[X]) (α : L) (d : ℕ)
    (hf_monic : f.Monic) (hf_irreducible : Irreducible f)
    (hf_separable : f.Separable) (hf_degree : f.natDegree = d)
    (hroot : aeval α f = 0)
    (hsplits : (f.map (algebraMap K L)).Splits) :
    ∃ U : Set (Fin d → K), IsOpen U ∧
      chapter12CoefficientVector d f ∈ U ∧
      ∀ b : Fin d → K, b ∈ U →
        let g := chapter12MonicPolynomial d b
        Irreducible g ∧
          (g.map (algebraMap K L)).Splits ∧
          ∀ β : L, aeval β g = 0 →
            Nonempty
              (IntermediateField.adjoin K ({α} : Set L) ≃ₐ[K]
                IntermediateField.adjoin K ({β} : Set L)) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
