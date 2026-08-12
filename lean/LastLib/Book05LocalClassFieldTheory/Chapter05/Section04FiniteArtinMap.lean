import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.Discrete
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section03ClassFormation

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

/-!
### 5.4. Definition of the finite Artin map
-/

/- LOCAL_DEPENDENCY_GUESS: this is the book-facing output of the cap-product
isomorphism after the canonical degree `-2`/`H₁` and degree-zero norm bridges
are composed.  The construction is named independently so later kernel and
functoriality lemmas can use it. -/
noncomputable def chapter05FiniteArtinQuotientEquiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    chapter05NormQuotient K L ≃*
      chapter05Abelianization (Gal(L / K)) := by
  sorry

def chapter05FiniteArtinMap
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Kˣ →* chapter05Abelianization (Gal(L / K)) :=
  (chapter05FiniteArtinQuotientEquiv D).toMonoidHom.comp
    (QuotientGroup.mk' (chapter05NormSubgroup K L))

theorem chapter05FiniteArtinMap_kernel
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    (chapter05FiniteArtinMap D).ker = chapter05NormSubgroup K L := by
  sorry

theorem chapter05FiniteArtinMap_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Function.Surjective (chapter05FiniteArtinMap D) := by
  sorry

theorem chapter05FiniteArtinMap_induced_quotient
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    (chapter05FiniteArtinQuotientEquiv D).toMonoidHom.comp
        (QuotientGroup.mk' (chapter05NormSubgroup K L)) =
      chapter05FiniteArtinMap D := by
  rfl

noncomputable def chapter05FiniteArtinMap_quotient_isomorphism
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    chapter05NormQuotient K L ≃*
      chapter05Abelianization (Gal(L / K)) :=
  chapter05FiniteArtinQuotientEquiv D

theorem chapter05FiniteNormQuotient
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Finite (chapter05NormQuotient K L) :=
  Finite.of_surjective (chapter05FiniteArtinQuotientEquiv D).symm
    (chapter05FiniteArtinQuotientEquiv D).symm.surjective

theorem chapter05FiniteArtinMap_continuous
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [TopologicalSpace Kˣ]
    [TopologicalSpace (chapter05Abelianization (Gal(L / K)))]
    (D : Chapter05LocalClassFormationData K L)
    (hquot : Continuous
      (QuotientGroup.mk' (chapter05NormSubgroup K L) :
        Kˣ → chapter05NormQuotient K L))
    (he : Continuous
      (chapter05FiniteArtinQuotientEquiv D :
        chapter05NormQuotient K L →
          chapter05Abelianization (Gal(L / K)))) :
    Continuous (chapter05FiniteArtinMap D) := by
  sorry

theorem chapter05FiniteArtinMap_continuous_of_open_kernel
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    [Finite (chapter05Abelianization (Gal(L / K)))]
    [TopologicalSpace (chapter05Abelianization (Gal(L / K)))]
    [DiscreteTopology (chapter05Abelianization (Gal(L / K)))]
    (D : Chapter05LocalClassFormationData K L)
    (hopen : IsOpen (chapter05NormSubgroup K L : Set Kˣ)) :
    Continuous (chapter05FiniteArtinMap D) := by
  sorry

theorem chapter05FiniteArtinMap_surjective_on_finite_level
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Function.Surjective (chapter05FiniteArtinMap_quotient_isomorphism D) := by
  exact (chapter05FiniteArtinQuotientEquiv D).surjective

theorem chapter05_reverse_cyclic_generator_inverts
    {G A : Type*} [Group G] [CommGroup A] (f : G →* A) (g : G) :
    f g⁻¹ = (f g)⁻¹ := by
  simp

/- The local-field topology result used in the source is isolated as a
bridge: once the norm quotient map is known to be continuous (equivalently,
once the open norm subgroup has been proved), continuity of reciprocity is
the displayed composition above. -/
structure Chapter05OpenNormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [TopologicalSpace Kˣ] where
  isOpen : IsOpen (chapter05NormSubgroup K L : Set Kˣ)

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
