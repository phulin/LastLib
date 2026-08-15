import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.Discrete
import LastLib.Book05LocalClassFieldTheory.Chapter05.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section02TateHomology
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section03ClassFormation

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open CategoryTheory

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
  haveI : IsIso (D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) (-2)) :=
    chapter05_class_formation_top_isomorphism D (-2)
  let capIso :
      chapter05TateCohomology (⊤ : Subgroup (Gal(L / K)))
          (Rep.res (⊤ : Subgroup (Gal(L / K))).subtype
            (Rep.trivial ℤ (Gal(L / K)) ℤ)) (-2) ≅
        chapter05TateCohomology (⊤ : Subgroup (Gal(L / K)))
          (Rep.res (⊤ : Subgroup (Gal(L / K))).subtype
            (chapter05CoefficientRep K L)) 0 :=
    @asIso _ _ _ _ (D.capProduct.cap (⊤ : Subgroup (Gal(L / K))) (-2)) this
  let topToNorm :
      chapter05TateCohomology (⊤ : Subgroup (Gal(L / K)))
          (Rep.res (⊤ : Subgroup (Gal(L / K))).subtype
            (chapter05CoefficientRep K L)) 0 ≃+
        Additive (chapter05NormQuotient K L) :=
    (D.topRestriction.iso 0).toLinearEquiv.toAddEquiv.trans
      D.degreeZeroNorm
  let topMinusToNorm :
      chapter05TateCohomology (⊤ : Subgroup (Gal(L / K)))
          (Rep.res (⊤ : Subgroup (Gal(L / K))).subtype
            (Rep.trivial ℤ (Gal(L / K)) ℤ)) (-2) ≃+
        Additive (chapter05NormQuotient K L) :=
    capIso.toLinearEquiv.toAddEquiv.trans topToNorm
  let sourceToNorm :
      chapter05TateCohomology (Gal(L / K))
          (Rep.trivial ℤ (Gal(L / K)) ℤ) (-2) ≃+
        Additive (chapter05NormQuotient K L) :=
    ((D.topRestrictionTrivial.iso (-2)).symm.toLinearEquiv.toAddEquiv).trans
      topMinusToNorm
  let sourceToAbelianization :
      chapter05TateCohomology (Gal(L / K))
          (Rep.trivial ℤ (Gal(L / K)) ℤ) (-2) ≃+
        Additive (chapter05Abelianization (Gal(L / K))) :=
    (chapter05_tate_minus_two_is_homology (Gal(L / K))).toLinearEquiv.toAddEquiv.trans
      (chapter05H1AbelianizationIso (Gal(L / K)))
  let eAdd : Additive (chapter05NormQuotient K L) ≃+
      Additive (chapter05Abelianization (Gal(L / K))) :=
    sourceToNorm.symm.trans sourceToAbelianization
  let eMul : chapter05NormQuotient K L ≃*
      chapter05Abelianization (Gal(L / K)) :=
    eAdd.toMultiplicativeRight.trans
      (MulEquiv.toMultiplicative_toAdditive
        (G := chapter05Abelianization (Gal(L / K))))
  exact eMul

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
  ext x
  change chapter05FiniteArtinMap D x = 1 ↔ x ∈ chapter05NormSubgroup K L
  simp [chapter05FiniteArtinMap]

theorem chapter05FiniteArtinMap_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalClassFormationData K L) :
    Function.Surjective (chapter05FiniteArtinMap D) := by
  intro y
  obtain ⟨z, rfl⟩ := (chapter05FiniteArtinQuotientEquiv D).surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (chapter05NormSubgroup K L) z
  exact ⟨x, rfl⟩

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
  simpa [chapter05FiniteArtinMap] using he.comp hquot

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
  apply continuous_iff_continuousAt.2
  intro x
  rw [ContinuousAt, nhds_discrete (chapter05Abelianization (Gal(L / K))),
    Filter.tendsto_pure]
  refine Filter.mem_of_superset ((hopen.leftCoset x).mem_nhds ?_) ?_
  · exact ⟨1, (chapter05NormSubgroup K L).one_mem, by simp⟩
  · rintro y ⟨k, hk, rfl⟩
    change chapter05FiniteArtinMap D (x * k) = chapter05FiniteArtinMap D x
    have hk' : chapter05FiniteArtinMap D k = 1 := by
      rw [← MonoidHom.mem_ker, chapter05FiniteArtinMap_kernel D]
      exact hk
    rw [map_mul, hk', mul_one]

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
