import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies

/-!
## 2.2 Single covers and affine reduction

The singleton-family predicate is kept distinct from quasi-compactness of the whole source.  This
is the distinction needed for an infinite disjoint union of redundant copies of the target.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry TensorProduct

universe u v

/-- A faithfully flat, quasi-compact, surjective morphism in the book's fpqc terminology. -/
def IsFpqcMorphism {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ QuasiCompact p ∧ Surjective p

/-- The singleton family associated to one scheme morphism. -/
def singletonFamily {S T : Scheme.{u}} (p : T ⟶ S) : SchemeFamily S Unit where
  obj := fun _ ↦ T
  map := fun _ ↦ p

/-- The family-level fpqc condition for a singleton. -/
def IsFpqcSingletonFamily {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  FpqcCoveringFamily (singletonFamily p)

/-- The finite-reduction condition for one morphism, with the source open exposed explicitly. -/
def SingletonFiniteReductionCondition {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  ∀ (U : S.Opens), IsCompact (U : Set S) →
    ∃ V : T.Opens, IsCompact (V : Set T) ∧
      (U : Set S) = p '' (V : Set T)

theorem singletonFamily_iff_flat_and_finite_reduction
    {S T : Scheme.{u}} (p : T ⟶ S) :
    IsFpqcSingletonFamily p ↔ Flat p ∧ SingletonFiniteReductionCondition p := by
  sorry

theorem fpqcMorphism_is_singletonFamily
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : IsFpqcMorphism p) : IsFpqcSingletonFamily p := by
  sorry

theorem singletonFamily_is_flat_and_surjective
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : IsFpqcSingletonFamily p) : Flat p ∧ Surjective p := by
  sorry

theorem singletonFamily_is_fpqcMorphism_of_quasiCompact
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : IsFpqcSingletonFamily p) (hqc : QuasiCompact p) :
    IsFpqcMorphism p := by
  sorry

theorem isFpqcMorphism_iff_singletonFamily_of_quasiCompact
    {S T : Scheme.{u}} (p : T ⟶ S) (hqc : QuasiCompact p) :
    IsFpqcMorphism p ↔ IsFpqcSingletonFamily p := by
  sorry

/-- A quasi-compact open part of a singleton source, together with a finite affine refinement. -/
structure AffineSingletonRefinement {S T : Scheme.{u}} (p : T ⟶ S) where
  sourceOpen : T.Opens
  sourceOpen_quasiCompact : IsCompact (sourceOpen : Set T)
  sourceOpen_surjective : p '' (sourceOpen : Set T) = (Set.univ : Set S)
  cardinality : ℕ
  affineOpen : Fin cardinality → T.Opens
  affine : ∀ j, IsAffineOpen (affineOpen j)
  refines : ∀ j, affineOpen j ≤ sourceOpen
  covers : (sourceOpen : Set T) = ⋃ j : Fin cardinality, (affineOpen j : Set T)

theorem exists_affine_singleton_refinement
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hS : IsAffine S) (hp : IsFpqcSingletonFamily p) :
    Nonempty (AffineSingletonRefinement p) := by
  sorry

/-- A finite family reduction in which every selected source open is affine. -/
structure AffineFiniteFamilyReduction {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) (U : S.Opens) where
  cardinality : ℕ
  member : Fin cardinality → I
  sourceOpen : ∀ j, (F.obj (member j)).Opens
  affine : ∀ j, IsAffineOpen (sourceOpen j)
  quasiCompact : ∀ j, IsCompact (sourceOpen j : Set (F.obj (member j)))
  covers : (U : Set S) =
    ⋃ j : Fin cardinality,
      F.map (member j) '' (sourceOpen j : Set (F.obj (member j)))

theorem finiteFamilyReduction_affine_refinement
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    {U : S.Opens} (hU : IsCompact (U : Set S))
    (hF : FpqcCoveringFamily F) :
    Nonempty (AffineFiniteFamilyReduction F U) := by
  sorry

/-- The finite affine ring diagram obtained over an affine base. -/
structure AffineRingReduction (A : CommRingCat.{u}) where
  cardinality : ℕ
  B : Fin cardinality → CommRingCat.{u}
  map : ∀ j, A ⟶ B j
  flat : ∀ j, RingHom.Flat (map j).hom
  spectra_cover :
    (⋃ j : Fin cardinality,
      Set.range (PrimeSpectrum.comap (map j).hom)) =
      (Set.univ : Set (PrimeSpectrum A))

/-- The geometric and algebraic records retained by affine reduction. -/
structure AffineFamilyRingReduction {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) (U : S.Opens) where
  geometric : AffineFiniteFamilyReduction F U
  A : CommRingCat.{u}
  targetIso : S ≅ Spec A
  B : Fin geometric.cardinality → CommRingCat.{u}
  map : ∀ j, A ⟶ B j
  sourceMap : ∀ j, Spec (B j) ⟶ S
  sourceMap_eq : ∀ j,
    sourceMap j ≫ targetIso.hom = Spec.map (map j)
  sourceMap_range : ∀ j,
    Set.range (sourceMap j) =
      F.map (geometric.member j) ''
        (geometric.sourceOpen j : Set (F.obj (geometric.member j)))
  flat : ∀ j, RingHom.Flat (map j).hom
  spectra_cover :
    (⋃ j : Fin geometric.cardinality,
      Set.range (PrimeSpectrum.comap (map j).hom)) =
      (Set.univ : Set (PrimeSpectrum A))

noncomputable def AffineFamilyRingReduction.toRingReduction
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I} {U : S.Opens}
    (R : AffineFamilyRingReduction F U) : AffineRingReduction R.A where
  cardinality := R.geometric.cardinality
  B := R.B
  map := R.map
  flat := R.flat
  spectra_cover := R.spectra_cover

theorem exists_affine_family_ring_reduction
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hS : IsAffine S) (hF : FpqcCoveringFamily F) :
    Nonempty (AffineFamilyRingReduction F (⊤ : S.Opens)) := by
  sorry

noncomputable def AffineRingReduction.productRingHom
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    (A : Type u) →+* (∀ j, (R.B j : Type u)) :=
  RingHom.pi (fun j ↦ (R.map j).hom)

/-- The finite product of the selected modules, identified with their finite direct sum. -/
noncomputable def AffineRingReduction.productDirectSumLinearEquiv
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    letI : ∀ j, Algebra (A : Type u) (R.B j : Type u) :=
      fun j ↦ (R.map j).hom.toAlgebra
    (∀ j, (R.B j : Type u)) ≃ₗ[(A : Type u)]
      DirectSum (Fin R.cardinality) (fun j ↦ (R.B j : Type u)) := by
  letI : ∀ j, Algebra (A : Type u) (R.B j : Type u) :=
    fun j ↦ (R.map j).hom.toAlgebra
  exact
    (DirectSum.linearEquivFunOnFintype (A : Type u) (Fin R.cardinality)
      (fun j ↦ (R.B j : Type u))).symm

@[simp]
theorem AffineRingReduction.productRingHom_apply
    {A : CommRingCat.{u}} (R : AffineRingReduction A)
    (a : A) (j : Fin R.cardinality) :
    R.productRingHom a j = R.map j a := by
  rfl

theorem AffineRingReduction.productRingHom_flat
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    RingHom.Flat R.productRingHom := by
  sorry

theorem AffineRingReduction.productRingHom_faithfullyFlat
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    RingHom.FaithfullyFlat R.productRingHom := by
  sorry

/-- The pairwise overlap ring retained for descent calculations. -/
noncomputable def AffineRingReduction.pairwiseOverlap
    {A : CommRingCat.{u}} (R : AffineRingReduction A)
    (i j : Fin R.cardinality) : Type u := by
  letI : Algebra (A : Type u) (R.B i : Type u) := (R.map i).hom.toAlgebra
  letI : Algebra (A : Type u) (R.B j : Type u) := (R.map j).hom.toAlgebra
  exact (R.B i : Type u) ⊗[(A : Type u)] (R.B j : Type u)

/-- The triple overlap ring retained for cocycle calculations. -/
noncomputable def AffineRingReduction.tripleOverlap
    {A : CommRingCat.{u}} (R : AffineRingReduction A)
    (i j k : Fin R.cardinality) : Type u := by
  letI : Algebra (A : Type u) (R.B i : Type u) := (R.map i).hom.toAlgebra
  letI : Algebra (A : Type u) (R.B j : Type u) := (R.map j).hom.toAlgebra
  letI : Algebra (A : Type u) (R.B k : Type u) := (R.map k).hom.toAlgebra
  exact
    ((R.B i : Type u) ⊗[(A : Type u)] (R.B j : Type u)) ⊗[(A : Type u)]
      (R.B k : Type u)

theorem affine_family_product_is_faithfullyFlat
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hS : IsAffine S) (hF : FpqcCoveringFamily F) :
    ∃ (A : CommRingCat.{u}) (R : AffineFamilyRingReduction F (⊤ : S.Opens)),
      RingHom.FaithfullyFlat R.toRingReduction.productRingHom := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
