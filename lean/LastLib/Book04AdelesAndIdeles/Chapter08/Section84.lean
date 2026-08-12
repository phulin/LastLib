import LastLib.Book04AdelesAndIdeles.Chapter08.Section82

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct
open IsDedekindDomain

/-! ## 8.4 Lattices and finite ideles -/

def chapter08LatticeSet {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Set K :=
  {a | ∀ v : HeightOneSpectrum (Chapter08Integers K),
    (a : v.adicCompletion K) * chapter08FiniteIdeleComponent x v ∈
      v.adicCompletionIntegers K}

def chapter08Lattice {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Submodule (Chapter08Integers K) K where
  carrier := chapter08LatticeSet x
  zero_mem' := by
    intro v
    sorry
  add_mem' := by
    intro a b ha hb v
    sorry
  smul_mem' := by
    intro r a ha v
    sorry

theorem chapter08_lattice_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) (a : K) :
    a ∈ chapter08Lattice x ↔
      ∀ v : HeightOneSpectrum (Chapter08Integers K),
        (a : v.adicCompletion K) * chapter08FiniteIdeleComponent x v ∈
          v.adicCompletionIntegers K :=
  Iff.rfl

noncomputable def chapter08LatticeFractionalIdeal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08FractionalIdeal K :=
  ⟨chapter08Lattice x, by
    sorry⟩

theorem chapter08_lattice_fractionalIdeal_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08LatticeFractionalIdeal x ≠ 0 := by
  sorry

theorem chapter08_lattice_eq_inverse_ideal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08LatticeFractionalIdeal x =
      (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)⁻¹ := by
  sorry

theorem chapter08_lattice_unchanged_by_finite_integral_unit
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (u : chapter08FiniteIntegralUnits (K := K)) :
    chapter08LatticeSet (x * u.1) = chapter08LatticeSet x := by
  sorry

theorem chapter08_lattice_unchanged_by_finite_integral_unit_submodule
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (u : chapter08FiniteIntegralUnits (K := K)) :
    chapter08Lattice (x * u.1) = chapter08Lattice x := by
  sorry

noncomputable def chapter08FiniteIdeleQuotientEquivIdealGroup
    (K : Type*) [Field K] [NumberField K] :
    (Chapter08FiniteIdeles K ⧸ chapter08FiniteIntegralUnits (K := K)) ≃*
      Chapter08IdealGroup K :=
  QuotientGroup.liftEquiv (chapter08FiniteIntegralUnits (K := K))
    (chapter08_finite_idele_ideal_surjective K)
    (chapter08_finite_idele_ideal_kernel (K := K)).symm

def chapter08RankOneFractionalLattice
    {K : Type*} [Field K] [NumberField K]
    (L : Submodule (Chapter08Integers K) K) : Prop :=
  ∃ I : Chapter08FractionalIdeal K, I ≠ 0 ∧ (I : Submodule (Chapter08Integers K) K) = L

theorem chapter08_lattice_is_rank_one_fractional_lattice
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08RankOneFractionalLattice (chapter08Lattice x) := by
  refine ⟨chapter08LatticeFractionalIdeal x, chapter08_lattice_fractionalIdeal_ne_zero x, ?_⟩
  rfl

theorem chapter08_ideal_group_classifies_rank_one_lattices
    (K : Type*) [Field K] [NumberField K] :
    ∀ L : Submodule (Chapter08Integers K) K,
      chapter08RankOneFractionalLattice L →
        ∃ x : Chapter08FiniteIdeles K, chapter08Lattice x = L := by
  sorry

def chapter08IdealToLattice {K : Type*} [Field K] [NumberField K]
    (I : Chapter08IdealGroup K) : Chapter08FractionalIdeal K :=
  (I : Chapter08FractionalIdeal K)⁻¹

def chapter08HomotheticFractionalIdeal
    {K : Type*} [Field K] [NumberField K]
    (I J : Chapter08IdealGroup K) : Prop :=
  ∃ a : Kˣ, I = J * toPrincipalIdeal (Chapter08Integers K) K a

abbrev Chapter08HomotheticLatticeClassGroup
    (K : Type*) [Field K] [NumberField K] :=
  Chapter08IdealGroup K ⧸ (toPrincipalIdeal (Chapter08Integers K) K).range

noncomputable def chapter08HomotheticLatticeClassEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter08OrdinaryClassGroup K ≃*
      Chapter08HomotheticLatticeClassGroup K :=
  ClassGroup.equiv K

theorem chapter08_homothetic_lattices_are_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      (Chapter08OrdinaryClassGroup K ≃*
        Chapter08HomotheticLatticeClassGroup K) := by
  exact ⟨chapter08HomotheticLatticeClassEquiv K⟩

end

end LastLib.Book04AdelesAndIdeles.Chapter08
