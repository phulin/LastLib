import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14.Section01APrimeAndItsCompletedBranches

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open Set
open LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

universe u v w

/-! ## 14.2. Frobenius at an unramified prime -/

abbrev chapter14PrimeResidueField
    {F : Type u} [Field F] [NumberField F] (p : Chapter14Prime F) : Type u :=
  p.asIdeal.ResidueField

abbrev chapter14BranchResidueField
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    {p : Chapter14Prime F} (P : Chapter14PrimeAbove F E p) : Type v :=
  P.1.ResidueField

/- The norm is the cardinality of the residue field. -/
theorem chapter14_prime_norm_eq_residue_field_card
    {F : Type u} [Field F] [NumberField F] (p : Chapter14Prime F) :
    chapter14PrimeNorm p = Nat.card (chapter14PrimeResidueField p) :=
  by sorry

def chapter14ArithmeticFrobeniusResidue
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [FiniteDimensional k l] : Gal(l / k) :=
  chapter06ArithmeticFrobenius k l

def chapter14GeometricFrobeniusResidue
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [FiniteDimensional k l] : Gal(l / k) :=
  (chapter14ArithmeticFrobeniusResidue k l)⁻¹

theorem chapter14_arithmetic_frobenius_residue_apply
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [FiniteDimensional k l] (x : l) :
    chapter14ArithmeticFrobeniusResidue k l x = x ^ Fintype.card k := by
  simpa [chapter14ArithmeticFrobeniusResidue] using
    chapter06_arithmetic_frobenius_apply k l x

theorem chapter14_geometric_frobenius_residue_is_inverse
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [FiniteDimensional k l] :
    chapter14GeometricFrobeniusResidue k l =
      (chapter14ArithmeticFrobeniusResidue k l)⁻¹ :=
  rfl

/- The reduction map and its kernel are the global form of the decomposition /
   inertia exact sequence. -/
def chapter14FrobeniusLiftSet
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) : Set D :=
  {σ | R.reduction σ =
    chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField}

def chapter14UnramifiedAtPrime
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) : Prop :=
  R.inertia = ⊥

theorem chapter14_prime_reduction_exact_sequence
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) :
    chapter14PrimeReductionExact R := by
  sorry

theorem chapter14_prime_reduction_is_exact
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) :
    chapter14PrimeReductionExact R ∧
      Function.Surjective R.reduction := by
  exact ⟨chapter14_prime_reduction_exact_sequence R, R.surjective⟩

theorem chapter14_prime_reduction_quotient_is_residue_galois_group
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) :
    Nonempty
      ((D ⧸ R.inertia) ≃*
        Gal(P.1.ResidueField / p.asIdeal.ResidueField)) := by
  sorry

theorem chapter14_unramified_reduction_is_injective
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hR : chapter14UnramifiedAtPrime R) :
    Function.Injective R.reduction := by
  sorry

theorem chapter14_unramified_frobenius_exists_unique
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hR : chapter14UnramifiedAtPrime R) :
    ∃! σ : D, σ ∈ chapter14FrobeniusLiftSet R := by
  sorry

noncomputable def chapter14ArithmeticFrobeniusLift
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hR : chapter14UnramifiedAtPrime R) : D :=
  Classical.choose (chapter14_unramified_frobenius_exists_unique R hR)

noncomputable def chapter14GeometricFrobeniusLift
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hR : chapter14UnramifiedAtPrime R) : D :=
  (chapter14ArithmeticFrobeniusLift R hR)⁻¹

theorem chapter14_arithmetic_frobenius_lift_reduces_to_power_map
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hR : chapter14UnramifiedAtPrime R) (x : P.1.ResidueField) :
    R.reduction (chapter14ArithmeticFrobeniusLift R hR) x =
      x ^ chapter14PrimeNorm p := by
  sorry

theorem chapter14_geometric_frobenius_lift_is_inverse
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hR : chapter14UnramifiedAtPrime R) :
    chapter14GeometricFrobeniusLift R hR =
      (chapter14ArithmeticFrobeniusLift R hR)⁻¹ :=
  rfl

/- Transport of the reduction sequence along `P' = σ P`. -/
structure Chapter14FrobeniusConjugacy
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F}
    {P Q : Chapter14PrimeAbove F E p}
    {D D' : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Field Q.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField Q.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField Q.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField Q.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (R' : Chapter14PrimeReduction F E p Q D')
    (σ : Gal(E / F)) where
  prime_transport : chapter14PrimeAction E p σ P = Q
  group_conjugation : D ≃* D'
  residue_conjugation :
    Gal(P.1.ResidueField / p.asIdeal.ResidueField) ≃*
      Gal(Q.1.ResidueField / p.asIdeal.ResidueField)
  group_conjugation_apply : ∀ τ : D,
    (group_conjugation τ : Gal(E / F)) =
      σ * (τ : Gal(E / F)) * σ⁻¹
  reduction_compatibility : ∀ τ : D,
    R'.reduction (group_conjugation τ) =
      residue_conjugation (R.reduction τ)

theorem chapter14_frobenius_conjugacy
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F}
    {P Q : Chapter14PrimeAbove F E p}
    {D D' : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Field Q.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField Q.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField Q.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField Q.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    [Finite Q.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (R' : Chapter14PrimeReduction F E p Q D')
    (σ : Gal(E / F))
    (C : Chapter14FrobeniusConjugacy R R' σ)
    (hR : chapter14UnramifiedAtPrime R)
    (hR' : chapter14UnramifiedAtPrime R') :
    C.group_conjugation (chapter14ArithmeticFrobeniusLift R hR) =
      chapter14ArithmeticFrobeniusLift R' hR' := by
  sorry

theorem chapter14_frobenius_conjugacy_in_the_global_galois_group
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F}
    {P Q : Chapter14PrimeAbove F E p}
    {D D' : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Field Q.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField Q.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField Q.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField Q.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    [Finite Q.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (R' : Chapter14PrimeReduction F E p Q D')
    (σ : Gal(E / F))
    (C : Chapter14FrobeniusConjugacy R R' σ)
    (hR : chapter14UnramifiedAtPrime R) :
    (C.group_conjugation (chapter14ArithmeticFrobeniusLift R hR) : Gal(E / F)) =
      σ * (chapter14ArithmeticFrobeniusLift R hR : Gal(E / F)) * σ⁻¹ := by
  exact C.group_conjugation_apply _

/- At a ramified prime the canonical object is a coset of lifts. -/
def chapter14ArithmeticFrobeniusCoset
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) : Set D :=
  chapter14FrobeniusLiftSet R

theorem chapter14_ramified_frobenius_coset_nonempty
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) :
    (chapter14ArithmeticFrobeniusCoset R).Nonempty := by
  sorry

theorem chapter14_frobenius_lifts_differ_by_inertia
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    {g h : D} (hg : g ∈ chapter14ArithmeticFrobeniusCoset R)
    (hh : h ∈ chapter14ArithmeticFrobeniusCoset R) :
    ∃ i : R.inertia, h = g * i := by
  sorry

theorem chapter14_ramified_frobenius_has_no_unique_lift
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D)
    (hI : ∃ i : R.inertia, (i : D) ≠ 1) :
    ¬ ∃! g : D, g ∈ chapter14ArithmeticFrobeniusCoset R := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
