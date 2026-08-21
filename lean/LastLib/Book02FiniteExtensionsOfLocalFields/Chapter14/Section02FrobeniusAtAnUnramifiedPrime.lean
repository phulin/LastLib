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
  by
    change Ideal.absNorm p.asIdeal = Nat.card p.asIdeal.ResidueField
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Equiv.ofBijective (algebraMap
      ((NumberField.RingOfIntegers F) ⧸ p.asIdeal) p.asIdeal.ResidueField)
      p.asIdeal.bijective_algebraMap_quotient_residueField)

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
  change Function.MulExact (Subgroup.subtype R.inertia) R.reduction
  apply MonoidHom.mulExact_iff.mpr
  rw [R.kernel_eq_inertia]
  exact (Subgroup.range_subtype (MonoidHom.ker R.reduction)).symm

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
  refine ⟨?_⟩
  exact
    (QuotientGroup.quotientMulEquivOfEq R.kernel_eq_inertia).trans
      (QuotientGroup.quotientKerEquivOfSurjective R.reduction R.surjective)

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
  apply (MonoidHom.ker_eq_bot_iff R.reduction).mp
  change R.inertia = ⊥ at hR
  rw [← R.kernel_eq_inertia, hR]

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
  change ∃! σ : D, R.reduction σ =
    chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField
  obtain ⟨σ₀, hσ₀⟩ := R.surjective
    (chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField)
  refine ⟨σ₀, hσ₀, ?_⟩
  intro σ hσ
  exact (chapter14_unramified_reduction_is_injective R hR) (hσ.trans hσ₀.symm)

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
  have hmem : chapter14ArithmeticFrobeniusLift R hR ∈ chapter14FrobeniusLiftSet R :=
    (Classical.choose_spec (chapter14_unramified_frobenius_exists_unique R hR)).1
  change R.reduction (chapter14ArithmeticFrobeniusLift R hR) =
    chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField at hmem
  have hcard : chapter14PrimeNorm p = Fintype.card p.asIdeal.ResidueField := by
    rw [chapter14_prime_norm_eq_residue_field_card, Nat.card_eq_fintype_card]
  rw [hmem, chapter14_arithmetic_frobenius_residue_apply, ← hcard]

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
    [Fintype p.asIdeal.ResidueField] [Finite P.1.ResidueField]
    [Finite Q.1.ResidueField]
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
  residue_frobenius_compatibility :
    residue_conjugation
        (chapter14ArithmeticFrobeniusResidue
          p.asIdeal.ResidueField P.1.ResidueField) =
      chapter14ArithmeticFrobeniusResidue
        p.asIdeal.ResidueField Q.1.ResidueField

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
  let hU := chapter14_unramified_frobenius_exists_unique R' hR'
  have hconj : C.group_conjugation (chapter14ArithmeticFrobeniusLift R hR) ∈
      chapter14FrobeniusLiftSet R' := by
    change R'.reduction (C.group_conjugation (chapter14ArithmeticFrobeniusLift R hR)) =
      chapter14ArithmeticFrobeniusResidue
        p.asIdeal.ResidueField Q.1.ResidueField
    rw [C.reduction_compatibility]
    rw [show R.reduction (chapter14ArithmeticFrobeniusLift R hR) =
      chapter14ArithmeticFrobeniusResidue
          p.asIdeal.ResidueField P.1.ResidueField from
      (Classical.choose_spec (chapter14_unramified_frobenius_exists_unique R hR)).1]
    exact C.residue_frobenius_compatibility
  have htarget : chapter14ArithmeticFrobeniusLift R' hR' ∈
      chapter14FrobeniusLiftSet R' :=
    (Classical.choose_spec hU).1
  exact hU.unique hconj htarget

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
    (hR : chapter14UnramifiedAtPrime R)
    (hR' : chapter14UnramifiedAtPrime R') :
    (chapter14ArithmeticFrobeniusLift R' hR' : Gal(E / F)) =
      σ * (chapter14ArithmeticFrobeniusLift R hR : Gal(E / F)) * σ⁻¹ := by
  rw [← chapter14_frobenius_conjugacy R R' σ C hR hR']
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
  change ∃ σ : D, R.reduction σ =
    chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField
  obtain ⟨σ, hσ⟩ := R.surjective
    (chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField)
  exact ⟨σ, hσ⟩

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
  change R.reduction g =
    chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField at hg
  change R.reduction h =
    chapter14ArithmeticFrobeniusResidue
      p.asIdeal.ResidueField P.1.ResidueField at hh
  refine ⟨⟨g⁻¹ * h, ?_⟩, ?_⟩
  · rw [R.kernel_eq_inertia]
    change R.reduction (g⁻¹ * h) = 1
    rw [map_mul, map_inv, hg, hh]
    exact inv_mul_cancel _
  · change h = g * (g⁻¹ * h)
    rw [← mul_assoc, mul_inv_cancel, one_mul]

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
  rintro ⟨g, hg, huniq⟩
  obtain ⟨i, hi⟩ := hI
  have hgi : g * (i : D) ∈ chapter14ArithmeticFrobeniusCoset R := by
    change R.reduction (g * (i : D)) =
      chapter14ArithmeticFrobeniusResidue
        p.asIdeal.ResidueField P.1.ResidueField
    rw [map_mul]
    have hi' : R.reduction (i : D) = 1 := by
      change (i : D) ∈ MonoidHom.ker R.reduction
      rw [← R.kernel_eq_inertia]
      exact i.property
    rw [hi', mul_one]
    exact hg
  have heq : g * (i : D) = g := huniq (g * (i : D)) hgi
  have hi_eq : (i : D) = 1 := by
    calc
      (i : D) = 1 * (i : D) := by simp
      _ = (g⁻¹ * g) * (i : D) := by simp
      _ = g⁻¹ * (g * (i : D)) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [heq]
      _ = 1 := by simp
  exact hi hi_eq

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
