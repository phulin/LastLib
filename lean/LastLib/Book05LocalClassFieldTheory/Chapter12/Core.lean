import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section01TheLocalNormFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section04TheMultiplicativePicture
import LastLib.Book05LocalClassFieldTheory.Chapter06.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter07.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter10.Section05CompositaAndIntersections
import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section01ExactTopologicalStatement
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

open scoped BigOperators

universe u v

/-! ### Shared interfaces for the reciprocity dictionary

The constructions below are the small bridges needed to state the source's
dictionary. Norms, finite Artin maps, finite abelian subextensions, and
continuous characters are inherited from the preceding Book 5 chapters.
-/

/-- The local-field hypotheses fixed at the beginning of the book. -/
abbrev Chapter12LocalFieldProfile (K : Type*) [Field K] :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.Chapter10LocalFieldProfile K

/-- The canonical valuation-ring unit filtration imported from Book 2. -/
abbrev chapter12CanonicalUnitFiltration
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnitFiltration v n

theorem chapter12_canonical_unit_filtration_zero
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    chapter12CanonicalUnitFiltration v 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnitSet v := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unit_filtration_zero v

theorem chapter12_canonical_unit_filtration_succ
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    chapter12CanonicalUnitFiltration v (n + 1) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11PrincipalUnitSet v
        (n + 1) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unit_filtration_succ v n

/-- The multiplicative homomorphism underlying the field norm. -/
noncomputable def chapter12MultiplicativeNormMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormHom K L

/-- The norm subgroup in the multiplicative group of the base field.

This is the Chapter 12 name for the canonical norm subgroup already exposed
by Book 5, Chapter 10. -/
abbrev chapter12NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroup K L

/-- Membership in a norm subgroup, with the units map exposed. -/
theorem chapter12_mem_normSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (u : Kˣ) :
    u ∈ chapter12NormSubgroup K L ↔
      ∃ y : Lˣ, chapter12MultiplicativeNormMap K L y = u := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_mem_normSubgroup_iff
    K L u

/-- The abelianity condition on a finite Galois extension. -/
abbrev Chapter12FiniteAbelianExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop :=
  LastLib.Book05LocalClassFieldTheory.Chapter06.Chapter06FiniteAbelianExtension K L

/-- A finite Artin map together with the two properties needed for its quotient. -/
abbrev Chapter12FiniteArtinMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))] :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.Chapter10NormalizedFiniteArtinMap K L

theorem chapter12_finite_artin_map_exists
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K L) :
  Nonempty (Chapter12FiniteArtinMap K L) := by
  refine ⟨{
    artin := {
      reciprocity :=
        LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05FiniteReciprocityMap D
      kernel_eq_norm := ?_
      surjective :=
        LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05FiniteReciprocityMap_surjective D }
    classFormation := D
    artin_eq_finite_reciprocity := rfl }⟩
  rw [LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05FiniteReciprocityMap_kernel D]
  have hmap : chapter12MultiplicativeNormMap K L =
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap K L := by
    rfl
  ext x
  rw [LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff,
    chapter12_mem_normSubgroup_iff, hmap]

/-- The finite Artin kernel is the norm subgroup. -/
theorem chapter12_finite_artin_kernel_eq_norm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (A : Chapter12FiniteArtinMap K L) :
    A.artin.reciprocity.ker = chapter12NormSubgroup K L := by
  exact A.artin.kernel_eq_norm

/-- The finite Artin map is onto the finite abelian Galois group. -/
theorem chapter12_finite_artin_surjective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (A : Chapter12FiniteArtinMap K L) :
    Function.Surjective A.artin.reciprocity := by
  exact A.artin.surjective

/- The quotient form is intentionally exposed as a `Nonempty` equivalence;
   later users may choose a representative without rebuilding the kernel
   calculation. -/
theorem chapter12_finite_artin_quotient_equiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (A : Chapter12FiniteArtinMap K L) :
    Nonempty
      (Kˣ ⧸ chapter12NormSubgroup K L ≃* Gal(L / K)) := by
  exact ⟨LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10ArtinQuotientEquiv
    K L A.artin⟩

/-- The finite quotient degree is the field degree. -/
theorem chapter12_norm_quotient_card_eq_degree
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (A : Chapter12FiniteArtinMap K L) :
    Nat.card (Kˣ ⧸ chapter12NormSubgroup K L) = Module.finrank K L := by
  exact
    (Nat.card_congr
      (LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10ArtinQuotientEquiv
        K L A.artin).toEquiv).trans
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_galois_group_card_eq_degree K L)

/-- A finite abelian subextension inside a fixed algebraic closure.

The separability field records the intended separable closure rather than
silently allowing purely inseparable intermediate fields in equal
characteristic. -/
abbrev Chapter12FiniteAbelianSubextension (K : Type*) [Field K] :=
  LastLib.Book05LocalClassFieldTheory.Chapter06.Chapter06FiniteAbelianSubextension
    K (AlgebraicClosure K)

/-- Open finite-index subgroups of the topological multiplicative group. -/
def chapter12OpenFiniteIndex
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (H : Subgroup Kˣ) : Prop :=
  IsOpen (H : Set Kˣ) ∧ H.FiniteIndex

/-- The cyclic quotient condition used for cyclic extensions. -/
abbrev chapter12CyclicQuotient
    {K : Type*} [Field K] (H : Subgroup Kˣ) : Prop :=
  IsCyclic (Kˣ ⧸ H)

/-- The local coordinates used by the dictionary. -/
structure Chapter12LocalCoordinates
    (K k : Type*) [Field K] [Field k] where
  [finite_residue : Finite k]
  uniformizer : Kˣ
  valuation : Kˣ → ℤ
  valuation_one : valuation 1 = 0
  valuation_mul : ∀ x y, valuation (x * y) = valuation x + valuation y
  valuation_inv : ∀ x, valuation x⁻¹ = -valuation x
  units : Subgroup Kˣ
  principalUnits : ℕ → Subgroup Kˣ
  principal_zero : principalUnits 0 = units
  principal_le_units : ∀ n, principalUnits n ≤ units
  valuation_kernel : ∀ x, valuation x = 0 ↔ x ∈ units
  uniformizer_value : valuation uniformizer = 1
  valuation_quotient : Kˣ ⧸ units ≃* Multiplicative ℤ
  valuation_quotient_apply : ∀ x : Kˣ,
    valuation_quotient (QuotientGroup.mk' units x) =
      Multiplicative.ofAdd (valuation x)
  residue_units :
    (units ⧸ ((principalUnits 1).comap units.subtype)) ≃* kˣ

/-- The subgroup generated by the uniformizer power and the unit subgroup. -/
def chapter12UnramifiedNormSubgroup
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (m : ℕ) : Subgroup Kˣ :=
  Subgroup.zpowers (C.uniformizer ^ m) ⊔ C.units

/-- Set-level notation for `π^(mℤ) Oˣ`. -/
def chapter12PiPowUnits
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (m : ℕ) : Set Kˣ :=
  {x | ∃ z : ℤ, ∃ u : C.units,
    x = C.uniformizer ^ ((m : ℤ) * z) * u.1}

theorem chapter12_mem_unramified_norm_subgroup_iff
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (m : ℕ) (x : Kˣ) :
    x ∈ chapter12UnramifiedNormSubgroup C m ↔
      x ∈ chapter12PiPowUnits C m := by
  change x ∈ Subgroup.zpowers (C.uniformizer ^ m) ⊔ C.units ↔
    x ∈ chapter12PiPowUnits C m
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, u, hu, hxy⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨z, ⟨u, hu⟩, ?_⟩
    rw [← hxy, ← hz, zpow_mul]
    rfl
  · rintro ⟨z, u, hxu⟩
    have hzmem : (C.uniformizer ^ m) ^ z ∈ Subgroup.zpowers (C.uniformizer ^ m) :=
      (Subgroup.mem_zpowers_iff).2 ⟨z, rfl⟩
    refine ⟨(C.uniformizer ^ m) ^ z, hzmem, (u : Kˣ), u.property, ?_⟩
    calc
      (C.uniformizer ^ m) ^ z * (u : Kˣ) =
          (C.uniformizer ^ (m : ℤ)) ^ z * (u : Kˣ) := by
            rw [zpow_natCast]
      _ = C.uniformizer ^ ((m : ℤ) * z) * (u : Kˣ) := by rw [zpow_mul]
      _ = x := hxu.symm

/-- The product of two norm subgroups, using the established Chapter 10 API. -/
abbrev chapter12NormSubgroupProduct
    {K : Type*} [Field K] (H₁ H₂ : Subgroup Kˣ) : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10NormSubgroupProduct H₁ H₂

theorem chapter12_mem_norm_subgroup_product_iff
    {K : Type*} [Field K] (H₁ H₂ : Subgroup Kˣ) (x : Kˣ) :
    x ∈ chapter12NormSubgroupProduct H₁ H₂ ↔
      ∃ a ∈ H₁, ∃ b ∈ H₂, a * b = x := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter10.chapter10_mem_normSubgroupProduct_iff
    H₁ H₂ x

/-- Total ramification on the norm side: the valuation image is all of `ℤ`. -/
def chapter12TotallyRamifiedNormSubgroup
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ) : Prop :=
  Function.Surjective (fun x : H => C.valuation x.1)

/-- A valuation-one norm is a unit times the chosen uniformizer. -/
def chapter12ValuationOneNormForm
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ) : Prop :=
  ∃ x : H, C.valuation x.1 = 1 ∧
    ∃ u : Kˣ, C.valuation u = 0 ∧ x.1 = u * C.uniformizer

/-- The multiplicative quotient in the `n`th unit layer. -/
abbrev chapter12UnitLayer
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (n : ℕ) : Type _ :=
  (C.principalUnits n : Type _) ⧸
    ((C.principalUnits (n + 1)).comap (C.principalUnits n).subtype)

/-- Topological equivalences and continuous characters use the canonical
interfaces from Mathlib and Chapter 11. -/
abbrev Chapter12TopologicalGroupEquiv
    (G H : Type*) [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] := G ≃ₜ* H

abbrev Chapter12ContinuousCharacter
    (G A : Type*) [Monoid G] [Monoid A]
    [TopologicalSpace G] [TopologicalSpace A] := G →ₜ* A

/-- Pullback of a continuous character along a continuous group homomorphism. -/
def chapter12CharacterPullback
    {G H A : Type*} [Monoid G] [Monoid H] [Monoid A]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace A]
    (f : G →ₜ* H)
    (χ : Chapter12ContinuousCharacter H A) :
    Chapter12ContinuousCharacter G A :=
  χ.comp f

/-- Relative compactness of a character image. -/
def chapter12RelativeCompactRange
    {G A : Type*} [Monoid G] [Monoid A]
    [TopologicalSpace G] [TopologicalSpace A]
    (χ : Chapter12ContinuousCharacter G A) : Prop :=
  IsCompact (closure (Set.range χ))

/-- The infinite reciprocity comparison is the canonical Chapter 11 datum. -/
abbrev Chapter12ReciprocityLimit
    (K G : Type*) [Field K] [Group G]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [IsTopologicalGroup G] :=
  LastLib.Book05LocalClassFieldTheory.Chapter11.Chapter11ReciprocityData K G

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
