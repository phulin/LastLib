import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section01TheLocalNormFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section04TheMultiplicativePicture
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

open scoped BigOperators

universe u v

/-! ### Shared interfaces for the reciprocity dictionary

The preceding chapters of Book 5 are not yet available in this checkout.  The
interfaces below keep the genuinely canonical constructions (norm images,
quotients, unit layers, and continuous characters) separate from the finite
reciprocity and existence statements that consume them.
-/

/-- The local-field hypotheses fixed at the beginning of the book. -/
structure Chapter12LocalFieldProfile
    (K : Type*) [Field K] where
  valuation : AddValuation K (WithTop ℤ)
  [discrete : Valuation.IsRankOneDiscrete valuation.toValuation]
  complete :
    IsAdicComplete (IsLocalRing.maximalIdeal valuation.toValuation.valuationSubring)
      valuation.toValuation.valuationSubring
  [finite_residue : Finite
    (IsLocalRing.ResidueField valuation.toValuation.valuationSubring)]
  uniformizer : K
  uniformizer_value : valuation uniformizer = 1

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
  Units.map (Algebra.norm K (S := L))

/-- The norm subgroup in the multiplicative group of the base field.

This is the Chapter 12 name for the canonical norm subgroup already exposed
by Book 2, Chapter 11. -/
abbrev chapter12NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormSubgroup K L

/-- Membership in a norm subgroup, with the units map exposed. -/
theorem chapter12_mem_normSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (u : Kˣ) :
    u ∈ chapter12NormSubgroup K L ↔
      ∃ y : Lˣ, chapter12MultiplicativeNormMap K L y = u := by
  constructor
  · intro hu
    change u ∈ Subgroup.map (chapter12MultiplicativeNormMap K L) ⊤ at hu
    rcases hu with ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    change u ∈ Subgroup.map (chapter12MultiplicativeNormMap K L) ⊤
    exact ⟨y, trivial, hy⟩

/-- The abelianity condition on a finite Galois extension. -/
class Chapter12FiniteAbelianExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop where
  galois_commutative : ∀ σ τ : Gal(L / K), σ * τ = τ * σ

/-- A finite Artin map together with the two properties needed for its quotient. -/
structure Chapter12FiniteArtinMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L] where
  reciprocity : Kˣ →* Gal(L / K)
  kernel_eq_norm : reciprocity.ker = chapter12NormSubgroup K L
  surjective : Function.Surjective reciprocity

/-
DEPENDENCY_GUESS: The finite Artin-map construction is the output of the
fundamental-class part of Book 5, Chapters 3--5.  Those chapters are not
present in this workspace, so the natural local interface is recorded here.
-/
theorem chapter12_finite_artin_map_exists
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L]
    (P : Chapter12LocalFieldProfile K) :
    Nonempty (Chapter12FiniteArtinMap K L) := by
  sorry

/-- The finite Artin kernel is the norm subgroup. -/
-- DEPENDENCY_GUESS: This is the kernel computation supplied by the
-- fundamental-class construction in the missing preceding chapters.
theorem chapter12_finite_artin_kernel_eq_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L]
    (A : Chapter12FiniteArtinMap K L) :
    A.reciprocity.ker = chapter12NormSubgroup K L := by
  exact A.kernel_eq_norm

/-- The finite Artin map is onto the finite abelian Galois group. -/
theorem chapter12_finite_artin_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L]
    (A : Chapter12FiniteArtinMap K L) :
    Function.Surjective A.reciprocity := by
  exact A.surjective

/- The quotient form is intentionally exposed as a `Nonempty` equivalence;
   later users may choose a representative without rebuilding the kernel
   calculation. -/
theorem chapter12_finite_artin_quotient_equiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L]
    (A : Chapter12FiniteArtinMap K L) :
    Nonempty
      (Kˣ ⧸ chapter12NormSubgroup K L ≃* Gal(L / K)) := by
  sorry

/-- The finite quotient degree is the field degree. -/
theorem chapter12_norm_quotient_card_eq_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L]
    (A : Chapter12FiniteArtinMap K L) :
    Nat.card (Kˣ ⧸ chapter12NormSubgroup K L) = Module.finrank K L := by
  sorry

/-- A finite abelian subextension inside a fixed algebraic closure.

The separability field records the intended separable closure rather than
silently allowing purely inseparable intermediate fields in equal
characteristic. -/
structure Chapter12FiniteAbelianSubextension
    (K : Type*) [Field K] where
  field : IntermediateField K (AlgebraicClosure K)
  [finite : FiniteDimensional K field]
  [galois : IsGalois K field]
  separable : Algebra.IsSeparable K field
  commutative : ∀ σ τ : Gal(field / K), σ * τ = τ * σ

/-- The canonical norm subgroup attached to a bundled subextension. -/
noncomputable def Chapter12FiniteAbelianSubextension.normSubgroup
    {K : Type*} [Field K]
    (E : Chapter12FiniteAbelianSubextension K) : Subgroup Kˣ := by
  letI : FiniteDimensional K E.field := E.finite
  exact chapter12NormSubgroup K E.field

/-- The degree of a bundled finite subextension. -/
noncomputable def Chapter12FiniteAbelianSubextension.degree
    {K : Type*} [Field K]
    (E : Chapter12FiniteAbelianSubextension K) : ℕ := by
  letI : FiniteDimensional K E.field := E.finite
  exact Module.finrank K E.field

/-- Open finite-index subgroups of the topological multiplicative group. -/
def chapter12OpenFiniteIndex
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (H : Subgroup Kˣ) : Prop :=
  IsOpen (H : Set Kˣ) ∧ Finite (Kˣ ⧸ H)

/-- The cyclic quotient condition used for cyclic extensions. -/
def chapter12CyclicQuotient
    {K : Type*} [Field K] (H : Subgroup Kˣ) : Prop :=
  ∃ g : Kˣ ⧸ H, ∀ x : Kˣ ⧸ H, ∃ n : ℤ, g ^ n = x

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
  Subgroup.closure (Set.insert (C.uniformizer ^ m) (C.units : Set Kˣ))

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
  sorry

/-- In the abelian multiplicative group this is the product of two subgroups. -/
def chapter12NormSubgroupProduct
    {K : Type*} [Field K] (H₁ H₂ : Subgroup Kˣ) : Subgroup Kˣ :=
  H₁ ⊔ H₂

theorem chapter12_mem_norm_subgroup_product_iff
    {K : Type*} [Field K] (H₁ H₂ : Subgroup Kˣ) (x : Kˣ) :
    x ∈ chapter12NormSubgroupProduct H₁ H₂ ↔
      ∃ a ∈ H₁, ∃ b ∈ H₂, a * b = x := by
  sorry

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

/-- A topological group isomorphism, keeping both continuity obligations explicit. -/
structure Chapter12TopologicalGroupEquiv
    (G H : Type*) [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] where
  toGroupEquiv : G ≃* H
  continuous_toFun : Continuous toGroupEquiv
  continuous_invFun : Continuous toGroupEquiv.symm

@[ext] theorem chapter12TopologicalGroupEquiv_ext
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    {e₁ e₂ : Chapter12TopologicalGroupEquiv G H}
    (h : e₁.toGroupEquiv = e₂.toGroupEquiv) : e₁ = e₂ := by
  cases e₁
  cases e₂
  cases h
  rfl

/-- A continuous multiplicative character. -/
structure Chapter12ContinuousCharacter
    (G A : Type*) [Group G] [Group A]
    [TopologicalSpace G] [TopologicalSpace A] where
  hom : G →* A
  continuous_hom : Continuous hom

@[ext] theorem chapter12ContinuousCharacter_ext
    {G A : Type*} [Group G] [Group A]
    [TopologicalSpace G] [TopologicalSpace A]
    {χ ψ : Chapter12ContinuousCharacter G A}
    (h : χ.hom = ψ.hom) : χ = ψ := by
  cases χ
  cases ψ
  cases h
  rfl

/-- Pullback of a continuous character along a continuous group homomorphism. -/
def chapter12CharacterPullback
    {G H A : Type*} [Group G] [Group H] [Group A]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace A]
    (f : G →* H) (hf : Continuous f)
    (χ : Chapter12ContinuousCharacter H A) :
    Chapter12ContinuousCharacter G A :=
  { hom := χ.hom.comp f
    continuous_hom := χ.continuous_hom.comp hf }

/-- Relative compactness of a character image. -/
def chapter12RelativeCompactRange
    {G A : Type*} [Group G] [Group A]
    [TopologicalSpace G] [TopologicalSpace A]
    (χ : Chapter12ContinuousCharacter G A) : Prop :=
  IsCompact (closure (Set.range χ.hom))

/-- The infinite reciprocity interface supplied by the inverse-limit construction.

DEPENDENCY_GUESS: the inverse-limit construction in the missing preceding
chapters supplies the continuity, injectivity, and density fields. -/
structure Chapter12ReciprocityLimit
    (K G : Type*) [Field K] [CommGroup G]
    [TopologicalSpace Kˣ] [TopologicalSpace G] where
  source_topological_group : IsTopologicalGroup Kˣ
  target_topological_group : IsTopologicalGroup G
  compact : IsCompact (Set.univ : Set G)
  hausdorff : T2Space G
  totally_disconnected : TotallyDisconnectedSpace G
  map : Kˣ →* G
  continuous_map : Continuous map
  injective_map : Function.Injective map
  dense_range_map : Dense (Set.range map)

/-- A profinite-completion interface.  The carrier is supplied by the
inverse-limit construction; the universal property is used only through its
embedding and its resulting equivalences in this chapter. -/
structure Chapter12CompletionData
    (G Ghat : Type*) [CommGroup G] [CommGroup Ghat]
    [TopologicalSpace G] [TopologicalSpace Ghat] where
  source_topological_group : IsTopologicalGroup G
  target_topological_group : IsTopologicalGroup Ghat
  compact : IsCompact (Set.univ : Set Ghat)
  hausdorff : T2Space Ghat
  totally_disconnected : TotallyDisconnectedSpace Ghat
  embedding : G →* Ghat
  continuous_embedding : Continuous embedding
  injective_embedding : Function.Injective embedding
  dense_embedding : Dense (Set.range embedding)

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
