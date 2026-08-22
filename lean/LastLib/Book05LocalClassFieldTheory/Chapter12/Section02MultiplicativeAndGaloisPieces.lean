import LastLib.Book05LocalClassFieldTheory.Chapter12.Core
import LastLib.Book05LocalClassFieldTheory.Chapter07.Section03DensityAndSurjectivity

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.2. Multiplicative pieces and Galois pieces -/

/-- The image definitions used for inertia and higher ramification. -/
def chapter12GaloisInertia
    {K k G : Type*} [Field K] [Field k] [Group G]
    (C : Chapter12LocalCoordinates K k) (reciprocity : Kˣ →* G) :
    Subgroup G :=
  Subgroup.map reciprocity C.units

def chapter12GaloisRamification
    {K k G : Type*} [Field K] [Field k] [Group G]
    (C : Chapter12LocalCoordinates K k) (reciprocity : Kˣ →* G)
    (n : ℕ) : Subgroup G :=
  Subgroup.map reciprocity (C.principalUnits n)

/-- The finite-level multiplicative/Galois dictionary, with the reduction map
and its canonical unit-kernel identification explicit. -/
structure Chapter12GaloisPieceDictionary
    (K k G Q : Type*) [Field K] [Field k] [CommGroup G] [Finite G] [Group Q] where
  coordinates : Chapter12LocalCoordinates K k
  reciprocity : Kˣ →* G
  inertia : Subgroup G
  ramification : ℕ → Subgroup G
  reduction : G →* Q
  reduction_kernel :
    reduction.ker = inertia
  reduction_surjective : Function.Surjective reduction
  finite_quotient : Finite Q
  arithmeticFrobenius : Q
  uniformizer_mod_inertia :
    reduction (reciprocity coordinates.uniformizer) = arithmeticFrobenius
  inertia_eq_units :
    inertia = chapter12GaloisInertia coordinates reciprocity
  ramification_eq_principal : ∀ n,
    ramification n = chapter12GaloisRamification coordinates reciprocity n

/-- The quotient by units is the integer valuation coordinate. -/
theorem chapter12_valuation_coordinate_is_integer_quotient
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) :
    Nonempty (Kˣ ⧸ C.units ≃* Multiplicative ℤ) := by
  exact ⟨C.valuation_quotient⟩

/-- The zeroth unit level is the abelian inertia subgroup. -/
theorem chapter12_units_are_exactly_abelian_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    D.inertia = chapter12GaloisInertia D.coordinates D.reciprocity := by
  exact D.inertia_eq_units

/-- The residue-unit quotient is the tame abelian inertia coordinate. -/
theorem chapter12_residue_units_are_tame_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    Nonempty
      ((D.coordinates.units ⧸
          ((D.coordinates.principalUnits 1).comap
            D.coordinates.units.subtype)) ≃* kˣ) := by
  exact ⟨D.coordinates.residue_units⟩

/-- Principal units are the wild abelian inertia coordinate. -/
theorem chapter12_principal_units_are_wild_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    D.ramification 1 =
      chapter12GaloisRamification D.coordinates D.reciprocity 1 := by
  exact D.ramification_eq_principal 1

/-- Every higher unit level maps to the matching upper-numbered ramification
subgroup in the book-facing normalization. -/
theorem chapter12_higher_units_are_higher_ramification
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) (n : ℕ) :
    D.ramification n =
      chapter12GaloisRamification D.coordinates D.reciprocity n := by
  exact D.ramification_eq_principal n

/- The profinite integer coordinate is the canonical Chapter 8 object. -/
abbrev Chapter12ProfiniteIntegerCoordinate : Type _ :=
  LastLib.Book05LocalClassFieldTheory.Chapter08.Chapter08ProfiniteIntegers

/-- The integer valuation powers are dense in the profinite Frobenius line. -/
theorem chapter12_integer_valuation_powers_are_dense :
      Dense (Set.range
      LastLib.Book05LocalClassFieldTheory.Chapter08.chapter08IntegerToProfiniteCompletionHom) := by
  change Dense (Set.range
    LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07IntegerToProfiniteCompletionHom)
  exact LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07_integer_image_dense_and_proper.1

/-- The arithmetic Frobenius class has lifts, but no distinguished lift through
inertia is supplied by the quotient. -/
def chapter12ArithmeticFrobeniusLifts
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) : Set G :=
  {g | D.reduction g = D.arithmeticFrobenius}

theorem chapter12_arithmetic_frobenius_lifts_nonempty
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    (chapter12ArithmeticFrobeniusLifts D).Nonempty := by
  exact ⟨D.reciprocity D.coordinates.uniformizer, D.uniformizer_mod_inertia⟩

/-- The residue-reduction kernel is the inertia subgroup. -/
theorem chapter12_reduction_kernel_is_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    D.reduction.ker = D.inertia := by
  exact D.reduction_kernel

theorem chapter12_reduction_is_surjective
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    Function.Surjective D.reduction := by
  exact D.reduction_surjective

theorem chapter12_frobenius_lifts_differ_by_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q)
    (hkernel : D.reduction.ker =
      D.inertia)
    {g h : G} (hg : g ∈ chapter12ArithmeticFrobeniusLifts D)
    (hh : h ∈ chapter12ArithmeticFrobeniusLifts D) :
    g⁻¹ * h ∈ D.inertia := by
  sorry

theorem chapter12_uniformizer_has_arithmetic_frobenius_image
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Finite G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    D.reduction (D.reciprocity D.coordinates.uniformizer) =
      D.arithmeticFrobenius := by
  exact D.uniformizer_mod_inertia

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
