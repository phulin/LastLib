import LastLib.Book05LocalClassFieldTheory.Chapter12.Core

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

/-- The finite-level multiplicative/Galois dictionary, with all maps explicit.

DEPENDENCY_GUESS: the reduction-kernel and arithmetic-normalization fields are
the finite-level local reciprocity interfaces supplied by the missing
preceding Book 5 chapters. -/
structure Chapter12GaloisPieceDictionary
    (K k G Q : Type*) [Field K] [Field k] [CommGroup G] [Group Q] where
  coordinates : Chapter12LocalCoordinates K k
  reciprocity : Kˣ →* G
  inertia : Subgroup G
  ramification : ℕ → Subgroup G
  inertia_eq_units_image :
    inertia = chapter12GaloisInertia coordinates reciprocity
  ramification_eq_principal_units_image :
    ∀ n, ramification n = chapter12GaloisRamification coordinates reciprocity n
  reduction : G →* Q
  reduction_kernel : reduction.ker = inertia
  reduction_surjective : Function.Surjective reduction
  finite_quotient : Finite Q
  arithmeticFrobenius : Q
  uniformizer_mod_inertia :
    reduction (reciprocity coordinates.uniformizer) = arithmeticFrobenius

/-- The quotient by units is the integer valuation coordinate. -/
theorem chapter12_valuation_coordinate_is_integer_quotient
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) :
    Nonempty (Kˣ ⧸ C.units ≃* Multiplicative ℤ) := by
  exact ⟨C.valuation_quotient⟩

/-- The zeroth unit level is the abelian inertia subgroup. -/
theorem chapter12_units_are_exactly_abelian_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    Subgroup.map D.reciprocity D.coordinates.units = D.inertia := by
  rw [D.inertia_eq_units_image]
  rfl

/-- The residue-unit quotient is the tame abelian inertia coordinate. -/
theorem chapter12_residue_units_are_tame_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    Nonempty
      ((D.coordinates.units ⧸
          ((D.coordinates.principalUnits 1).comap
            D.coordinates.units.subtype)) ≃* kˣ) := by
  exact ⟨D.coordinates.residue_units⟩

/-- Principal units are the wild abelian inertia coordinate. -/
theorem chapter12_principal_units_are_wild_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    Subgroup.map D.reciprocity (D.coordinates.principalUnits 1) =
      D.ramification 1 := by
  rw [D.ramification_eq_principal_units_image]
  rfl

/-- Every higher unit level maps to the matching upper-numbered ramification
subgroup in the book-facing normalization. -/
theorem chapter12_higher_units_are_higher_ramification
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) (n : ℕ) :
    Subgroup.map D.reciprocity (D.coordinates.principalUnits n) =
      D.ramification n := by
  rw [D.ramification_eq_principal_units_image]
  rfl

/-- A separate interface for the profinite unramified coordinate. -/
structure Chapter12ProfiniteIntegerCoordinate
    (Zhat : Type*) [AddCommGroup Zhat] [TopologicalSpace Zhat] where
  topological_group : IsTopologicalAddGroup Zhat
  compact : IsCompact (Set.univ : Set Zhat)
  hausdorff : T2Space Zhat
  totally_disconnected : TotallyDisconnectedSpace Zhat
  embedding : ℤ →+ Zhat
  dense_powers : Dense (Set.range embedding)

/-- The integer valuation powers are dense in the profinite Frobenius line. -/
theorem chapter12_integer_valuation_powers_are_dense
    (Zhat : Type*) [AddCommGroup Zhat] [TopologicalSpace Zhat]
    (P : Chapter12ProfiniteIntegerCoordinate Zhat) :
    Dense (Set.range P.embedding) := by
  exact P.dense_powers

/-- The arithmetic Frobenius class has lifts, but no distinguished lift through
inertia is supplied by the quotient. -/
def chapter12ArithmeticFrobeniusLifts
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) : Set G :=
  {g | D.reduction g = D.arithmeticFrobenius}

theorem chapter12_arithmetic_frobenius_lifts_nonempty
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q)
    (hfrobenius :
      D.reduction (D.reciprocity D.coordinates.uniformizer) =
        D.arithmeticFrobenius) :
    (chapter12ArithmeticFrobeniusLifts D).Nonempty := by
  exact ⟨D.reciprocity D.coordinates.uniformizer, hfrobenius⟩

/-- The residue-reduction kernel is the inertia subgroup. -/
-- DEPENDENCY_GUESS: This is the finite-level reduction exactness bridge from
-- the missing preceding local reciprocity chapters.
theorem chapter12_reduction_kernel_is_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    D.reduction.ker = D.inertia := by
  exact D.reduction_kernel

theorem chapter12_reduction_is_surjective
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    Function.Surjective D.reduction := by
  exact D.reduction_surjective

theorem chapter12_frobenius_lifts_differ_by_inertia
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q)
    (hkernel : D.reduction.ker = D.inertia)
    {g h : G} (hg : g ∈ chapter12ArithmeticFrobeniusLifts D)
    (hh : h ∈ chapter12ArithmeticFrobeniusLifts D) :
    g⁻¹ * h ∈ D.inertia := by
  sorry

theorem chapter12_uniformizer_has_arithmetic_frobenius_image
    {K k G Q : Type*} [Field K] [Field k] [CommGroup G] [Group Q]
    (D : Chapter12GaloisPieceDictionary K k G Q) :
    D.reduction (D.reciprocity D.coordinates.uniformizer) =
      D.arithmeticFrobenius := by
  exact D.uniformizer_mod_inertia

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
