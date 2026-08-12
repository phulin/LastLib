import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Section01FiberwiseEulerCharacteristics

namespace LastLib
namespace Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
namespace Chapter08

open AlgebraicGeometry CategoryTheory

noncomputable section

/-! ## 8.2 Flatness forces constancy -/

/- The pointwise local constancy statement for the Euler-characteristic values
   used in the proof of the constancy theorem. -/
theorem chapter08_hilbert_function_locally_constant
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (hflat : Chapter08FlatOver F.family.f E.sheaf) (n : ℕ) :
    Chapter08LocallyConstant (fun s => D.eulerCharacteristic s n) := by
  sorry

/- If the sheaf is flat over the base, its fiber Hilbert polynomial is locally
   constant. -/
theorem chapter08_hilbert_polynomial_locally_constant
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (hflat : Chapter08FlatOver F.family.f E.sheaf) :
    Chapter08LocallyConstant (fun s => D.fiberPolynomial s) := by
  sorry

/- The polynomial values in a degree bound determine the whole fiber polynomial. -/
theorem chapter08_fiber_polynomial_eq_of_values
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) {s t : F.family.S} {n : ℕ}
    (hvalues : ∀ i ≤ D.dimension_bound,
      (D.fiberPolynomial s).value (n + i) =
        (D.fiberPolynomial t).value (n + i)) :
    D.fiberPolynomial s = D.fiberPolynomial t := by
  apply chapter08_numericalPolynomial_ext_of_degree_le
  · exact D.polynomial_degree_le s
  · exact D.polynomial_degree_le t
  · exact hvalues

/- On a connected base the locally constant fiber polynomial is constant. -/
theorem chapter08_fiber_hilbert_polynomial_constant_on_connected_base
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (hflat : Chapter08FlatOver F.family.f E.sheaf)
    (hconnected : _root_.IsConnected (Set.univ : Set F.family.S)) :
    ∀ s t : F.family.S, D.fiberPolynomial s = D.fiberPolynomial t := by
  sorry

/- The same conclusion holds on every connected subset, hence on connected
   components of the base. -/
theorem chapter08_fiber_hilbert_polynomial_constant_on_connected_set
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (hflat : Chapter08FlatOver F.family.f E.sheaf)
    {C : Set F.family.S} (hconnected : _root_.IsConnected C) :
    ∀ s ∈ C, ∀ t ∈ C, D.fiberPolynomial s = D.fiberPolynomial t := by
  sorry

/-!
The following profile records the concrete family in the failure example.  The
base is `Spec k[t]` at the coordinate-ring level, and the ambient ring is the
polynomial ring in `x` over `k[t]`; the two generators are exactly `(tx, x²)`.
The actual scheme-fiber length calculation is kept as a local interface because
the pinned snapshot does not provide the preceding affine-family API.
-/

abbrev chapter08JumpBaseRing (k : Type*) [CommRing k] := Polynomial k

abbrev chapter08JumpAmbientRing (k : Type*) [CommRing k] := Polynomial (Polynomial k)

def chapter08JumpStructureMap (k : Type*) [CommRing k] :
    chapter08JumpBaseRing k →+* chapter08JumpAmbientRing k :=
  Polynomial.C

def chapter08JumpIdeal (k : Type*) [CommRing k] :
    Ideal (chapter08JumpAmbientRing k) :=
  Ideal.span ({
    Polynomial.C (Polynomial.X : Polynomial k) *
        (Polynomial.X : Polynomial (Polynomial k)),
    (Polynomial.X : Polynomial (Polynomial k)) ^ 2
  } : Set (Polynomial (Polynomial k)))

/- The coordinate ring of the displayed closed subscheme. -/
abbrev chapter08JumpQuotientRing (k : Type*) [CommRing k] :=
  chapter08JumpAmbientRing k ⧸ chapter08JumpIdeal k

/- The induced ring map from the base coordinate ring to the quotient. -/
def chapter08JumpQuotientMap (k : Type*) [CommRing k] :
    CommRingCat.of (chapter08JumpBaseRing k) ⟶
      CommRingCat.of (chapter08JumpQuotientRing k) :=
  CommRingCat.ofHom
    ((Ideal.Quotient.mk (chapter08JumpIdeal k)).comp (chapter08JumpStructureMap k))

/- The affine schemes underlying `Spec k[t]` and the displayed family. -/
def chapter08JumpBaseScheme (k : Type*) [CommRing k] : Scheme :=
  Spec (.of (chapter08JumpBaseRing k))

def chapter08JumpTotalScheme (k : Type*) [CommRing k] : Scheme :=
  Spec (.of (chapter08JumpQuotientRing k))

/- The quotient family morphism `Z ⟶ Spec k[t]`. -/
def chapter08JumpFamilyMap (k : Type*) [CommRing k] :
    chapter08JumpTotalScheme k ⟶ chapter08JumpBaseScheme k :=
  Scheme.Spec.map (chapter08JumpQuotientMap k).op

/- The expected length of the fiber in the `(tx,x²)` example. -/
def chapter08JumpFiberLength {k : Type*} [Field k] (t : k) : ℕ :=
  by
    classical
    exact if t = 0 then 2 else 1

/- The generic fiber is the reduced one-point fiber in the coordinate-ring model. -/
def chapter08JumpFiberIsReduced {k : Type*} [Field k] (t : k) : Prop := t ≠ 0

/- LOCAL_DEPENDENCY_GUESS: the fields below are the book-facing output of the
   affine fiber computation for the displayed ideal. -/
structure Chapter08JumpProfile (k : Type*) [Field k] where
  structureMap : chapter08JumpBaseRing k →+* chapter08JumpAmbientRing k
  structureMap_eq : structureMap = chapter08JumpStructureMap k
  ideal : Ideal (chapter08JumpAmbientRing k)
  ideal_eq : ideal = chapter08JumpIdeal k
  fiberLength : k → ℕ
  fiberLength_eq : ∀ t, fiberLength t = chapter08JumpFiberLength t
  fiberIsReduced : k → Prop
  fiberIsReduced_eq : ∀ t, fiberIsReduced t ↔ chapter08JumpFiberIsReduced t

/- The canonical numerical profile of the `(tx,x²)` failure family. -/
def chapter08JumpProfileCanonical (k : Type*) [Field k] : Chapter08JumpProfile k where
  structureMap := chapter08JumpStructureMap k
  structureMap_eq := rfl
  ideal := chapter08JumpIdeal k
  ideal_eq := rfl
  fiberLength := chapter08JumpFiberLength
  fiberLength_eq := fun _ => rfl
  fiberIsReduced := chapter08JumpFiberIsReduced
  fiberIsReduced_eq := fun _ => Iff.rfl

theorem chapter08_jump_fiber_length_generic {k : Type*} [Field k]
    {t : k} (ht : t ≠ 0) : chapter08JumpFiberLength t = 1 := by
  simp [chapter08JumpFiberLength, ht]

theorem chapter08_jump_fiber_length_special {k : Type*} [Field k] :
    chapter08JumpFiberLength (0 : k) = 2 := by
  simp [chapter08JumpFiberLength]

theorem chapter08_jump_profile_has_length_jump {k : Type*} [Field k] :
    (chapter08JumpProfileCanonical k).fiberLength 0 = 2 ∧
      (chapter08JumpProfileCanonical k).fiberLength 1 = 1 := by
  constructor
  · simp [chapter08JumpProfileCanonical, chapter08JumpFiberLength]
  · simp [chapter08JumpProfileCanonical, chapter08JumpFiberLength]

end
end Chapter08
end Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
end LastLib
