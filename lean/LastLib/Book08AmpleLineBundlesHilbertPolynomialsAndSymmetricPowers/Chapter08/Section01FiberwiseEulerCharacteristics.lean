import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies

namespace LastLib
namespace Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
namespace Chapter08

open AlgebraicGeometry

noncomputable section

/-!
## 8.1 Fiberwise Euler characteristics

The preceding chapter supplies the geometric construction of fibers and twists
when available.  `Chapter08FiberwiseHilbertData` records the numerical output of
that construction, including the formula
`Pₛ(n) = χ(Xₛ, Fₛ ⊗ Lₛⁿ)` through its named Euler-characteristic field.
-/

/-- The Hilbert function of a specified fiberwise data package. -/
def chapter08FiberHilbertFunction
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) : ℕ → ℤ :=
  D.eulerCharacteristic s

/-- The numerical Hilbert polynomial of a specified fiber. -/
def chapter08FiberHilbertPolynomial
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) :
    Chapter08NumericalPolynomial :=
  D.fiberPolynomial s

/-- The Euler characteristic of the `n`th fiber twist, in the notation of the
book. -/
def chapter08FiberEulerCharacteristic
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) (n : ℕ) : ℤ :=
  (chapter08FiberHilbertFunction D s) n

theorem chapter08_fiber_hilbert_function_eq_euler_characteristic
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) (n : ℕ) :
    chapter08FiberHilbertFunction D s n = D.eulerCharacteristic s n := by
  rfl

theorem chapter08_fiber_hilbert_polynomial_value
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) (n : ℕ) :
    (chapter08FiberHilbertPolynomial D s).value n =
      chapter08FiberEulerCharacteristic D s n := by
  exact D.fiberPolynomial_value s n

theorem chapter08_fiber_hilbert_polynomial_degree_le
    {F : Chapter08PolarizedFamily} {E : Chapter08FamilySheaf F}
    (D : Chapter08FiberwiseHilbertData E) (s : F.family.S) :
    (chapter08FiberHilbertPolynomial D s).degree ≤ D.dimension_bound := by
  exact D.polynomial_degree_le s

/-- Values at `d + 1` consecutive natural numbers determine polynomials of
degree at most `d`.  The theorem is stated for the integer-valued interface so
it can be used directly with fiber Hilbert functions. -/
theorem chapter08_numericalPolynomial_ext_of_degree_le
    {P Q : Chapter08NumericalPolynomial} {d n : ℕ}
    (hP : P.degree ≤ d) (hQ : Q.degree ≤ d)
    (hvalues : ∀ i ≤ d, P.value (n + i) = Q.value (n + i)) : P = Q := by
  sorry

/-- A local large-twist profile packages Serre vanishing on nearby fibers and
local freeness of the corresponding pushforward. -/
structure Chapter08SerreVanishingProfile
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E) where
  threshold : F.family.S → ℕ
  neighborhood : F.family.S → Set F.family.S
  neighborhood_open : ∀ s, IsOpen (neighborhood s)
  point_mem_neighborhood : ∀ s, s ∈ neighborhood s
  higher_cohomology_vanishes :
    ∀ (s t : F.family.S), t ∈ neighborhood s →
      ∀ n, threshold s ≤ n → ∀ i, 0 < i → D.cohomologyRank t n i = 0
  pushforward :
    ∀ (s : F.family.S) (n : ℕ), threshold s ≤ n →
      Chapter08PushforwardWitness E D (neighborhood s) n

/- LOCAL_DEPENDENCY_GUESS: this is the book-facing interface to relative Serre
   vanishing and cohomology-and-base-change, which are not in the pinned API. -/
theorem chapter08_serre_vanishing_and_base_change
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (D : Chapter08FiberwiseHilbertData E)
    (hflat : Chapter08FlatOver F.family.f E.sheaf) :
    Nonempty (Chapter08SerreVanishingProfile E D) := by
  sorry

end
end Chapter08
end Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
end LastLib
