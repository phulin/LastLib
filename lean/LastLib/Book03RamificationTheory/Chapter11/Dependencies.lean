import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Rep.Res
import LastLib.Book03RamificationTheory.Chapter09.Dependencies
import LastLib.Book03RamificationTheory.Chapter10.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter11

noncomputable section

open CategoryTheory
open LastLib.Book03RamificationTheory.Chapter05
open LastLib.Book03RamificationTheory.Chapter09
open scoped BigOperators

/-!
Shared interfaces for Book 3, Chapter 11.

`Chapter11RamificationData` is the finite, lower-numbered view consumed by the
Artin-character API.  The adapter immediately following it takes the
canonical Chapter 5 profile (and hence the Chapter 9 local/Hilbert setup when
one is available) as its filtration source.  The numerical degree and residue
hypotheses remain explicit inputs; no Chapter 11 conclusion is stored in the
adapter.
-/
structure Chapter11RamificationData (G : Type*) [Fintype G] [Group G] where
  /-- The lower-numbered ramification subgroups. -/
  lower : ℕ → Subgroup G
  /-- The inertia subgroup, exposed as the zeroth lower group. -/
  inertia : Subgroup G
  /-- Ramification index, residue degree, and a finite-support bound. -/
  e : ℕ
  f : ℕ
  bound : ℕ
  lower_zero : lower 0 = inertia
  lower_succ_le : ∀ i, lower (i + 1) ≤ lower i
  lower_eq_bot_of_bound_le : ∀ i, bound ≤ i → lower i = ⊥
  inertia_normal : inertia.Normal
  inertia_card : Nat.card inertia = e
  group_card : Fintype.card G = e * f
  e_pos : 0 < e
  f_pos : 0 < f
  /-- Non-inertia elements have zero displacement. -/
  support_outside_inertia :
    ∀ {σ : G}, σ ∉ inertia → ∀ i, σ ∉ lower i
  /-- Every lower level is stable under conjugation. -/
  lower_conj_invariant :
    ∀ i (g σ : G), σ ∈ lower i ↔ g * σ * g⁻¹ ∈ lower i
  /-- The residue extension hypothesis used by the classical `i_G` theory. -/
  residue_separable : Prop
  /-- Perfectness is kept separate because Hasse--Arf and Artin integrality
      use it in addition to separability. -/
  residue_perfect : Prop
  /-- A perfect residue field supplies the separability hypothesis. -/
  residue_perfect_implies_separable : residue_perfect → residue_separable

/-!
The canonical Chapter 5 profile records the lower groups and displacement, but
it intentionally does not package the residue degree or the perfect-residue
hypothesis used by Chapter 11.  This small context supplies exactly those
external local witnesses.  In particular, `group_card` is a degree identity,
not an Artin-character statement.
-/
structure Chapter11CanonicalRamificationContext
    {G : Type*} [Fintype G] [Group G]
    (P : Chapter05RamificationFiltration G) where
  residue_degree : ℕ
  residue_degree_pos : 0 < residue_degree
  group_card :
    Fintype.card G = Nat.card (P.lowerGroup 0) * residue_degree
  residue_separable : Prop
  residue_perfect : Prop
  residue_perfect_implies_separable :
    residue_perfect → residue_separable

/-!
Convert the canonical Chapter 5/9 lower profile to the finite API used by the
rest of this chapter.  The cutoff is the canonical Chapter 9 witness for
eventual triviality; the local subgroup, conjugacy, and displacement facts are
kept as obligations of this adapter rather than being inferred from an Artin
conclusion.
-/
noncomputable def chapter11RamificationDataOfChapter05
    {G : Type*} [Fintype G] [Group G]
    (P : Chapter05RamificationFiltration G)
    (C : Chapter11CanonicalRamificationContext P) :
    Chapter11RamificationData G where
  lower := fun i => P.lowerGroup (i : ℝ)
  inertia := P.lowerGroup 0
  e := Nat.card (P.lowerGroup 0)
  f := C.residue_degree
  bound := chapter09Cutoff P
  lower_zero := by
    norm_num
  lower_succ_le := by
    intro i
    apply P.lower_antitone
    norm_num
  lower_eq_bot_of_bound_le := by
    exact chapter09_lower_group_trivial_at_cutoff P
  inertia_normal := P.lower_normal 0
  inertia_card := by
    rfl
  group_card := C.group_card
  e_pos := by
    exact Nat.card_pos
  f_pos := C.residue_degree_pos
  support_outside_inertia := by
    intro σ hσ i hσi
    apply hσ
    exact (P.lower_antitone (by positivity)) hσi
  lower_conj_invariant := by
    intro i g σ
    constructor
    · intro hσ
      exact P.lower_normal (i : ℝ) |>.conj_mem σ hσ g
    · intro hσ
      have hσ' := P.lower_normal (i : ℝ) |>.conj_mem (g * σ * g⁻¹) hσ g⁻¹
      simpa [mul_assoc] using hσ'
  residue_separable := C.residue_separable
  residue_perfect := C.residue_perfect
  residue_perfect_implies_separable := C.residue_perfect_implies_separable

/- The Chapter 9 wrapper makes the source profile and its local residue
   certificate visible at the call site while reusing the Chapter 5 adapter. -/
noncomputable def chapter11RamificationDataOfChapter09
    {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter09ResidueField vK) (chapter09ResidueField vL)]
    [FiniteDimensional (chapter09ResidueField vK)
      (chapter09ResidueField vL)]
    (S : Chapter09HilbertFormulaSetup A B K L vK vL)
    (C : Chapter11CanonicalRamificationContext S.profile) :
    Chapter11RamificationData (Gal(L / K)) :=
  chapter11RamificationDataOfChapter05 S.profile C

noncomputable instance chapter11SubgroupFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/- A bookkeeping wrapper for a finite-Galois realization.  The group
  identification and residue witnesses are exposed here, while the actual
  identification of `D` with valuation-theoretic ramification data remains an
  explicit boundary for the preceding local-field chapters. -/
structure Chapter11FiniteGaloisRamificationContext
    {K L G : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype G] [Group G]
    (D : Chapter11RamificationData G) where
  group_identification : G ≃* Gal(L / K)
  residue_separable : D.residue_separable
  residue_perfect : D.residue_perfect

abbrev Chapter11Inertia
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) : Subgroup G := D.inertia

abbrev Chapter11LowerGroup
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (i : ℕ) : Subgroup G := D.lower i

theorem chapter11_lower_le_inertia
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (i : ℕ) : D.lower i ≤ D.inertia := by
  sorry

theorem chapter11_residue_separable_of_perfect
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (hperfect : D.residue_perfect) :
    D.residue_separable := by
  sorry

/-- The finite set of lower levels at which a group element occurs. -/
def chapter11LowerSupport
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) : Finset ℕ := by
  classical
  exact (Finset.range D.bound).filter (fun i => σ ∈ D.lower i)

/-- The finite lower displacement of a nonidentity element.

The source assigns `+∞` to the identity.  Since all Artin sums exclude that
element and this interface is Nat-valued, the identity is represented by the
zero sentinel instead. -/
def chapter11Displacement
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (σ : G) : ℕ :=
  by
    classical
    exact if σ = 1 then 0 else (chapter11LowerSupport D σ).card

theorem chapter11_displacement_eq_support_card_of_ne_one
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) {σ : G} (hσ : σ ≠ 1) :
    chapter11Displacement D σ = (chapter11LowerSupport D σ).card := by
  sorry

theorem chapter11_displacement_eq_zero_of_not_mem_inertia
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) {σ : G} (hσ : σ ∉ D.inertia) :
    chapter11Displacement D σ = 0 := by
  sorry

/-!
The conductor is recorded as a rational number.  This keeps the weighted
formula honest before Artin integrality is applied; integrality statements
below identify these rationals with nonnegative integers.
-/

/-- The rational weight attached to a lower level. -/
def chapter11LowerWeight
    {G : Type*} [Fintype G] [Group G]
    (D : Chapter11RamificationData G) (i : ℕ) : ℚ :=
  (Nat.card (D.lower i) : ℚ) / (Nat.card D.inertia : ℚ)

/-- The Artin conductor in its fixed-space, lower-numbered form. -/
def chapter11ArtinConductor
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ Finset.range D.bound,
    chapter11LowerWeight D i *
      (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ
        (D.lower i) : ℚ)

/-- The tame contribution, namely the codimension of inertia-fixed vectors. -/
def chapter11TameConductor
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : ℚ :=
  (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ D.inertia : ℚ)

/-- The Swan conductor, retaining the positive lower-numbered levels. -/
def chapter11SwanConductor
    {k G V : Type*} [Field k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : Chapter11RamificationData G) (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ Finset.Ico 1 D.bound,
    chapter11LowerWeight D i *
      (LastLib.Book03RamificationTheory.Chapter10.fixedSpaceCodim ρ
        (D.lower i) : ℚ)

end
end LastLib.Book03RamificationTheory.Chapter11
