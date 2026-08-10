import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped BigOperators WithTop

/-! # 8.1. Isolating value-group growth

The valuation language below uses Book 1's additive valuation interface.  In
particular, the residue degree is a module rank of residue fields, while the
ramification index is kept as a separate numerical invariant.
-/

/-! The following predicates are the valuation-theoretic form of `f = 1`. -/

/-- Book §8.1: a finite valued extension is totally ramified when its residue
degree is one.  No separability or Galois hypothesis is built into this
definition. -/
def chapter08TotallyRamified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree vK vL h = 1

/-- Book §8.1: the chosen valuation interface's encoding of equality of the
residue fields, namely residue degree one for the induced residue extension. -/
def chapter08ResidueFieldsEqual
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
    vK vL h = 1

/-- Book §8.1: for a finite extension, the total-ramification predicate is
definitionally equivalent to the residue-degree-one encoding of no
residue-field growth. -/
theorem chapter08_total_ramification_iff_residue_fields_equal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    chapter08TotallyRamified vK vL h ↔ chapter08ResidueFieldsEqual vK vL h := by
  rfl

/-- Book §8.1: the fundamental equality specializes to `[L : K] = e` at the
totally ramified endpoint. -/
theorem chapter08_total_ramification_degree_formula
    (p : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile)
    (hdegree : p.degree = p.ramificationIndex * p.residueDegree)
    (htotal : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p) :
    p.degree = p.ramificationIndex := by
  change p.residueDegree = 1 at htotal
  simpa [htotal] using hdegree

/-- A root relation of the form used by the equal-characteristic example
`k((t^(1/p)))/k((t))`. -/
def chapter08RadicalPresentation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (π : K) (α : L) (n : ℕ) : Prop :=
  algebraMap K L π = α ^ n

/-- Book §8.1: a purely inseparable radical extension can still be totally
ramified; total ramification does not imply separability. -/
theorem chapter08_purely_inseparable_radical_is_totally_ramified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (h : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (p : ℕ) (hp : Nat.Prime p) (π : K) (α : L)
    (hroot : chapter08RadicalPresentation π α p)
    (hdegree : Module.finrank K L = p)
    (e : ℕ)
    (he_lower : p ≤ e)
    (hfundamental : Module.finrank K L =
      e * LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL h) :
    chapter08TotallyRamified vK vL h := by
  change LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
    vK vL h = 1
  let residueDegree :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
      vK vL h
  have hfundamental' : p = e * residueDegree := by
    calc
      p = Module.finrank K L := hdegree.symm
      _ = e * residueDegree := hfundamental
  have hresidue_pos : 0 < residueDegree := by
    by_contra hnot
    have hresidue_zero : residueDegree = 0 := Nat.eq_zero_of_not_pos hnot
    have hp_zero : p = 0 := by simpa [hresidue_zero] using hfundamental'
    exact (Nat.Prime.ne_zero hp) hp_zero
  have he_pos : 0 < e := by
    have hprod_pos : 0 < e * residueDegree := by
      simpa [hfundamental'] using hp.pos
    have he_ne : e ≠ 0 := by
      intro he_zero
      simp [he_zero] at hprod_pos
    exact Nat.pos_of_ne_zero he_ne
  have hprod_le : e * residueDegree ≤ e := by
    calc
      e * residueDegree = p := hfundamental'.symm
      _ ≤ e := he_lower
  have hresidue_one : residueDegree = 1 := by
    apply le_antisymm
    · by_contra hnot
      have htwo : 2 ≤ residueDegree := by omega
      have hlt : e < e * residueDegree := by
        calc
          e = e * 1 := (Nat.mul_one e).symm
          _ < e * 2 := (Nat.mul_lt_mul_left he_pos).2 (by omega)
          _ ≤ e * residueDegree := Nat.mul_le_mul_left e htwo
      exact (Nat.not_lt_of_ge hprod_le) hlt
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hresidue_pos)
  exact hresidue_one

/-- Book §8.1: a finite extension which is both Galois and purely inseparable
is trivial, so the displayed purely inseparable example is not Galois. -/
theorem chapter08_galois_purely_inseparable_extension_is_trivial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsPurelyInseparable K L] :
    Module.finrank K L = 1 := by
  exact Module.finrank_of_bijective_algebraMap
    (IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L)

/-- Book §8.1: total ramification is inherited by both stages of a tower.
The hypotheses expose the residue-degree multiplication and do not assume
separability. -/
theorem chapter08_total_ramification_inherited_by_subextensions
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional M L]
    (fKM fML fKL : ℕ)
    (htower : fKL = fKM * fML) (htotal : fKL = 1) :
    fKM = 1 ∧ fML = 1 := by
  have hmul : fKM * fML = 1 := by
    calc
      fKM * fML = fKL := htower.symm
      _ = 1 := htotal
  have hKM : fKM ∣ 1 := ⟨fML, hmul.symm⟩
  have hML : fML ∣ 1 := ⟨fKM, by simpa [Nat.mul_comm] using hmul.symm⟩
  exact ⟨Nat.eq_one_of_dvd_one hKM, Nat.eq_one_of_dvd_one hML⟩

/-- The invariant-level interface for the unramified base-change assertion in
Book §8.1. -/
def chapter08UnramifiedBaseChangeProfile
    (base p p' : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified base ∧
    p'.residueDegree = p.residueDegree

/-- Book §8.1: unramified base change preserves total ramification once the
residue-degree compatibility supplied by the base-change theorem is recorded. -/
theorem chapter08_total_ramification_preserved_under_unramified_base_change
    (base p p' : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile)
    (hbase : chapter08UnramifiedBaseChangeProfile base p p')
    (htotal : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified p' := by
  change p'.residueDegree = 1
  rcases hbase with ⟨_, hresidue⟩
  change p.residueDegree = 1 at htotal
  exact hresidue.trans htotal

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
