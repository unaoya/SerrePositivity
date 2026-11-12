module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyCoordinates
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
概要：閉じた次数一の斉次作用素が誘導するホモロジー射。
方針：隣接短複体の外側二成分に負号を付けて短複体射にする。
規約：全整数次数を使い、零次数鎖写像への置換を仮定しない。
使われ方：coherent bar の一次列と長完全列の連結射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] {K L : Complex R}
  (z : Cochain K L 1) (hz : δ 1 2 z = 0)
include hz

lemma dgDegreeOneCochain_comm (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) :
    z.v p q hpq ≫ L.d q r + K.d p q ≫ z.v q r hqr = 0 := by
  have h := Cochain.congr_v hz p r (by omega)
  rw [δ_v 1 2 (by rfl) z p r (by omega) q q (by omega) hpq, Cochain.zero_v,
    Int.negOnePow_even 2 ⟨1, by decide⟩, one_smul] at h
  exact h

def dgDegreeOneShortComplexMap (q : ℤ) : K.sc' (q - 1) q (q + 1) ⟶
    L.sc' q (q + 1) (q + 2) where
  τ₁ := -z.v (q - 1) q (by omega)
  τ₂ := z.v q (q + 1) rfl
  τ₃ := -z.v (q + 1) (q + 2) (by omega)
  comm₁₂ := by
    change (-z.v (q - 1) q (by omega)) ≫ L.d q (q + 1) =
      K.d (q - 1) q ≫ z.v q (q + 1) rfl
    rw [Preadditive.neg_comp]
    exact neg_eq_iff_add_eq_zero.mpr (dgDegreeOneCochain_comm R z hz (q - 1) q (q + 1)
      (by omega) rfl)
  comm₂₃ := by
    change z.v q (q + 1) rfl ≫ L.d (q + 1) (q + 2) =
      K.d q (q + 1) ≫ (-z.v (q + 1) (q + 2) (by omega))
    rw [Preadditive.comp_neg]
    exact eq_neg_iff_add_eq_zero.mpr (dgDegreeOneCochain_comm R z hz q (q + 1) (q + 2)
      rfl (by omega))

def dgDegreeOneHomologyMap (q : ℤ) : K.homology q ⟶ L.homology (q + 1) :=
  (K.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom ≫
    ShortComplex.homologyMap (dgDegreeOneShortComplexMap R z hz q) ≫
      (L.homologyIsoSc' q (q + 1) (q + 2) (by simp) (by simp; omega)).inv

lemma dgDegreeOneCochain_cycles_closed (q : ℤ) :
    (K.iCycles q ≫ z.v q (q + 1) rfl) ≫ L.d (q + 1) (q + 2) = 0 := by
  have h := eq_neg_iff_add_eq_zero.mpr
    (dgDegreeOneCochain_comm R z hz q (q + 1) (q + 2) rfl (by omega))
  rw [Category.assoc, h, Preadditive.comp_neg, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp, neg_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
