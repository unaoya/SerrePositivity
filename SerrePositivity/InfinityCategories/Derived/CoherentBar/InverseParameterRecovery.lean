module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterCoefficients
/-!
概要：比較射の像では、逆構成のパラメーター係数が元の余錐族の Hom を回収する。
方針：右 pinched 規約の次数符号と逆構成の次数符号を二回作用させて消す。
規約：任意のパラメーター部分集合と全次数を扱う。
使われ方：逆比較と元の余錐族の全混合成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarInverseParameterCoefficient_recovery {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    dgCoherentBarInverseParameterCoefficient (dgCoherentBarCoconeLinearData R D F hMC y c)
      J (-(r : ℤ)) hJ (by rw [hc]; push_cast; omega) =
    dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc := by
  unfold dgCoherentBarInverseParameterCoefficient
  change (-(r : ℤ)).negOnePow • dgCoherentBarCoconeSubsetHom R D F hMC y c
    J (-(r : ℤ)) hJ (by rw [hc]; push_cast; omega) = _
  rw [eq_of_heq (dgCoherentBarCoconeSubsetHom_heq R D F hMC y c J
    (-(r : ℤ)) hJ (by rw [hc]; push_cast; omega) r hc), Int.negOnePow_neg,
    smul_smul, Int.units_mul_self, one_smul]

lemma dgCoherentBarInverseParameterCoefficient_recovery_heq {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (r : ℕ) (hc : J.card = r + 1) :
    HEq (dgCoherentBarInverseParameterCoefficient
      (dgCoherentBarCoconeLinearData R D F hMC y c) J k hJ hk)
      (dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc) := by
  have hkr : k = -(r : ℤ) := by rw [hc] at hk; push_cast at hk; omega
  cases hkr
  exact heq_of_eq (dgCoherentBarInverseParameterCoefficient_recovery R D F hMC y c J r hc hJ)

end SerrePositivity.InfinityCategories
