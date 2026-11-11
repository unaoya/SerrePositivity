module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterCoefficients
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarInverseParameterCoefficient_recovery {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseParameterCoefficient (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c)
      J (-(r : ℤ)) hJ (by rw [hc]; push_cast; omega) =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseParameterCoefficient
  change (-(r : ℤ)).negOnePow • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom R D F hMC y c
    J (-(r : ℤ)) hJ (by rw [hc]; push_cast; omega) = _
  rw [eq_of_heq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y c J
    (-(r : ℤ)) hJ (by rw [hc]; push_cast; omega) r hc), Int.negOnePow_neg,
    smul_smul, Int.units_mul_self, one_smul]

lemma dgCoherentBarInverseParameterCoefficient_recovery_heq {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (r : ℕ) (hc : J.card = r + 1) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseParameterCoefficient
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c) J k hJ hk)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc) := by
  have hkr : k = -(r : ℤ) := by rw [hc] at hk; push_cast at hk; omega
  cases hkr
  exact heq_of_eq (dgCoherentBarInverseParameterCoefficient_recovery R D F hMC y c J r hc hJ)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
