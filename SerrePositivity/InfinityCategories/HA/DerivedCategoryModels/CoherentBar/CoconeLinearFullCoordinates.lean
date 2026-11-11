module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLinearData
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterFaces
/-!
概要：回収した pinched 成分族の全頂点と一点削除の成分を計算する。
方針：全頂点の列挙は恒等、一点削除の列挙は標準面であることを再利用する。
規約：右 pinched 規約への次数符号と整数次数の輸送を保持する。
使われ方：全頂点の線形方程式を既に証明した Hom の境界式へ帰着する。
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

lemma dgCoherentBarCoconeLinearData_full_component {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c).component Finset.univ (-(n : ℤ))
      Finset.univ_nonempty (by simp) =
      (n : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y c := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y c Finset.univ (-(n : ℤ))
    Finset.univ_nonempty (by simp) n (by simp)
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarUniv_orderHom, op_id, CategoryTheory.Functor.map_id_apply] at h
  exact eq_of_heq h

lemma dgCoherentBarCoconeLinearData_erase_component_heq {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m + 1⦌) (a : Fin (m + 2)) (k : ℤ)
    (hJ : ((Finset.univ : Finset (Fin (m + 2))).erase a).Nonempty)
    (hk : k = 1 - (((Finset.univ : Finset (Fin (m + 2))).erase a).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c).component
      (Finset.univ.erase a) k hJ hk)
      ((m : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).δ a c)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y c (Finset.univ.erase a)
    k hJ hk m (by simp)
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarErase_orderHom] at h
  exact h

lemma dgCoherentBarCoconeLinearData_erase_boundary_component {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m + 1⦌) (a : Fin (m + 2))
    (hJ : ((Finset.univ : Finset (Fin (m + 2))).erase a).Nonempty)
    (hk : -((m + 1 : ℕ) : ℤ) + 1 =
      1 - (((Finset.univ : Finset (Fin (m + 2))).erase a).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c).component
      (Finset.univ.erase a) (-((m + 1 : ℕ) : ℤ) + 1) hJ hk =
      (m : ℤ).negOnePow • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFaceHom R D F hMC y c a := by
  have h := dgCoherentBarCoconeLinearData_erase_component_heq R D F hMC y c a
    (-((m + 1 : ℕ) : ℤ) + 1) hJ hk
  have hF : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFaceHom R D F hMC y c a)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).δ a c)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
      (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega) _
  have hS := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq (R := R) (C := RightModule R D)
    rfl rfl (show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega)
    (m : ℤ).negOnePow _ _ hF
  exact eq_of_heq (h.trans hS.symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
