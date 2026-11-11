module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterComposite
/-!
概要：逆構成のパラメーター側の全 HA 項を、標準面の高次 Hom と native 列の係数で表示する。
方針：削除成分を面へ戻し、切断合成を最後の面だけにまとめる。
規約：最後の内部頂点にも同じ有限和の式を使う。
使われ方：混合 HA 右辺から標準面の符号付き境界を回収する。
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
  (N : _root_.SerrePositivity.DifferentialGraded.RightModule R D)

lemma dgCoherentBarInverseFullComposite_parameter
    {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullComposite
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      (if j = Fin.last m then _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceColumn R D F hMC N f s
        (Fin.last (m + 1)) else 0) := by
  classical
  by_cases hj : j = Fin.last m
  · subst j
    rw [ite_eq_left rfl]
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullComposite_parameter_last R D F hMC N f s
  · rw [ite_eq_right hj, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullComposite_parameter_zero R D F hMC N f s j hj]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_source R D F hMC N f s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_target R D F hMC N f s) rfl

lemma dgCoherentBarInverseFullTerm_parameter {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      ((((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceColumn R D F hMC N f s j.castSucc -
          if j = Fin.last m then _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceColumn R D F hMC N f s
            (Fin.last (m + 1)) else 0)) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm_eq_composite, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm_sign_right,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm_sign]
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_source R D F hMC N f s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_target R D F hMC N f s) rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_source R D F hMC N f s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_target R D F hMC N f s) rfl
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullErase_parameter R D F hMC N f s j
  · exact dgCoherentBarInverseFullComposite_parameter R D F hMC N f s j

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
