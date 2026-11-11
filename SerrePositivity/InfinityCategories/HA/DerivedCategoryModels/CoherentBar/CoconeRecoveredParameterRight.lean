module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftParameterData
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredRightHom
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents
/-!
概要：回収した一点下のデータについて、パラメーターで切った HA 右因子を、動く右面の実成分へ直す。
方針：右区間の尾部集合の像と、純粋右面の成分比較を使う。
規約：定値性を仮定せず、実 dg HA 成分を保持する。
使われ方：全切断合成を型付きの回収 HA 項へ移す。
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

lemma dgCoherentBarCoconeRecoveredFullRight_parameter {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c) (j.natAdd 0))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).hom
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
        (2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j).card : ℤ)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_two j)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_min j) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_max j) rfl) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c)
  let L := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j
  have hj : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 (m + 1) j.castSucc =
      (j.natAdd 0).succ.castSucc := Fin.ext (by
    change 0 + 1 + j.val = 0 + j.val + 1
    omega)
  have hl : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 (m + 1) (Fin.last (m + 1)) =
      Fin.last (0 + (m + 1) + 1) := Fin.ext (by
    change 0 + 1 + (m + 1) = 0 + (m + 1) + 1
    omega)
  have hSet : L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 (m + 1)) =
      (Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
        ((j.natAdd 0).succ.castSucc ≤ ·) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_right_le
      (Finset.univ : Finset (Fin (0 + 1)))
      (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hd : (2 - (((Finset.univ : Finset (Fin (0 + (m + 1) + 2))).filter
      ((j.natAdd 0).succ.castSucc ≤ ·)).card : ℤ)) = 2 - (L.card : ℤ) := by
    rw [← hSet, Finset.card_image_of_injective _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective 0 (m + 1))]
  have hPure := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_pure_right_hom_heq R D F hMC c L
    j.castSucc (Fin.last (m + 1)) (2 - (L.card : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_two j) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_min j)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_max j) rfl
  refine HEq.trans ?_ hPure
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSet.symm hj.symm hl.symm hd

lemma dgCoherentBarCoconeRecoveredFullRight_parameter_tail {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c) (j.natAdd 0))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterTail R D F c j) := by
  refine (dgCoherentBarCoconeRecoveredFullRight_parameter R D F hMC c j).trans ?_
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftParameterTail
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
