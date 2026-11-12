module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSubsetFactorization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterRightCut
/-!
概要：動く右面のパラメーター削除・前部・後部の三成分を型付きで保持する。
方針：削除と前部には回収 Hom、後部には元の右面の実 HA 成分を使う。
規約：定値性による消去はせず、動く切断点の対象を保つ。
使われ方：標準 Hom の持ち上げのパラメーター HA 境界式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

def dgCoherentBarParameterPrefix {m : ℕ} (j : Fin (m + 1)) : Finset (Fin (m + 2)) :=
  Finset.univ.filter (· ≤ j.castSucc)

lemma dgCoherentBarParameterPrefix_card {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterPrefix j).card = j.val + 1 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_card (m + 1) j.castSucc

lemma dgCoherentBarParameterPrefix_nonempty {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterPrefix j).Nonempty :=
  ⟨j.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩

lemma dgCoherentBarParameterPrefix_max {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterPrefix j).max' (dgCoherentBarParameterPrefix_nonempty j) =
      j.castSucc := by
  apply le_antisymm
  · exact Finset.max'_le (dgCoherentBarParameterPrefix j)
      (dgCoherentBarParameterPrefix_nonempty j) j.castSucc
      (fun x hx => (Finset.mem_filter.mp hx).2)
  · exact Finset.le_max' (dgCoherentBarParameterPrefix j) j.castSucc
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)

lemma dgCoherentBarParameterErase_nonempty {m : ℕ} (j : Fin (m + 1)) :
    ((Finset.univ : Finset (Fin (m + 2))).erase j.castSucc).Nonempty :=
  ⟨Fin.last (m + 1), Finset.mem_erase.mpr
    ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩⟩

lemma dgCoherentBarParameterErase_max {m : ℕ} (j : Fin (m + 1)) :
    ((Finset.univ : Finset (Fin (m + 2))).erase j.castSucc).max'
      (dgCoherentBarParameterErase_nonempty j) = Fin.last (m + 1) := by
  apply le_antisymm
  · exact Fin.le_last _
  · exact Finset.le_max' _ _ (Finset.mem_erase.mpr
      ⟨ne_of_gt (Fin.castSucc_lt_last _), Finset.mem_univ _⟩)

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

def dgCoherentBarCoconeLiftParameterErase {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F c) (-(m : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport rfl
    (congrArg (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
      (dgCoherentBarParameterErase_max j)) rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c (Finset.univ.erase j.castSucc)
      (-(m : ℤ)) (dgCoherentBarParameterErase_nonempty j) (by simp))

def dgCoherentBarCoconeLiftParameterPrefix {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj j.castSucc) (-(j.val : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport rfl
    (congrArg (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj)
      (dgCoherentBarParameterPrefix_max j)) rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c (dgCoherentBarParameterPrefix j)
      (-(j.val : ℤ)) (dgCoherentBarParameterPrefix_nonempty j)
      (by rw [dgCoherentBarParameterPrefix_card]; push_cast; omega))

def dgCoherentBarCoconeLiftParameterTail {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).obj j.castSucc)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F c) ((j.val : ℤ) - (m : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport rfl rfl (show 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j).card : ℤ) =
      (j.val : ℤ) - (m : ℤ) by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_card]
    have := j.isLt
    omega)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m + 1⦌) c).hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
      (2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j).card : ℤ)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_two j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_min j) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_max j) rfl)

def dgCoherentBarCoconeLiftParameterTerm {m : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m + 1⦌) (j : Fin (m + 1)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F c) (-(m : ℤ)) :=
  (((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
    (dgCoherentBarCoconeLiftParameterErase R D F hMC c j -
      _root_.SerrePositivity.DifferentialGraded.compose R (dgCoherentBarCoconeLiftParameterTail R D F c j)
        (dgCoherentBarCoconeLiftParameterPrefix R D F hMC c j)
        (show -(j.val : ℤ) + ((j.val : ℤ) - (m : ℤ)) = -(m : ℤ) by omega))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
