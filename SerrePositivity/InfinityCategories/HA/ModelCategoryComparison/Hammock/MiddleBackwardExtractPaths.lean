module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackwardPositions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram

/-!
# 元の固定語の zigzag 圏から左右の forward 射列を抽出する

概要：元の頂点と隣接射を使い、左右の指定長の射列と全縦射を抽出する。
方針：元の列の端点を位置の等式で移し、標準の隣接射列の構成へ渡す。
規約：射列の長さは元の n,m。差の長さへの未証明の同一視を使わない。
使われ方：元の固定語の graph を添字とする Family の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {n m : ℕ} {X Y : C}

def leftPath (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) : ComposableArrows C n :=
  ComposableArrows.mkOfObjOfMapSucc (fun i => S.vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i))
    (fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn n m i)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i.castSucc) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i.succ)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.left_source n m i).symm (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.left_target n m i)).app S)

def rightPath (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) : ComposableArrows C m :=
  ComposableArrows.mkOfObjOfMapSucc (fun i => S.vertex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i))
    (fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn n m i)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i.castSucc) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i.succ)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.right_source n m i).symm (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.right_target n m i)).app S)

def leftPathMap {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPath S ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPath T :=
  ComposableArrows.homMk (fun i => f.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftVertex n m i)) (by
    intro i hi
    dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPath]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality.square_transport f _ _ _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.left_source n m ⟨i, hi⟩).symm
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.left_target n m ⟨i, hi⟩))

def rightPathMap {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPath S ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPath T :=
  ComposableArrows.homMk (fun i => f.app (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightVertex n m i)) (by
    intro i hi
    dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPath]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality.square_transport f _ _ _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.right_source n m ⟨i, hi⟩).symm
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.right_target n m ⟨i, hi⟩))

def leftFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y ⥤ ComposableArrows C n where
  obj := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPath
  map := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPathMap
  map_id _ := by
    apply NatTrans.ext
    funext i
    rfl
  map_comp _ _ := by
    apply NatTrans.ext
    funext i
    rfl

def rightFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y ⥤ ComposableArrows C m where
  obj := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPath
  map := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPathMap
  map_id _ := by
    apply NatTrans.ext
    funext i
    rfl
  map_comp _ _ := by
    apply NatTrans.ext
    funext i
    rfl

lemma leftPath_map_succ_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) (i : ℕ) (hi : i < n) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPath S).map' i (i + 1)) (S.arrow (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.leftColumn n m ⟨i, hi⟩)) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.leftPath, ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

lemma rightPath_map_succ_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) (i : ℕ) (hi : i < m) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPath S).map' i (i + 1)) (S.arrow (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.rightColumn n m ⟨i, hi⟩)) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract.rightPath, ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Extract
