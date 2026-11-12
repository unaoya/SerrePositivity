module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardExtractPaths
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation

/-!
# 動く局所端点を持つ図式からの左右射列の抽出

概要：同じ左右の forward ブロックを動く端点を持つ図式から抽出する。
方針：元の頂点と列を使い、MovingHom の正方形を射列の自然性に移す。
規約：左右の長さ零も含む。局所端点の全縦射を保持する。
使われ方：元の任意の前後の語の中の中央列へのモデル圏的置換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {n m : ℕ}

def leftPathMap {X Y X' Y' : C} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X' Y'} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) :
    Extract.leftPath S ⟶ Extract.leftPath T :=
  ComposableArrows.homMk (fun i => f.app (Positions.leftVertex n m i)) (by
    intro i hi
    dsimp only [Extract.leftPath]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport.square_transport f _ _ _ (Positions.left_source n m ⟨i, hi⟩).symm
      (Positions.left_target n m ⟨i, hi⟩))

def rightPathMap {X Y X' Y' : C} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X' Y'} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) :
    Extract.rightPath S ⟶ Extract.rightPath T :=
  ComposableArrows.homMk (fun i => f.app (Positions.rightVertex n m i)) (by
    intro i hi
    dsimp only [Extract.rightPath]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram.columnDiagram]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport.square_transport f _ _ _ (Positions.right_source n m ⟨i, hi⟩).symm
      (Positions.right_target n m ⟨i, hi⟩))

variable {D : Type u'} [Category.{v'} D] {A B : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) A B)

def leftFunctor : D ⥤ ComposableArrows C n where
  obj d := Extract.leftPath (F.obj d)
  map f := leftPathMap (F.map f)
  map_id d := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun g => g.app (Positions.leftVertex n m i)) (F.map_id d)
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun h => h.app (Positions.leftVertex n m i)) (F.map_comp f g)

def rightFunctor : D ⥤ ComposableArrows C m where
  obj d := Extract.rightPath (F.obj d)
  map f := rightPathMap (F.map f)
  map_id d := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun g => g.app (Positions.rightVertex n m i)) (F.map_id d)
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun h => h.app (Positions.rightVertex n m i)) (F.map_comp f g)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingExtract
