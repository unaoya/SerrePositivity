module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentMapNaturality

/-!
# 元の連結語の zigzag の左右の部分

概要：任意の向きを持つ元の前後の語を、元の頂点・全列から切り出す。
方針：連結語の左右の埋め込みを使い、元の列の両端だけを等式で移す。
規約：接合対象は元の zigzag の頂点であり、対象とともに動く。
使われ方：元の prefix/core/suffix の図式の抽出。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def leftObj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X (S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b (Fin.last a.length))) where
  vertex i := S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i)
  first := S.first
  last := rfl
  arrow i := eqToHom (congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_left a b i).symm) ≫
    S.arrow (i.castAdd b.length) ≫ eqToHom (congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_left a b i))
  backward_mem i hi :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2
      (S.backward_mem _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a b i).trans hi))

def rightObj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b (S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b (Fin.last a.length))) Y where
  vertex i := S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i)
  first := congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.jointVertex a b).symm
  last := S.last
  arrow i := eqToHom (congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_right a b i).symm) ≫
    S.arrow (i.natAdd a.length) ≫ eqToHom (congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_right a b i))
  backward_mem i hi :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2
      (S.backward_mem _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a b i).trans hi))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
