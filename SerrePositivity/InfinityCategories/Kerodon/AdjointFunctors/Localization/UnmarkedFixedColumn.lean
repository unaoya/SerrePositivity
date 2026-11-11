module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCut
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnCutSquare

/-!
# 同じ固定生成矢で切った元の列と全縦射の圏

概要：固定した生成矢で切れる元の列を持つ zigzag の圏を作り、元の全縦射を保持する。
方針：射を元の Zigzag.Hom とし、切断の一意性から追加の条件を課さない。
規約：元の対象・列と全縦射を変更しない。
使われ方：接頭列と残りの実際の自然変換への分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
  (X Y : Paths C) (i : Fin w.length) (a : Quiver.Total C)

structure ColumnCut where
  row : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y
  cut : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a (row.arrow i)

namespace ColumnCut

instance category : Category.{max u v} (ColumnCut W w X Y i a) where
  Hom P Q := P.row ⟶ Q.row
  id P := 𝟙 P.row
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def forget : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y where
  obj P := P.row
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def sourceEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a ⥤ Paths C :=
  forget W w X Y i a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (w.source i)

def targetEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a ⥤ Paths C :=
  forget W w X Y i a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (w.target i)

end ColumnCut
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
