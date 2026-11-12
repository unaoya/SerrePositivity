module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramFixed

/-!
# 元の前後の語の動く接合点を持つ図式

概要：元の固定端点の zigzag 圏上で左右の部分と接合点を図式にする。
方針：元の全縦射の制限の恒等・合成則と両端の成分回収を使う。
規約：局所接合点の評価関手は定数とは仮定しない。
使われ方：任意の prefix/core/suffix へのモデル圏的置換の接続。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def jointFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b (Fin.last a.length))

def leftDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y) C W a
    ((Functor.const _).obj X) jointFunctor where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.leftMap
  map_id _ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    rfl
  map_comp _ _ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    rfl
  first {S T} f := by
    change HEq (f.app 0) (𝟙 X)
    apply (conj_eqToHom_iff_heq _ _ S.first T.first).1
    simpa only [Category.id_comp, eqToHom_trans] using f.first
  last _ := HEq.rfl

def rightDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y) C W b
    jointFunctor ((Functor.const _).obj Y) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.rightMap
  map_id _ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    rfl
  map_comp _ _ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    rfl
  first f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.app_heq f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.jointVertex a b).symm
  last {S T} f := by
    change HEq (f.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length)) (𝟙 Y)
    apply (conj_eqToHom_iff_heq _ _ S.last T.last).1
    simpa only [Category.id_comp, eqToHom_trans] using f.last

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams
