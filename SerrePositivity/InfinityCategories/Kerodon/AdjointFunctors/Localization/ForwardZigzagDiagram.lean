module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagram

/-!
# 元の forward 自然変換からの一列の図式

概要：元の端点関手と自然変換を、そのまま一列の MovingDiagram にする。
方針：元の各可換正方形を movingHom に渡し、恒等・合成を両端で回収する。
規約：自然性は元の自然変換から導く。
使われ方：指定接頭射・固定生成矢・残りの射を全語へ接続する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  (W : MorphismProperty C) [W.IsMultiplicative] {A B : D ⥤ C} (α : A ⟶ B)
  (hA : ∀ {d e : D} (f : d ⟶ e), W (A.map f))
  (hB : ∀ {d e : D} (f : d ⟶ e), W (B.map f))

def diagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) A B where
  obj d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (α.app d)
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.movingHom (A.map f) (B.map f) (hA f) (hB f) (α.naturality f).symm
  map_id d := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => exact A.map_id d
    | succ _ => exact B.map_id d
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => exact A.map_comp f g
    | succ _ => exact B.map_comp f g
  first _ := HEq.rfl
  last _ := HEq.rfl

lemma diagram_arrow (d : D) : ((diagram W α hA hB).obj d).arrow (0 : Fin 1) = α.app d := rfl

lemma diagram_arrow_mem (hα : ∀ d, W (α.app d)) (d : D) (j : Fin 1) :
    W (((diagram W α hA hB).obj d).arrow j) := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hα d

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram
