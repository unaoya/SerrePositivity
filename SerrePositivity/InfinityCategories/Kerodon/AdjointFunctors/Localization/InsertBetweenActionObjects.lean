module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects

/-!
# 元の語の作用による中央恒等列の挿入の対象の同定

概要：元の insertBetween の WordAction は、元の左右対象の間に恒等列を置く対象。
方針：切断による全頂点、像の全列、像の外の一列を元の射で照合する。
規約：語の長さだけや nerve のホモトピーだけで同定しない。
使われ方：右置換の各対象が元の語の作用の本質像に属することの証拠。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X E Y : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X E) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b E Y)

lemma action_obj_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj S T := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_vertex_cases a b .backward
      (P := fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).vertex j = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj S T).vertex j)
    · intro i
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.action_leftVertex S T i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj_leftVertex S T i).symm
    · intro i
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.action_rightVertex S T i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj_rightVertex S T i).symm
  · intro j
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_column_cases a b .backward
      (P := fun j => HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).arrow j) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj S T).arrow j))
    · intro i
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_injective a b .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (i.castAdd b.length)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_left] at h
      exact (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S T i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj_arrow_left_heq S T i).symm
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.action_arrow_middle_heq S T).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj_arrow_middle_heq S T).symm
    · intro i
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.arrow_image_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_injective a b .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (i.natAdd a.length)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_right] at h
      exact (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq S T i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects.obj_arrow_right_heq S T i).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
