module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendNaturalityArrows

/-!
# 元の連結後の左右の切り出しと端点移送による回収

概要：連結して切り出した元の左右の部分は同じ端点表示に戻すと元の対象になる。
方針：全頂点と全列の異種等式を使う。
規約：空語と全ての向きを含み、指定性の仮定を追加しない。
使われ方：DK9.4・10.3の分解の逆向きの回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
lemma joint_eq : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).vertex (Fin.last a.length) = Y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T (Fin.last a.length)).trans S.last

lemma leftObj_obj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj rfl (joint_eq S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)) = S := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T j
  · intro i
    change HEq (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T).arrow (i.castAdd b.length) ≫ eqToHom _) (S.arrow i)
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S T i

lemma rightObj_obj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj (joint_eq S T) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)) = T := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T j
  · intro i
    change HEq (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T).arrow (i.natAdd a.length) ≫ eqToHom _) (T.arrow i)
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq S T i
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
