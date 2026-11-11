module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofRightIdentity
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition

/-!
# 元の恒等左脚 roof と同じ forward 射の厳密な余極限表示

概要：前向き一列に恒等後向き列を挿入すると、元の恒等左脚 roof になる。
方針：同じ cut・元の空区間と一列区間を計算し、元の語の標準射を適用する。
規約：元の射・元の余極限の点を保持する。
使われ方：Under 全円柱の定数端を元の右脚へ戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

def insertLeftIdentity : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word where
  orderHom := ⟨Fin.succ, fun _ _ h => Nat.succ_le_succ h⟩
  direction_eq i := by fin_cases i; rfl

lemma insertLeftIdentity_cut (j : Fin 3) :
    insertLeftIdentity.cut j = (![0, 0, 1] : Fin 3 → Fin 2) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C} (f : X ⟶ Y)

lemma insertLeftIdentity_obj :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj insertLeftIdentity (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (𝟙 X) (W.id_mem X) f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f).vertex (insertLeftIdentity.cut j) = _
    rw [insertLeftIdentity_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) 0 0 _ _).unop = 𝟙 X
      exact congrArg (fun m : Opposite.op X ⟶ Opposite.op X => m.unop)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) 0 _)
    · apply heq_of_eq
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) 0 1 _ _ = f
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) (0 : Fin 1) rfl).trans
        (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f) (0 : Fin 1) rfl))

lemma colimitRowMap_leftIdentity : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (𝟙 X) (W.id_mem X) f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f := by
  rw [← insertLeftIdentity_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_wordAction, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.colimitRowMap_forward]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
