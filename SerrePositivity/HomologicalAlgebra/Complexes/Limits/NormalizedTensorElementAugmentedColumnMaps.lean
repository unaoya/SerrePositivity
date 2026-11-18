module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementAugmentedColumn

/-!
概要：終端付き実列の通常射と終端への射を、元の frame 射と augmentation 自身へ戻す。
方針：既存の終端追加関手の全射を同じ Hom の上下写像で移す。
規約：対象の輸送を異種等号で保持する。使われ方：二重 cone の通常閉 cochain の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

private lemma downMap_heq {C : Type (u + 1)} [Category.{u} C]
    {x y x' y' : ULiftHom.{u + 1} C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (hf : HEq f g) :
    HEq (ULiftHom.down.{u, u + 1, u + 1}.map f)
      (ULiftHom.down.{u, u + 1, u + 1}.map g) := by
  cases hx
  cases hy
  cases eq_of_heq hf
  rfl

lemma normalizedTensorElementAugmentedColumn_map_cast_cast {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map (c.map (homOfLE hij))) := by
  let L := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedAugmentationCocone A X Y
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_cast L Γ i j hij
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ j
  exact _root_.SerrePositivity.ComplexLimits.downMap_heq hx hy _ _ he

lemma normalizedTensorElementAugmentedColumn_map_cast_last {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentedColumn A X Y c).map
      (homOfLE (Fin.le_last i.castSucc)))
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj i)) := by
  let L := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftedAugmentationCocone A X Y
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_map_cast_last L Γ i
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_cast L Γ i
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.diagram_obj_last L Γ
  exact _root_.SerrePositivity.ComplexLimits.downMap_heq hx hy _ _ he

end SerrePositivity.ComplexLimits
