module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstTriangleObjects

/-!
概要：指定した通常の二射列の各 Hom を、元の輸送射と固定成分で計算する。
方針：最初の二ラベルと最終ラベルの有限の場合を調べ、恒等射保存を使う。
規約：対象の正規化を明示し、元の通常の射を保持する。
使われ方：第一三角形全体の Hom の比較の strict 側。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)

/-- 最初の二ラベルで指定射列の対象は、元の始域図式の同じ対象。 -/
lemma cocartesianFirstTriangleSourceOrderDiagram_obj_zero (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleSourceOrderDiagram F G b).obj (ULift.up i.castSucc) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up i) := by
  fin_cases i <;> rfl

/-- 最初の二ラベルの間の指定射列の射は、元の輸送射そのもの。 -/
lemma cocartesianFirstTriangleSourceOrderDiagram_map_zero (i j : Fin 2) (hij : i ≤ j) :
    eqToHom (cocartesianFirstTriangleSourceOrderDiagram_obj_zero F G b i).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleSourceOrderDiagram F G b).map
          (homOfLE (show (ULift.up i.castSucc : ULift.{u} (Fin 3)) ≤ ULift.up j.castSucc
            from Fin.castSucc_le_castSucc_iff.mpr hij)) ≫
        eqToHom (cocartesianFirstTriangleSourceOrderDiagram_obj_zero F G b j) =
      F.val.map (homOfLE (show (ULift.up i : ULift.{u} (Fin 2)) ≤ ULift.up j from hij)) := by
  fin_cases i <;> fin_cases j
  · change (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) = F.val.map (𝟙 _)
    rw [F.val.map_id]
    simp
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hij)
  · change (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) = F.val.map (𝟙 _)
    rw [F.val.map_id]
    simp

/-- 最終ラベルへ向かう指定射列の射は、同じ輸送射の後の固定成分の射。 -/
lemma cocartesianFirstTriangleSourceOrderDiagram_map_to_last (i : Fin 2) :
    eqToHom (cocartesianFirstTriangleSourceOrderDiagram_obj_zero F G b i).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleSourceOrderDiagram F G b).map
          (homOfLE (show (ULift.up i.castSucc : ULift.{u} (Fin 3)) ≤ ULift.up 2
            from Fin.le_last _)) =
      F.val.map (homOfLE (show (ULift.up i : ULift.{u} (Fin 2)) ≤ ULift.up 1
        from Fin.le_last _)) ≫
        (SimplicialCategory.homEquiv' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1))).symm b.down := by
  fin_cases i
  · rw [eqToHom_refl, Category.id_comp]
    rfl
  · change (𝟙 _) ≫ _ = F.val.map (𝟙 _) ≫ _
    rw [F.val.map_id]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
