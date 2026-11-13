module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRowColumnPushouts

/-!
概要：大きな二四角形の始点を元の (0,1)・(1,0) と厳密比較する。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma ExcisionSquareGrid.row_outer_source {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip ≫ d.extension.full) 1 1) 0 0 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1 := by
  have he : nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫
      d.extension.full = d.extension.core := by
    rw [d.extension.middle_eq, d.extension.core_eq]
  have hv := congrArg (fun F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X ↦
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2) 0 1) he
  exact hv.trans (congrArg (fun F ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1) d.core_input_restriction)

lemma ExcisionSquareGrid.column_outer_source {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip ≫ d.extension.full) 1 1) 0 0 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 1 0 := by
  have he : nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion ≫
      d.extension.full = d.extension.core := by
    rw [d.extension.middle_eq, d.extension.core_eq]
  have hv := congrArg (fun F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X ↦
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2) 1 0) he
  exact hv.trans (congrArg (fun F ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 0) d.core_input_restriction)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
