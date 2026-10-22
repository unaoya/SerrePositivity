module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRowColumnPushouts

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
namespace SerrePositivity.InfinityCategories

lemma ExcisionSquareGrid.row_outer_source {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    squareVertex (strip3Square (excisionGridRowStrip ≫ d.extension.full) 1 1) 0 0 =
      squareVertex R 0 1 := by
  have he : nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫
      d.extension.full = d.extension.core := by
    rw [d.extension.middle_eq, d.extension.core_eq]
  have hv := congrArg (fun F : nerve ExcisionGridCoreIndex.{u} ⟶ X ↦
    squareVertex (grid22Face (excisionGridCoreDiagram ≫ F) 2 2) 0 1) he
  exact hv.trans (congrArg (fun F ↦ squareVertex F 0 1) d.core_input_restriction)

lemma ExcisionSquareGrid.column_outer_source {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    squareVertex (strip3Square (excisionGridColumnStrip ≫ d.extension.full) 1 1) 0 0 =
      squareVertex R 1 0 := by
  have he : nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫
      d.extension.full = d.extension.core := by
    rw [d.extension.middle_eq, d.extension.core_eq]
  have hv := congrArg (fun F : nerve ExcisionGridCoreIndex.{u} ⟶ X ↦
    squareVertex (grid22Face (excisionGridCoreDiagram ≫ F) 2 2) 1 0) he
  exact hv.trans (congrArg (fun F ↦ squareVertex F 1 0) d.core_input_restriction)

end SerrePositivity.InfinityCategories
