module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreSuspension
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridOuterPushout

/-!
概要：元の終点・指定零頂点・同じ最終対角頂点を保つ suspension 模型。
方針：実際の長方形の貼り合わせと同じ図式の評価を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma ExcisionSquareGrid.final_outer_source {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z) :
    squareVertex (grid22Face (excisionGridOuterDiagram ≫ d.extension.full) 1 1) 0 0 =
      squareVertex R 1 1 := by
  have he : nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion ≫
      d.extension.full = d.extension.core := by
    rw [d.extension.middle_eq, d.extension.core_eq]
  have hv := congrArg (fun F : nerve ExcisionGridCoreIndex.{u} ⟶ X ↦
    squareVertex (grid22Face (excisionGridCoreDiagram ≫ F) 2 2) 1 1) he
  exact hv.trans (congrArg (fun F ↦ squareVertex F 1 1) d.core_input_restriction)

def ExcisionSquareGrid.final_suspension {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) : SuspensionSquare (squareVertex R 1 1) where
  square := grid22Face (excisionGridOuterDiagram ≫ d.extension.full) 1 1
  zero_corner := by
    change IsZeroVertex (d.extension.full.app (Opposite.op ⦋0⦌)
      (nerveVertex excisionGridSecondNewZero.val))
    rw [d.extension.second_new_zero]
    exact hz
  source_eq := d.final_outer_source
  other_zero := by
    change IsZeroVertex (d.extension.full.app (Opposite.op ⦋0⦌)
      (nerveVertex excisionGridFirstNewZero.val))
    rw [d.extension.first_new_zero]
    exact hz
  isPushout := d.extension.final_outer_pushout

lemma ExcisionSquareGrid.final_suspension_vertex {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) : (d.final_suspension hz).vertex =
      d.extension.full.app (Opposite.op ⦋0⦌) (nerveVertex excisionGridPoint33) := rfl

end SerrePositivity.InfinityCategories
