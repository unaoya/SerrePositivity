module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingOuterToRightHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

/-!
概要：始域屋根長方形の外周から右面への同じ全ホモトピーの四頂点辺を回収する。
方針：元の有限順序形状を各頂点で評価し、左列の二辺と固定右列を照合する。
規約：元全長方形を変更しない。使われ方：厚平坦核へ移す外周全比較の可逆性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories
open scoped Simplicial
variable {X : SSet.{u}} (F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X)

/-- 概要：左下成分は元長方形左面の下辺そのもの。
方針：同じ有限形状の一次単体を計算。規約：元の辺を保持。
使われ方：元始域から厚核への同値成分の回収。 -/
lemma pastingOuterRightVertexEdge_bottom :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 _) 0 0)).edge = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)).edge  := by
  change F.app (Opposite.op ⦋1⦌) _ = F.app (Opposite.op ⦋1⦌) _
  congr 1
  apply Prod.ext
  all_goals
    apply stdSimplex.ext
    intro k
    fin_cases k <;> rfl

/-- 概要：左上成分は元長方形左面の上辺そのもの。
方針：同じ有限形状の一次単体を計算。規約：元の辺を保持。
使われ方：元全対象商の二零頂点の比較。 -/
lemma pastingOuterRightVertexEdge_top :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 _) 0 1)).edge = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)).edge  := by
  change F.app (Opposite.op ⦋1⦌) _ = F.app (Opposite.op ⦋1⦌) _
  congr 1
  apply Prod.ext
  all_goals
    apply stdSimplex.ext
    intro k
    fin_cases k <;> rfl

/-- 概要：右列成分は元長方形の同じ固定頂点の恒等辺。
方針：右列を二に保つ有限形状を計算。規約：元対象を保持。
使われ方：元実外面から核面への全比較の二恒等成分。 -/
lemma pastingOuterRightVertexEdge_fixed (j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHomotopy F)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 _) 1 j)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 j)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (𝟙 _) 1) 1 j)) 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map F (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (𝟙 _) 1) 1 j) 1]
  change F.app (Opposite.op ⦋1⦌) _ = F.app (Opposite.op ⦋1⦌) _
  congr 1
end SerrePositivity.KST.SConstruction
