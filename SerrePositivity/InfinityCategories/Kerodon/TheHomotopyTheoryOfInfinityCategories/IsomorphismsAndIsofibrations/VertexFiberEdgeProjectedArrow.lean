module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero

/-!
概要：元のfiber内の辺の底への像の類を、同じ底の頂点の恒等射へ合わせる。
方針：包含後の厳密な定値の式と元の恒等辺の式を評価する。
規約：底の後合成も保持し、quasicategory性を仮定しない。
使われ方：元のtwisted Homの左右射影の単位の計算。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 元のfiber内の同じ辺は、元の底とその後合成で恒等射のArrowになる。 -/
lemma vertexFiber_edge_projected_arrow {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D)
    {b : B _⦋0⦌} {v w : (vertexFiber p b) _⦋0⦌} (e : SSet.Edge v w) :
    Arrow.mk (HomotopyCategory.homMk ((e.map (vertexFiberι p b)).map (p ≫ g))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌) b))) := by
  rw [← HomotopyCategory.homMk_id (g.app (Opposite.op ⦋0⦌) b)]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  have hmap : vertexFiberι p b ≫ (p ≫ g) = SSet.const (g.app (Opposite.op ⦋0⦌) b) := by
    rw [← Category.assoc, vertexFiberι_comp, SSet.const_comp]
  have h := congrArg (fun f => f.app (Opposite.op ⦋1⦌) e.edge) hmap
  exact h.trans (pinchedConstant_one _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

end
