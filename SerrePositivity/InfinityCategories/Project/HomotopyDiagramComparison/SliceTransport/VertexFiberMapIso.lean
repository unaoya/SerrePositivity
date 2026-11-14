module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：同じ底上の同型は、各頂点の fiber の実際の同型を誘導する。
方針：逆射も底を保つことを計算し、包含後に二つの合成を検査する。
規約：充填性は不要。使われ方：span の形状の厳密な同型による固定終点余錐空間の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ底上の同型が誘導する頂点 fiber の射も同型。 -/
instance vertexFiberMap_isIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) [IsIso f] (y : B _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf y) := by
  have hi : inv f ≫ p = q := by
    rw [← hf, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p (inv f) hi y, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p y
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q y
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
