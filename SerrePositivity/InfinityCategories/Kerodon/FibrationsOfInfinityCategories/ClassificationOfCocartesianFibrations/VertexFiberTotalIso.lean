module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：底を固定した全空間の同型による頂点 fiber の同型。
方針：全空間の同型と逆同型が誘導する fiber の射を組み合わせる。
規約：射影の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening と元の全空間の fiber の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底上の全空間の同型は各頂点の fiber の同型を誘導する。
方針：順方向と逆方向の fiber の射の合成を包含後に計算する。
規約：同型 e と底の可換性を明示して固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、宇宙調整の同型を fiber の比較へ制限する。 -/
def vertexFiberTotalIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q e.hom he b
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p e.inv (by rw [← he, e.inv_hom_id_assoc]) b
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
