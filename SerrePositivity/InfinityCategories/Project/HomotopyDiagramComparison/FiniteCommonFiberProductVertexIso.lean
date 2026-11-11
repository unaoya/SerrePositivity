module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteCommonFiberProductUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：元の有限共通 fiber 積の頂点 fiber と、元の各頂点 fiber の有限積の同型。
方針：元の全射影の fiber 射を組にし、元の fiber 包含から普遍逆射を構成する。
規約：充填性は不要。元の全空間・底射影・全成分を保持する。
使われ方：有限 coherent 積の指定全空間比較の fiber ごとの同値判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の有限共通 fiber 積の同じ頂点上の fiber は、元の各 fiber の有限積。 -/
def finiteCommonFiberProductVertexIso (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n)) b ≅
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p i) b) := by
  let r := pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProductMap n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nonemptyFiniteDiagonal B n)
  let H := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap r (p i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection_base n p i) b)
  let L : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p i) b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift n p
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p j) b) i ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p i) b) (SSet.const b) (by
          intro i
          rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const])
  have hL : L ≫ r = SSet.const b := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift_base _ _ _ _ _
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift r b L hL
  have hV : V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r b = L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hH (i : Fin (n + 1)) :
      H ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p j) b) i ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p i) b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i := by
    rw [← Category.assoc, show H ≫ _ = _ from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection n _ i,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  refine { hom := H, inv := V, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext r b
    rw [Category.assoc, hV, Category.id_comp]
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProduct_hom_ext n p
    intro i
    rw [Category.assoc, show L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i = _ from
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift_projection n p _ _ _ i, hH]
  · apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_hom_ext n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p i) b)
    intro i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (p i) b
    rw [Category.assoc, Category.assoc, hH, ← Category.assoc, hV, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCommonFiberProductLift_projection n p _ _ _ i

/-- 元の有限 fiber 同型の各成分は、元の全空間射影の fiber 射そのもの。 -/
lemma finiteCommonFiberProductVertexIso_projection (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (b : B _⦋0⦌) (i : Fin (n + 1)) :
    (finiteCommonFiberProductVertexIso n p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p j) b) i =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ (p i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection n p i)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductProjection_base n p i) b :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetLift_projection _ _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
