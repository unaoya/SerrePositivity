module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCommonFiberProductUniversal
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の有限共通 fiber 積の同じ頂点上の fiber は、元の各 fiber の有限積。 -/
def finiteCommonFiberProductVertexIso (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (b : B _⦋0⦌) :
    vertexFiber (pullback.snd (nonemptyFiniteSSetProductMap n p)
      (nonemptyFiniteDiagonal B n)) b ≅
        nonemptyFiniteSSetProduct n (fun i ↦ vertexFiber (p i) b) := by
  let r := pullback.snd (nonemptyFiniteSSetProductMap n p) (nonemptyFiniteDiagonal B n)
  let H := nonemptyFiniteSSetLift n (fun i ↦ vertexFiberMap r (p i)
    (finiteCommonFiberProductProjection n p i) (finiteCommonFiberProductProjection_base n p i) b)
  let L : nonemptyFiniteSSetProduct n (fun i ↦ vertexFiber (p i) b) ⟶
      finiteCommonFiberProduct n p :=
    finiteCommonFiberProductLift n p
      (fun i ↦ nonemptyFiniteSSetProjection n (fun j ↦ vertexFiber (p j) b) i ≫
        vertexFiberι (p i) b) (SSet.const b) (by
          intro i
          rw [Category.assoc, vertexFiberι_comp, SSet.comp_const])
  have hL : L ≫ r = SSet.const b := finiteCommonFiberProductLift_base _ _ _ _ _
  let V := vertexFiberLift r b L hL
  have hV : V ≫ vertexFiberι r b = L := vertexFiberLift_ι _ _ _ _
  have hH (i : Fin (n + 1)) :
      H ≫ nonemptyFiniteSSetProjection n (fun j ↦ vertexFiber (p j) b) i ≫
        vertexFiberι (p i) b = vertexFiberι r b ≫ finiteCommonFiberProductProjection n p i := by
    rw [← Category.assoc, show H ≫ _ = _ from nonemptyFiniteSSetLift_projection n _ i,
      vertexFiberMap_ι]
  refine { hom := H, inv := V, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply vertexFiber_hom_ext r b
    rw [Category.assoc, hV, Category.id_comp]
    apply finiteCommonFiberProduct_hom_ext n p
    intro i
    rw [Category.assoc, show L ≫ finiteCommonFiberProductProjection n p i = _ from
      finiteCommonFiberProductLift_projection n p _ _ _ i, hH]
  · apply nonemptyFiniteSSetProduct_hom_ext n (fun i ↦ vertexFiber (p i) b)
    intro i
    apply vertexFiber_hom_ext (p i) b
    rw [Category.assoc, Category.assoc, hH, ← Category.assoc, hV, Category.id_comp]
    exact finiteCommonFiberProductLift_projection n p _ _ _ i

/-- 元の有限 fiber 同型の各成分は、元の全空間射影の fiber 射そのもの。 -/
lemma finiteCommonFiberProductVertexIso_projection (n : ℕ) {B : SSet.{u}}
    {E : Fin (n + 1) → SSet.{u}} (p : (i : Fin (n + 1)) → E i ⟶ B)
    (b : B _⦋0⦌) (i : Fin (n + 1)) :
    (finiteCommonFiberProductVertexIso n p b).hom ≫
      nonemptyFiniteSSetProjection n (fun j ↦ vertexFiber (p j) b) i =
        vertexFiberMap _ (p i) (finiteCommonFiberProductProjection n p i)
          (finiteCommonFiberProductProjection_base n p i) b :=
  nonemptyFiniteSSetLift_projection _ _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
