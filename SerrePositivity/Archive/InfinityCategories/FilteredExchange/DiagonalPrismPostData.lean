module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonWitness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：底を固定した全空間の射で、同じ実 prism の両端と底を保持する。
方針：fiber 射の包含式で、元の三つの実等式を後合成する。
規約：全係数を保持。使われ方：元の指定対角比較の後合成の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {P E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F)
  (hf : f ≫ q = p) {a b : B _⦋0⦌} (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)

/-- 元の実 prism の始点は、同じ始点の fiber 射で移した像。 -/
lemma diagonalPrismPost_start (x : P ⟶ vertexFiber p a)
    (hx : prismEndpoint 0 P ≫ H = x ≫ vertexFiberι p a) :
    prismEndpoint 0 P ≫ (H ≫ f) =
      (x ≫ vertexFiberMap p q f hf a) ≫ vertexFiberι q a := by
  simpa only [Category.assoc, vertexFiberMap_ι] using congrArg (fun k ↦ k ≫ f) hx

/-- 元の実 prism の終点も、同じ終点の fiber 射で移した像。 -/
lemma diagonalPrismPost_finish (y : P ⟶ vertexFiber p b)
    (hy : prismEndpoint 1 P ≫ H = y ≫ vertexFiberι p b) :
    prismEndpoint 1 P ≫ (H ≫ f) =
      (y ≫ vertexFiberMap p q f hf b) ≫ vertexFiberι q b := by
  simpa only [Category.assoc, vertexFiberMap_ι] using congrArg (fun k ↦ k ≫ f) hy

include hf in
/-- 元の実 prism を後合成しても、同じ底の族を厳密に被覆する。 -/
lemma diagonalPrismPost_projection (γ : (Δ[1] : SSet.{u}) ⊗ P ⟶ B)
    (hH : H ≫ p = γ) : (H ≫ f) ≫ q = γ := by
  rw [Category.assoc, hf, hH]

end SerrePositivity.InfinityCategories.F2
