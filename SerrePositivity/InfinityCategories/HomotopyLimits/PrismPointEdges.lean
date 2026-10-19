module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportTriangle

/-!
概要：指定した同じ prism の頂点評価から、両端を明示した実際の辺を取り出す。
方針：評価した区間の両端を prism の端点式で計算し、Yoneda 表示で辺を作る。
規約：輸送辺を存在命題から選び直さず、標準 prism そのものを使う。
使われ方：輸送三角形の頂点評価の二辺と長辺の厳密な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 指定した両端の射を持つ同じ prism を、係数頂点で評価した実際の辺。 -/
def prismPointEdge {A E : SSet.{u}} (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (F₀ F₁ : A ⟶ E) (h₀ : prismEndpoint 0 A ≫ W = F₀)
    (h₁ : prismEndpoint 1 A ≫ W = F₁) (v : A _⦋0⦌) :
    E.Edge (F₀.app (Opposite.op ⦋0⦌) v) (F₁.app (Opposite.op ⦋0⦌) v) where
  edge := SSet.yonedaEquiv (prismVertexEvaluation W v)
  src_eq := by
    change E.δ 1 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, prismVertexEvaluation_shape,
      trianglePrism_endpoint_zero, Category.assoc, h₀]
    rw [prismVertexEvaluation, ← Category.assoc, lift_snd,
      SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const]
  tgt_eq := by
    change E.δ 0 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, prismVertexEvaluation_shape,
      trianglePrism_endpoint_one, Category.assoc, h₁]
    rw [prismVertexEvaluation, ← Category.assoc, lift_snd,
      SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const]

/-- 点で評価した辺の全単体表示は、元の prism の評価そのもの。 -/
lemma prismPointEdge_diagram {A E : SSet.{u}} (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (F₀ F₁ : A ⟶ E) (h₀ : prismEndpoint 0 A ≫ W = F₀)
    (h₁ : prismEndpoint 1 A ≫ W = F₁) (v : A _⦋0⦌) :
    SSet.yonedaEquiv.symm (prismPointEdge W F₀ F₁ h₀ h₁ v).edge = prismVertexEvaluation W v :=
  SSet.yonedaEquiv.symm_apply_apply _

/-- 元の prism が辺 e を被覆すれば、頂点評価の辺も e を一単体として厳密に被覆する。 -/
lemma prismPointEdge_projection {A E B : SSet.{u}} (p : E ⟶ B)
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (F₀ F₁ : A ⟶ E)
    (h₀ : prismEndpoint 0 A ≫ W = F₀) (h₁ : prismEndpoint 1 A ≫ W = F₁)
    {a b : B _⦋0⦌} (e : B.Edge a b)
    (hW : W ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge) (v : A _⦋0⦌) :
    ((prismPointEdge W F₀ F₁ h₀ h₁ v).map p).edge = e.edge := by
  change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (prismVertexEvaluation W v)) = _
  rw [← SSet.yonedaEquiv_comp, prismVertexEvaluation_projection p W _ hW,
    Equiv.apply_symm_apply]

/-- 標準輸送で使った同じ prism の、指定した fiber 頂点を始点とする実際の辺。 -/
def standardTransportPointEdge {E B : SSet.{u}} (p : E ⟶ B) [CocartesianFibration p]
    {a b : B _⦋0⦌} (e : B.Edge a b) (v : (vertexFiber p a) _⦋0⦌) :
    E.Edge v.val ((edgeTransport p e).app (Opposite.op ⦋0⦌) v).val :=
  prismPointEdge (transportEdgePrism p e) (vertexFiberι p a)
    (edgeTransport p e ≫ vertexFiberι p b)
    (transportEdgePrism_zero p e) (transportEdgePrism_one p e) v

/-- 標準輸送の点の辺を全単体で表示すると、同じ標準 prism の評価になる。 -/
lemma standardTransportPointEdge_diagram {E B : SSet.{u}} (p : E ⟶ B)
    [CocartesianFibration p] {a b : B _⦋0⦌} (e : B.Edge a b) (v : (vertexFiber p a) _⦋0⦌) :
    SSet.yonedaEquiv.symm (standardTransportPointEdge p e v).edge =
      prismVertexEvaluation (transportEdgePrism p e) v :=
  prismPointEdge_diagram _ _ _ _ _ _

/-- 標準輸送の点の辺の底は、元の指定辺そのもの。 -/
lemma standardTransportPointEdge_projection {E B : SSet.{u}} (p : E ⟶ B)
    [CocartesianFibration p] {a b : B _⦋0⦌} (e : B.Edge a b) (v : (vertexFiber p a) _⦋0⦌) :
    ((standardTransportPointEdge p e v).map p).edge = e.edge :=
  prismPointEdge_projection p _ _ _ _ _ e (transportEdgePrism_projection p e) v

end
end SerrePositivity.InfinityCategories.HomotopyLimits
