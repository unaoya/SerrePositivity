module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismPointEdges

/-!
概要：元の輸送三角形 prism を、指定した始点 fiber の頂点で実際の三角形へ評価する。
方針：形状と係数の自然性により、二面・長辺・底の二単体を同じ評価で照合する。
規約：標準二辺と同じ選択済み prism を使用し、二単体を別の合成へ置き換えない。
使われ方：共通余錐から出る実際の輸送三角形と、その全 Hom の族の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g) (v : (vertexFiber p a) _⦋0⦌)

/-- 指定した始点の頂点で評価した、元の二単体を覆う実際の三角形。 -/
def coherentTransportTriangleVertex : (Δ[2] : SSet.{u}) ⟶ E :=
  prismVertexEvaluation (coherentTransportTriangle p σ).prism v

/-- 評価した三角形の底は、元の native な二単体そのもの。 -/
lemma coherentTransportTriangleVertex_projection :
    coherentTransportTriangleVertex p σ v ≫ p = SSet.yonedaEquiv.symm σ.simplex :=
  prismVertexEvaluation_projection p _ _ (coherentTransportTriangle p σ).projection v

/-- 最初の面は、同じ標準 prism の点の辺。 -/
lemma coherentTransportTriangleVertex_first :
    stdSimplex.δ (2 : Fin 3) ≫ coherentTransportTriangleVertex p σ v =
      SSet.yonedaEquiv.symm (standardTransportPointEdge p e v).edge := by
  rw [coherentTransportTriangleVertex, prismVertexEvaluation_shape,
    (coherentTransportTriangle p σ).first, standardTransportPointEdge_diagram]

/-- 評価した三角形の最初の頂点は、元の指定した fiber 頂点そのもの。 -/
lemma coherentTransportTriangleVertex_initial :
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
      coherentTransportTriangleVertex p σ v = SSet.yonedaEquiv.symm v.val := by
  rw [Category.assoc, coherentTransportTriangleVertex_first,
    SSet.Edge.δ_one_yonedaEquiv_symm]

/-- 次の面は、同じ最初の輸送の像を始点とする標準の点の辺。 -/
lemma coherentTransportTriangleVertex_second :
    stdSimplex.δ (0 : Fin 3) ≫ coherentTransportTriangleVertex p σ v =
      SSet.yonedaEquiv.symm
        (standardTransportPointEdge p f ((edgeTransport p e).app (Opposite.op ⦋0⦌) v)).edge := by
  rw [coherentTransportTriangleVertex, prismVertexEvaluation_shape,
    (coherentTransportTriangle p σ).second, prismVertexEvaluation_coefficient,
    standardTransportPointEdge_diagram]

/-- 同じ三角形 prism の長辺を同じ頂点で評価した、実際の対角辺。 -/
def coherentTransportTriangleDiagonalPointEdge :
    E.Edge v.val (((edgeTransport p e ≫ edgeTransport p f).app (Opposite.op ⦋0⦌)) v).val :=
  prismPointEdge (coherentTransportTriangleLongPrism p σ) (vertexFiberι p a)
    ((edgeTransport p e ≫ edgeTransport p f) ≫ vertexFiberι p c)
    (coherentTransportTriangleLongPrism_zero p σ)
    (coherentTransportTriangleLongPrism_one p σ) v

/-- 対角辺は、同じ評価した三角形の長辺そのもの。 -/
lemma coherentTransportTriangleVertex_long :
    stdSimplex.δ (1 : Fin 3) ≫ coherentTransportTriangleVertex p σ v =
      SSet.yonedaEquiv.symm (coherentTransportTriangleDiagonalPointEdge p σ v).edge := by
  change _ = SSet.yonedaEquiv.symm (prismPointEdge _ _ _ _ _ _).edge
  rw [prismPointEdge_diagram, coherentTransportTriangleVertex, prismVertexEvaluation_shape]
  rfl

/-- 対角の点の辺も、元の指定長辺を一単体として厳密に被覆する。 -/
lemma coherentTransportTriangleDiagonalPointEdge_projection :
    ((coherentTransportTriangleDiagonalPointEdge p σ v).map p).edge = g.edge :=
  prismPointEdge_projection p _ _ _ _ _ g (coherentTransportTriangleLongPrism_projection p σ) v

/-- 元の二単体を覆う、標準の二つの点の辺と同じ対角辺の合成三角形。 -/
def coherentTransportTrianglePointCompStruct :
    SSet.Edge.CompStruct (standardTransportPointEdge p e v)
      (standardTransportPointEdge p f ((edgeTransport p e).app (Opposite.op ⦋0⦌) v))
      (coherentTransportTriangleDiagonalPointEdge p σ v) where
  simplex := SSet.yonedaEquiv (coherentTransportTriangleVertex p σ v)
  d₂ := by
    change E.δ 2 (SSet.yonedaEquiv (coherentTransportTriangleVertex p σ v)) =
      (standardTransportPointEdge p e v).edge
    rw [← stdSimplex.yonedaEquiv_δ_comp, coherentTransportTriangleVertex_first,
      Equiv.apply_symm_apply]
  d₀ := by
    change E.δ 0 (SSet.yonedaEquiv (coherentTransportTriangleVertex p σ v)) =
      (standardTransportPointEdge p f ((edgeTransport p e).app (Opposite.op ⦋0⦌) v)).edge
    rw [← stdSimplex.yonedaEquiv_δ_comp, coherentTransportTriangleVertex_second,
      Equiv.apply_symm_apply]
  d₁ := by
    change E.δ 1 (SSet.yonedaEquiv (coherentTransportTriangleVertex p σ v)) =
      (coherentTransportTriangleDiagonalPointEdge p σ v).edge
    rw [← stdSimplex.yonedaEquiv_δ_comp, coherentTransportTriangleVertex_long,
      Equiv.apply_symm_apply]

/-- 合成三角形の二単体の像も、指定した元の二単体に厳密に一致する。 -/
lemma coherentTransportTrianglePointCompStruct_projection :
    p.app (Opposite.op ⦋2⦌) (coherentTransportTrianglePointCompStruct p σ v).simplex =
      σ.simplex := by
  change p.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv _) = _
  rw [← SSet.yonedaEquiv_comp, coherentTransportTriangleVertex_projection,
    Equiv.apply_symm_apply]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
