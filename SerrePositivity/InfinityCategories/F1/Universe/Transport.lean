module

public import SerrePositivity.InfinityCategories.F1.Universe.Fiber
public import SerrePositivity.InfinityCategories.F1.Universe.Prism
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport

/-!
概要：left fibration の fiber 間の transport とその持ち上げの証人の宇宙移送。
方針：fiber の宇宙同型と prism の宇宙持ち上げを用いて、同じ始点・終点・底の条件を移す。
規約：追加の宇宙 v は任意。モデル構造を用いない。
使われ方：Kerodon Corollary 5.6.0.6、weighted nerve の係数輸送を coherent な復元の宇宙で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fiber 間の射を宇宙持ち上げした射影の fiber 間の射へ移す。
方針：元の射の ULift の両側に fiber の宇宙同型を合成する。
規約：両端点の添字は元の底の頂点の ULift。
使われ方：Kerodon Corollary 5.6.0.6、元の transport の射の宇宙移送。 -/
def uliftFiberTransport {E B : SSet.{u}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (T : vertexFiber p a ⟶ vertexFiber p b) :
    vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up a) ⟶
      vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) :=
  (uliftVertexFiberIso.{u, v} p a).inv ≫ (SSet.uliftFunctor.{v, u}).map T ≫
    (uliftVertexFiberIso.{u, v} p b).hom

/-- 概要：left fibration の transport の証人は宇宙持ち上げで保たれる。
方針：証人の prism を持ち上げ、始域の fiber の宇宙同型の逆で制限する。
規約：全ての垂直辺の cocartesian 性は持ち上げた射影の left fibration 性による。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元と比較する transport の証人。 -/
lemma IsEdgeTransport.ulift {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (e : SSet.Edge a b) {T : vertexFiber p a ⟶ vertexFiber p b}
    (hT : IsEdgeTransport p e T) :
    IsEdgeTransport ((SSet.uliftFunctor.{v, u}).map p) (uliftTruncatedEdge.{u, v} e)
      (uliftFiberTransport.{u, v} p T) := by
  obtain ⟨H, hH₀, hH₁, hHp, _⟩ := hT
  have h₀ : prismEndpoint 0 ((SSet.uliftFunctor.{v, u}).obj (vertexFiber p a)) ≫
      uliftSimplexPrism.{u, v} H = (SSet.uliftFunctor.{v, u}).map (vertexFiberι p a) := by
    change simplexPrismVertex 1 0 _ ≫ _ = _
    rw [uliftSimplexPrism_vertex]
    exact congrArg (SSet.uliftFunctor.{v, u}).map hH₀
  have h₁ : prismEndpoint 1 ((SSet.uliftFunctor.{v, u}).obj (vertexFiber p a)) ≫
      uliftSimplexPrism.{u, v} H =
    (SSet.uliftFunctor.{v, u}).map T ≫ (SSet.uliftFunctor.{v, u}).map (vertexFiberι p b) := by
    change simplexPrismVertex 1 1 _ ≫ _ = _
    rw [uliftSimplexPrism_vertex, ← Functor.map_comp]
    exact congrArg (SSet.uliftFunctor.{v, u}).map hH₁
  have hbase : uliftSimplexPrism.{u, v} H ≫ (SSet.uliftFunctor.{v, u}).map p =
      fst _ _ ≫ SSet.yonedaEquiv.symm (uliftTruncatedEdge.{u, v} e).edge := by
    rw [uliftSimplexPrism_post, hHp]
    exact uliftSimplexPrism_edgeFamily (A := vertexFiber p a) e
  refine ⟨(Δ[1] ◁ (uliftVertexFiberIso.{u, v} p a).inv) ≫ uliftSimplexPrism.{u, v} H,
    ?_, ?_, ?_, fun _ ↦ isCocartesianEdge_of_leftFibration _ _⟩
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₀,
      uliftVertexFiberIso_inv_ι]
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁,
      uliftFiberTransport, Category.assoc, Category.assoc, uliftVertexFiberIso_hom_ι]
  · rw [Category.assoc, hbase, ← Category.assoc, whiskerLeft_fst]

/-- 概要：持ち上げた射影の標準 transport は、元の標準 transport の宇宙移送と関手同型。
方針：持ち上げた transport の証人と新しい標準 transport の一意性を使う。
規約：同型は持ち上げた終点 fiber 内に取る。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、選択した transport と宇宙移送の整合性。 -/
noncomputable def edgeTransport_uliftIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      (edgeTransport ((SSet.uliftFunctor.{v, u}).map p) (uliftTruncatedEdge.{u, v} e))
      (uliftFiberTransport.{u, v} p (edgeTransport p e)) :=
  (IsEdgeTransport.functorIso ((SSet.uliftFunctor.{v, u}).map p) (uliftTruncatedEdge.{u, v} e)
    (edgeTransport_isTransport _ _) ((edgeTransport_isTransport p e).ulift p e)).some

end SerrePositivity.InfinityCategories
