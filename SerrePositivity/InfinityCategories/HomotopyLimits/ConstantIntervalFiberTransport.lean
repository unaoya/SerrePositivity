module

public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransport
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransport

/-!
概要：固定した元の辺の区間頂点に沿う、動く始点の普遍輸送を比較する。
方針：全始点 fiber での既存の辺評価を前合成し、対角輸送の定義を計算する。
規約：元の辺と元の輸送を保持。使われ方：Kan 射の右 Hom 輸送の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の辺を固定した対角輸送は、動く始点の後に元の辺輸送を続けた射と同型。 -/
def diagonalFiberTransport_edgeIso {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (f : P ⟶ vertexFiber p a) :
    FunctorIso (diagonalFiberTransport p f (SSet.const (intervalMappingVertexOfEdge e)))
      (f ≫ edgeTransport p e) := by
  let T := parametrizedFiberTransportFamily p a b
  let v := intervalMappingVertexOfEdge e
  let g := (functorVertexEquiv _ _).symm ((parametrizedFiberTransport p a b).app _ v)
  have hg : lift (𝟙 _) (SSet.const v) ≫ T.endpoint = g := by
    have h := uncurry_at_vertex T.map v
    rw [FiberTransportFamily.map, uncurry_curry] at h
    exact h
  have hf : diagonalFiberTransport p f (SSet.const v) = f ≫ g := by
    rw [← hg]
    simp only [diagonalFiberTransport, ← Category.assoc, comp_lift, Category.comp_id,
      SSet.comp_const]
    rfl
  exact F2.functorIsoOfEq ((parametrizedFiberTransport_at_edgeIso p e).precomp f) hf.symm rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
