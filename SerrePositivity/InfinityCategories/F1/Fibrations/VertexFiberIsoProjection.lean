module

public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexIsoMappingLaws
public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：同じ fiber 内の頂点同型を射影すると、元の端点の等号による同型へ戻る。
方針：fiber の包含と射影の合成が定値であることを使う。
規約：指定された fiber 内の同型そのものについて像を計算する。
使われ方：元の大域 Hom 自然性の標準持ち上げの coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ fiber 内の指定同型の像は、端点を同じ定値頂点へ揃える等号の同型。 -/
lemma VertexIso.map_vertexFiber_projection {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {x y : (vertexFiber p b) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map (VertexIso.map e (vertexFiberι p b)) p =
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun t : vertexFiber p b ⟶ B ↦ t.app (Opposite.op ⦋0⦌) x)
          (vertexFiberι_comp p b))) ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun t : vertexFiber p b ⟶ B ↦ t.app (Opposite.op ⦋0⦌) y)
          (vertexFiberι_comp p b)))).symm := by
  rw [VertexIso.map_comp]
  have h := VertexIso.map_congr e (vertexFiberι_comp p b)
  rw [VertexIso.map_const] at h
  simpa only [Iso.refl_trans] using h

end SerrePositivity.InfinityCategories
