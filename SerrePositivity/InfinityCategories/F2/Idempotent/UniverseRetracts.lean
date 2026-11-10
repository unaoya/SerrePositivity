module

public import SerrePositivity.InfinityCategories.F2.Idempotent.RetractionTriangle
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge

/-!
概要：元の指定二頂点の retract の存在は、宇宙持ち上げで保たれる。
方針：元の実際の分裂三角形全体を持ち上げ、同じ恒等長辺を保持する。
規約：元の両頂点と射の向きを保持する。
使われ方：前層値の左 Kan 延長の値が元の Yoneda retract 閉包にあること。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の二頂点の retract の存在は、同じ二頂点の任意の宇宙持ち上げで保たれる。 -/
lemma IsVertexRetractOf.ulift {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) (ULift.up y) := by
  obtain ⟨r⟩ := h
  obtain ⟨t, _hi, _hr⟩ := r.triangle_exists
  let T : RetractionTriangle (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up y) (ULift.up x) :=
    ⟨SSet.Edge.ofTruncated (uliftTruncatedEdge t.1.toTruncated),
      SSet.Edge.ofTruncated (uliftTruncatedEdge t.2.1.toTruncated),
      SSet.Edge.CompStruct.ofTruncated (uliftTruncatedCompStruct t.2.2.toTruncated)⟩
  exact ⟨T.vertexRetraction⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
