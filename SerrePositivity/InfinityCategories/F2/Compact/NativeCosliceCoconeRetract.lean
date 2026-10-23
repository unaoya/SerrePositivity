module

public import SerrePositivity.InfinityCategories.F2.Compact.NativeCosliceRepresentation
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentationEdgeFactorization
public import SerrePositivity.InfinityCategories.F2.Compact.CosliceIdentityRetraction
public import SerrePositivity.InfinityCategories.F1.Universe.Fiber

/-!
概要：元の coslice 表現が指定余錐を余極限へ写すなら、元の頂点は一つの元の項の retract。
方針：元の恒等点への実辺を全空間で回収し、同じ辺を元の宇宙へ戻して分裂三角形を読む。
規約：元の余錐頂点・元の図式の項・元の coslice の恒等点を保持する。
使われ方：compact 対象の任意の小さい filtered 生成表示から retract を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の指定全余錐像の余極限性から、同じ頂点の一つの元の項への retract を構成する。 -/
lemma nativeCosliceCocone_retract {I C : SSet.{u}} [Quasicategory C]
    (D : I ⟶ C) (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone (nativeCosliceRepresentation c.vertex).diagram
      (JoinCocone.ulift.{u, u + 1} c))) :
    ∃ i : I _⦋0⦌, Idempotent.IsVertexRetractOf c.vertex (D.app (Opposite.op ⦋0⦌) i) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex)
  let t := (uliftVertexFiberIso.{u, u + 1} p c.vertex).hom.app (Opposite.op ⦋0⦌)
    (ULift.up (cosliceIdentityFiberPoint c.vertex))
  obtain ⟨i, w, k, _⟩ := representationCocone_edge_factorization
    ((SSet.uliftFunctor.{u + 1, u}).map p) (nativeCosliceRepresentation c.vertex)
    ((SSet.uliftFunctor.{u + 1, u}).map D) (JoinCocone.ulift c) hc t
  let w₀ := ((uliftVertexFiberIso.{u, u + 1} p (D.app (Opposite.op ⦋0⦌) i.down)).inv.app
    (Opposite.op ⦋0⦌) w).down
  let k₀ : (sliceUnder (SSet.yonedaEquiv.symm c.vertex)).Edge w₀.val
      (cosliceIdentityCone c.vertex) :=
    ⟨k.edge.down, congrArg ULift.down k.src_eq, congrArg ULift.down k.tgt_eq⟩
  exact ⟨i.down, cosliceIdentityEdge_retract w₀ k₀⟩

end SerrePositivity.InfinityCategories.F2.Compact
