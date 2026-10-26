module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputCompactGluing
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSliceExtension

/-!
概要：入力と標的を固定した頂点族を元の slice 図式の全余錐に戻す。
方針：入力 coslice 内の標的へ向かう辺から既存の相対 slice 余錐を作る。
規約：元の全入力を保持し、先端の基底頂点を厳密に回収する。
使われ方：compact 入力の比較を compact comma の試験余錐へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：標的を固定した入力 coslice の頂点は、元の slice 図式の全余錐を与える。
方針：同じ頂点族の終辺を既存の相対余錐構成に渡す。
規約：元の入力図式上の全余錐と基底先端の厳密な等式を返す。
使われ方：厳密に貼った二成分から元の compact comma へ戻す。 -/
lemma exists_sliceCocone_of_inputVertex {K X : SSet.{u}}
    {x : (Δ[0] : SSet.{u}) ⟶ X} (U : K ⟶ sliceOver x)
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌) :
    ∃ c : JoinCocone U, (sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex =
      ((sliceOverProjection ((SSet.yonedaEquiv
        (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U)) ≫
          sliceUnderProjection (U ≫ sliceOverProjection x)).app (Opposite.op ⦋0⦌) v) := by
  let e := sliceOverVertexEdge (X := sliceUnder (U ≫ sliceOverProjection x))
    (sliceDiagramCocone U) v
  let w : (sliceUnder (U ≫ sliceOverProjection x)) _⦋0⦌ :=
    (sliceOverProjection ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))).app
        (Opposite.op ⦋0⦌) v
  let k : (sliceUnder (U ≫ sliceOverProjection x)).Edge w (sliceDiagramCocone U) :=
    ⟨e.edge, e.src_eq, e.tgt_eq⟩
  let c := relativeSliceCocone U k
  have hc : mapJoinCocone (sliceOverProjection x) c = w := by
    apply Subtype.ext
    exact relativeSliceCocone_projection U k
  have hv := congrArg (fun d : JoinCocone (U ≫ sliceOverProjection x) ↦ d.vertex) hc
  rw [Ind.mapJoinCocone_vertex] at hv
  exact ⟨c, hv⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
