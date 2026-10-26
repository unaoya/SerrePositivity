module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputCoconeRecovery

/-!
概要：既存の相対 slice 余錐構成の元の入力付き頂点における全値を計算する。
方針：既存の辺への変換と三因子表示の二つの区間同型を相殺する。
規約：relativeSliceCocone をそのまま使い、新たな slice 交換同型を構成しない。
使われ方：追加入力の制限と成分後合成に関する全余錐の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の入力付き頂点に既存の相対 slice 余錐構成を適用する。
方針：元の標的への辺を既存の定義に渡す。
規約：既存の構成を変更せず、同じ元の全入力上の余錐を返す。
使われ方：同じ全余錐の成分像と入力制限の比較。 -/
def inputVertexSliceCocone {K X : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ X}
    (U : K ⟶ sliceOver x)
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌) :
    JoinCocone U := by
  let e := sliceOverVertexEdge (X := sliceUnder (U ≫ sliceOverProjection x))
    (sliceDiagramCocone U) v
  exact relativeSliceCocone U ⟨e.edge, e.src_eq, e.tgt_eq⟩

/-- 概要：既存の相対余錐の全展開は元の入力付き頂点の全展開の再結合。
方針：既存の三因子式内の区間同型と逆同型を相殺する。
規約：元の全単体集合射の厳密な等式。
使われ方：成分後合成と入力制限の下の全値の自然性。 -/
lemma inputVertexSliceCocone_uncurry {K X : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ X}
    (U : K ⟶ sliceOver x)
    (v : (sliceOver ((SSet.yonedaEquiv
      (X := sliceUnder (U ≫ sliceOverProjection x))).symm (sliceDiagramCocone U))) _⦋0⦌) :
    sliceOverUncurry (inputVertexSliceCocone U v).val =
      (HomotopyLimits.joinAssociator K Δ[0] Δ[0]).hom ≫ sliceUnderUncurry v.val := by
  dsimp only [inputVertexSliceCocone]
  rw [relativeSliceCocone, sliceOverUncurry_curry, relativeSliceCoconeMap]
  dsimp only [sliceOverVertexEdge, SSet.Edge.edge, SSet.Edge.toTruncated]
  erw [Equiv.symm_apply_apply]
  rw [sliceUnderUncurry_precomp]
  rw [← Category.assoc (joinMap _ _), ← joinMap_comp, Iso.hom_inv_id, Category.id_comp,
    joinMap_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
