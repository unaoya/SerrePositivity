module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.F1.CoherentEdgeEquiv

/-!
概要：pointed-space 射影と left unstraightening の fiber の零単体を比較する。
方針：coslice の辺表示、coherent nerve の辺と通常の射の同値、Yoneda を合成する。
規約：零単体の型の同値を証明する。fiber 全体の同値には高次単体の比較が必要。
使われ方：Kerodon Construction 5.5.2.1、Example 5.6.2.9、𝒮 値 unstraightening の値の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pointed-space 射影の K 上の fiber の零単体は K の零単体と同値。
方針：一点空間から K への coherent な辺を通常の射に直し、Yoneda で点を取り出す。
規約：左辺の宇宙は u+1、右辺の宇宙は u。
使われ方：Kerodon Construction 5.5.2.1、pointed-space fiber の比較の零次部分。 -/
noncomputable def pointedSpaceFiberVertexEquiv (K : KanObject.{u}) :
    (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌ ≃ K.obj _⦋0⦌ := by
  let e := cosliceFiberVertexEquiv pointSpaceVertex (spaceInfinityVertex K)
  have h : SpaceInfinity.Edge pointSpaceVertex (spaceInfinityVertex K) ≃
      (pointKanObject ⟶ K) := by
    dsimp only [pointSpaceVertex]
    rw [spaceInfinityVertex_eq_coherent, spaceInfinityVertex_eq_coherent]
    exact coherentNerveEdgeEquiv pointKanObject K
  exact e.trans (h.trans SSet.yonedaEquiv)

/-- 概要：任意の 𝒮 の頂点上の pointed-space fiber の零単体を対応する空間の点にする。
方針：coherent nerve の頂点と KanObject の同値で標準頂点に書き直す。
規約：頂点に代表の選択を追加せず、その対象を直接評価する。
使われ方：Kerodon Construction 5.5.2.1、coherent な図式の任意の頂点の fiber 比較。 -/
noncomputable def pointedSpaceFiberVertexEquivAt (s : SpaceInfinity.{u} _⦋0⦌) :
    (vertexFiber pointedSpaceProjection s) _⦋0⦌ ≃ (spaceInfinityObject s).obj _⦋0⦌ := by
  have hs : spaceInfinityVertex (spaceInfinityObject s) = s :=
    spaceInfinityVertexEquiv.apply_symm_apply s
  rw [← hs]
  exact pointedSpaceFiberVertexEquiv (spaceInfinityObject s)

/-- 概要：left unstraightening の fiber の零単体は図式の値の零単体と同値。
方針：引き戻し fiber の同型の零次成分を pointed-space fiber の比較と合成する。
規約：底の quasicategory 性は不要。図式は coherent nerve に値を持つ。
使われ方：Kerodon Example 5.6.2.9、unstraightening の fiber と値の比較の零次部分。 -/
noncomputable def leftUnstraighteningFiberVertexEquiv {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection F) c) _⦋0⦌ ≃
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) c)).obj _⦋0⦌ :=
  (CategoryTheory.Iso.toEquiv
    (((evaluation _ _).obj (Opposite.op ⦋0⦌)).mapIso
      (leftUnstraighteningFiberIso F c))).trans
        (pointedSpaceFiberVertexEquivAt (F.app (Opposite.op ⦋0⦌) c))

end SerrePositivity.InfinityCategories
