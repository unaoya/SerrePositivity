module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceOverRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：元の余錐の slice 図式の後合成を、像の余錐の slice 図式へ全射として比較する。
方針：既存の slice 後合成を、元の余錐頂点の像の厳密な等式で正規化する。
規約：元の余錐と後合成余錐を選び直さない。
使われ方：可算交互構成の第一成分の全偶数比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：像の余錐の標的は、元の標的点の後合成と一致する。
方針：余錐頂点の後合成公式と Yoneda 自然性。
規約：点射そのものの等式。
使われ方：固定標的 slice 後合成の正規化。 -/
lemma coconeSliceImagePoint_eq {K E B : SSet.{u}} {D : K ⟶ E}
    (c : JoinCocone D) (p : E ⟶ B) :
    SSet.yonedaEquiv.symm c.vertex ≫ p = SSet.yonedaEquiv.symm (mapJoinCocone p c).vertex := by
  rw [Ind.mapJoinCocone_vertex, SSet.yonedaEquiv_symm_comp]

/-- 概要：元の余錐頂点の slice から像の余錐頂点の slice への全後合成。
方針：既存の後合成を固定標的点の等式で移送する。
規約：元の図式の後合成 API を使う。
使われ方：元の compact 可算図式の像の全比較。 -/
def coconeSliceImageMap {K E B : SSet.{u}} {D : K ⟶ E}
    (c : JoinCocone D) (p : E ⟶ B) :
    sliceOver (SSet.yonedaEquiv.symm c.vertex) ⟶
      sliceOver (SSet.yonedaEquiv.symm (mapJoinCocone p c).vertex) :=
  sliceOverPostcomp (SSet.yonedaEquiv.symm c.vertex) p ≫
    eqToHom (congrArg sliceOver (coconeSliceImagePoint_eq c p))

/-- 概要：正規化した後合成の全展開は元の全展開の後合成。
方針：固定図式の等号移送を全 uncurry で除く。
規約：全族についての厳密な等式。
使われ方：元の指定可算余錐の像の比較。 -/
lemma coconeSliceImageMap_uncurry {K E B T : SSet.{u}} {D : K ⟶ E}
    (c : JoinCocone D) (p : E ⟶ B) (a : T ⟶ sliceOver (SSet.yonedaEquiv.symm c.vertex)) :
    sliceOverUncurry (a ≫ coconeSliceImageMap c p) = sliceOverUncurry a ≫ p := by
  rw [coconeSliceImageMap, ← Category.assoc,
    sliceOverUncurry_eqToHom (coconeSliceImagePoint_eq c p), sliceOverUncurry_postcomp]

/-- 概要：元の余錐の slice 表示を後合成すると、像の余錐の slice 表示そのもの。
方針：全 uncurry の単射性と元の余錐値の後合成を使う。
規約：全射の等式。
使われ方：第一成分の元の表示を全交互図式の偶数部分列に接続する。 -/
lemma coconeSliceDiagram_postcomp {K E B : SSet.{u}} {D : K ⟶ E}
    (c : JoinCocone D) (p : E ⟶ B) :
    coconeSliceDiagram c ≫ coconeSliceImageMap c p = coconeSliceDiagram (mapJoinCocone p c) := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm (mapJoinCocone p c).vertex)
  rw [coconeSliceImageMap_uncurry, coconeSliceDiagram_uncurry, coconeSliceDiagram_uncurry]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
