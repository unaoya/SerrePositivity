module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceDiagram
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge

/-!
概要：元の余錐の指定脚の辺表示と、同じ余錐の slice 図式の指定頂点を比較する。
方針：二点 join と区間の標準同型を相殺する。
規約：元の全辺を保つ値の厳密な等式。
使われ方：全図式の因子化が元の指定表示脚の上にあることの回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の指定表示脚の辺を join へ戻すと、slice 表示の同じ頂点の全値になる。
方針：余錐脚の既存の全辺表示と Yoneda の逆関係を使う。
規約：底の点だけではなく全区間射を比較する。
使われ方：相対全余錐の頂点を元の表示段に厳密に合わせる。 -/
lemma coconeTransportLeg_sliceDiagram_val {K C : SSet.{u}} {D : K ⟶ C}
    (c : JoinCocone D) (i : K _⦋0⦌) :
    (edgeCosliceVertex (Compact.coconeTransportLeg c i).toTruncated).val =
      ((coconeSliceDiagram c).app (Opposite.op ⦋0⦌) i).val := by
  change (joinStdSimplexIso 0 0).hom ≫
    SSet.yonedaEquiv.symm (Compact.coconeTransportLeg c i).edge = _
  rw [Compact.coconeTransportLeg_edge]
  change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm i) (𝟙 Δ[0]) ≫ c.val)) = _
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
