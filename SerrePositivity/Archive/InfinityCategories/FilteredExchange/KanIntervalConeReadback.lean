module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeLeg
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeComparisonNaturality

/-!
概要：区間引き戻し錐の全円柱を元の切断成分と置換錐の実際の脚へ同定する。
方針：元の全一単体を保持する読み戻しと strict 錐の脚の式。
規約：元の頂点と射を変更しない。使われ方：元の指定 path との二次の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：同じ coherent 一単体を持つ Kan 射は同じ。
方針：射と辺の往復。規約：指定両端。使われ方：元の成分と脚の読み戻し。 -/
lemma kanHom_eq_of_coherent_edge_eq {A B : KanObject.{u}} {f g : A ⟶ B}
    (h : (coherentNerveEdge f).edge = (coherentNerveEdge g).edge) : f = g :=
  eq_of_heq ((heq_of_eq (coherentEdgeHom_edge f)).symm.trans (coherentEdgeHom_of_edge_eq h))

/-- 概要：元の区間錐の比較を Kan 図式上の全円柱として表示する。
方針：置換錐の表示だけを正規化。規約：円柱そのものは同じ。使われ方：指定比較。 -/
def intervalPullbackKanConeHomotopy (f : X ⟶ Y) (g : Z ⟶ Y) :
    SSet.Homotopy (intervalPullbackCone f g).val
      (spacePullbackCone (intervalReplacementKanEndpoint f) g).val :=
  intervalPullbackConeHomotopy f g

/-- 概要：置換錐の頂点は元の区間引き戻し対象。
方針：元の頂点の式。規約：厳密な等式。使われ方：指定射の読み戻し。 -/
lemma intervalPullbackKanConeTarget_vertex (f : X ⟶ Y) (g : Z ⟶ Y) :
    (spacePullbackCone (intervalReplacementKanEndpoint f) g).vertex =
      coherentNerveVertex (intervalPullbackKanObject f g) :=
  intervalPullbackReplacementCone_vertex f g

/-- 概要：図式成分の読み戻しは元の定値 path 切断の成分と厳密に一致する。
方針：元の一単体と切断の成分の辺の一致。
規約：元の自然変換を保持。使われ方：二次の自然性への切断の代入。 -/
lemma intervalPullbackKanCone_component (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    kanConeDiagramComponent (intervalPullbackKanConeHomotopy f g) i =
      (intervalCospanSection f g).app i := by
  apply kanHom_eq_of_coherent_edge_eq
  exact (kanConeDiagramComponent_edge _ i).trans (intervalPullbackConeHomotopy_diagramEdge f g i)

/-- 概要：置換錐の脚の読み戻しは元の通常の引き戻し射影。
方針：strict な錐の全一単体と辺の逆対応。
規約：元の頂点を保持。使われ方：指定脚比較の終点の同定。 -/
lemma intervalPullbackKanCone_targetLeg (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    kanNativeConeLeg (spacePullbackCone (intervalReplacementKanEndpoint f) g) _
      (intervalPullbackKanConeTarget_vertex f g) i =
      (kanPullbackCone (intervalReplacementKanEndpoint f) g).π.app i := by
  apply kanHom_eq_of_coherent_edge_eq
  exact (kanNativeConeLeg_edge _ _ _ i).trans
    (nativeConeLeg_strict (kanPullbackCone (intervalReplacementKanEndpoint f) g) i)

end SerrePositivity.InfinityCategories.F2
