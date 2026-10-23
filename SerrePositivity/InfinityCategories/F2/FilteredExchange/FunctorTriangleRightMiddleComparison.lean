module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleRightEndpointNormalized
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleMiddleComparison

/-!
概要：右辺の指定比較の native 始点像を、元の同じ中間比較の native 後合成へ同定する。
方針：元の全三角形比較の辺像の値と、右辺始点の厳密な中間評価への因子分解を使う。
規約：指定比較の値を保持。使われ方：全終点比較を元の二辺の比較へ表す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorTrianglePointedCanonicalWitness T p s hi
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J)
  (Subtype.val (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)))
  (Subtype.property (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b))) p

/-- 元の右辺の native 始点比較は、元の同じ中間比較の第二作用による後合成そのもの。 -/
lemma FunctorTrianglePointedWitness.rightNativeComparison_eq_middleNative :
    w.rightNativeComparison hi = w.middleNativeComparison hi := by
  let φ := w.rightPrismComparison hi
  let ν := w.comparison hi
  let E := w.edgeMap b 0 T.face_zero
  let q := functorHomotopyPrismSourceEvaluation b p
  have hx := w.edgeMap_vertex b 0 T.face_zero w
  have hy := w.edgeMap_vertex b 0 T.face_zero z
  have hm := vertexIso_map_heq_of_heq φ (VertexIso.map ν E) hx.symm hy.symm
    (w.prismComparison_heq_edge hi b 0 T.face_zero) (q ≫ P)
  have hf : E ≫ (q ≫ P) = w.middleMap ≫ P :=
    (Category.assoc E q P).symm.trans (congrArg (fun k => k ≫ P) w.rightSource_factor)
  have ha : HEq (w.rightNativeComparison hi) (VertexIso.map φ (q ≫ P)) :=
    vertexIsoOfEq_heq _
      (functorHomotopyPrismNativeSource_vertex b p w.middle w.middle_projection w.secondWitness)
      (functorHomotopyPrismNativeSource_vertex b p (z).middle (z).middle_projection
        (z).secondWitness)
  exact eq_of_heq (ha.trans (hm.trans
    ((heq_of_eq (vertexIso_map_comp ν E (q ≫ P))).trans
      ((vertexIso_map_heq ν hf).trans (w.middleNativeComparison_heq_map hi).symm))))

/-- 右辺の指定自然性は、元の中間比較と元の全終点比較を同じ第二作用で結ぶ。 -/
lemma FunctorTrianglePointedWitness.middleNativeComparison_eq :
    w.middleNativeComparison hi =
      functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness ≪≫
        w.rightEndpointComparison hi := by
  rw [← w.rightNativeComparison_eq_middleNative hi]
  exact w.rightNativeComparison_eq hi

end SerrePositivity.InfinityCategories.F2
