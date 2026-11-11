module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteEmbedding
public import SerrePositivity.EInfinity.BarrattEccles.ZeroDegreeDiscreteSpan

/-!
# 零次ホモロジー集中代数頂点の元の離散像との同型

概要：実代数の擬同型 span を CAlg_R の元の頂点同型へ移す。
方針：元の二つの代数射を反転し、同じ離散関手の頂点比較を合成する。
規約：底の D(R) の同型だけに還元しない。
使われ方：離散対象の本質像の逆包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

def cAlgZeroDegreeDiscreteIso (B : (operad A).Algebra)
    [B.carrier.IsLE 0] [B.carrier.IsGE 0] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (cAlgVertex A B)
      ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (zeroDegreeDiscreteAlgebra A B))) :=
  (cAlgVertexIsoOfQuasiIso A (connectiveCoverInclusion A B)
    (connectiveCoverInclusion_quasiIso A B)).symm ≪≫
      cAlgVertexIsoOfQuasiIso A (zeroDegreeDiscreteComparison A B)
        (zeroDegreeDiscreteComparison_quasiIso A B) ≪≫
          (discreteCAlgEmbedding_vertexIso A (zeroDegreeDiscreteAlgebra A B)).symm

end SerrePositivity.EInfinity.BarrattEccles
