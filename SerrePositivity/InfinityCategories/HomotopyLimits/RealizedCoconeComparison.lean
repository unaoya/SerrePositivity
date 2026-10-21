module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalVertexHomotopy
public import SerrePositivity.InfinityCategories.F2.CoconeRealizationTransformation
public import SerrePositivity.InfinityCategories.F2.CoconeTransformationEquivalence
public import SerrePositivity.InfinityCategories.F2.YonedaHomotopyVertex

/-!
概要：指定変換の実現余錐と、同じ変換を表す元の余錐を全余錐空間内で比較する。
方針：元の実現ホモトピーを変換空間の同型にし、標準比較の充満忠実性で反映する。
規約：元の図式・指定頂点・指定余錐・元の変換を保持する。
使われ方：同じ単位三角形の長辺の区間比較を、全余錐の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K X : SSet.{u}} [Quasicategory X] {f : K ⟶ X} {z : X _⦋0⦌}

/-- 指定された元の余錐を指定頂点で読んだ、同じ変換空間の頂点。 -/
def coconeTransformationPointAt (c : JoinCocone f) (hz : c.vertex = z) :
    (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))) _⦋0⦌ :=
  (F2.coconeTransformationMap f z).app (Opposite.op ⦋0⦌) (F2.coconeMappingPointAt c z hz)

omit [Quasicategory X] in
/-- 同じ頂点をそのまま指定した変換は、元の余錐変換そのもの。 -/
lemma coconeTransformationPointAt_self (c : JoinCocone f) :
    coconeTransformationPointAt c rfl = F2.coconeTransformationVertex c := rfl

/-- 同じ指定変換の実現余錐の標準変換を、元の変換と結ぶ実現比較。 -/
def realizedCoconeTransformationIso
    (t : (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))) _⦋0⦌)
    (R : F2.HomotopyCoconeRealization
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated)) :
    VertexIso (coconeTransformationPointAt R.cocone R.vertex_eq) t :=
  F2.vertexIsoOfYonedaHomotopy (F2.coconeRealizationTransformationHomotopy t R)

/-- 元の指定余錐と指定変換の同型を、同じ実現余錐との全余錐同型へ反映。 -/
def coconeRealizationComparisonIso
    (t : (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))) _⦋0⦌)
    (R : F2.HomotopyCoconeRealization
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated))
    (c : JoinCocone f) (hz : c.vertex = z)
    (e : VertexIso (coconeTransformationPointAt c hz) t) :
    VertexIso (X := coconeMappingSpace f z) (F2.coconeMappingPointAt c z hz)
      (F2.coconeMappingPointAt R.cocone z R.vertex_eq) :=
  (F2.coconeTransformationMap_isQCatEquivalence f z).isFullyFaithful.preimageVertexIso
    (e ≪≫ (realizedCoconeTransformationIso t R).symm)

end SerrePositivity.InfinityCategories.HomotopyLimits
