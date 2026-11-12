module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeActionComponents
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

/-!
概要：指定された全空間射の比較を、元の native 単位の模型側比較へ移す。
方針：同じ比較を元の単位で後合成し、宇宙の持ち上げと縮小同型を通して写す。
規約：元の比較・単位・両実射を保持。使われ方：元の三角形に対する正方形 hu。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})

/-- 元の単位の自然性に沿う表示変更は、同じ実頂点の縮小同型による像を保持する。 -/
lemma coherentTotalMapNativeModel_vertex
    (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G) :
    (smallUnstraighteningHomIso F (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).inv.app
      (Opposite.op ⦋0⦌) (ULift.up (functorVertex (a ≫ coherentDiagramTotalUnit G))) =
      functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a)) := by
  refine (smallUnstraighteningHomIso_inv_vertex F (a ≫ coherentDiagramTotalUnit G)).trans ?_
  exact congrArg (fun h => functorVertex
    ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map h))
    (coherentTotalVertexMap_unit F G a).symm

/-- 指定された全空間比較の同じ単位での像を、元の native 模型側比較として保持する。 -/
def coherentTotalMapNativeModelComparison
    {a b : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G} (e : FunctorIso a b) :
    VertexIso
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a)))
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b))) :=
  vertexIsoOfEq (VertexIso.map (uliftVertexIso.{u, u + 1} (e.postcomp (coherentDiagramTotalUnit G)))
    (smallUnstraighteningHomIso F (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).inv)
    (coherentTotalMapNativeModel_vertex F G a) (coherentTotalMapNativeModel_vertex F G b)

end SerrePositivity.InfinityCategories.F2
