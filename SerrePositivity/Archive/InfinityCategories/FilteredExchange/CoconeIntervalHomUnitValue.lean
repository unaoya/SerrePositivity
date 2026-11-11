module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalHomUnitVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalHomUnitComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の区間 Hom 比較の指定成分の値を、元の単位による前合成後の同じ値へ戻す。
方針：元の両実射の頂点等式と同じ指定比較の一点表示を合成する。
規約：単位・比較・値への射を保持。使われ方：下側輸送因子と三角形消去の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定成分の任意の値への像は、同じ定値輸送比較の同じ単位での前合成の値。 -/
lemma coconeIntervalFiberHomIso_app_map_heq_unit {B T X : SSet.{u + 1}}
    [Quasicategory T] {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace c.vertex z) (l : T _⦋0⦌)
    (g : vertexFiber pointedSpaceProjection z ⟶ X) :
    HEq (VertexIso.map ((coconeIntervalFiberHomIso c a).app l)
      ((ihom (leftUnstraightening F)).map g))
      ((((constantDiagramMappingTransportIso B a).precomp (lift (𝟙 _) (SSet.const l))).precomp
        (leftUnstraighteningMappingVertexMap F (SSet.const c.vertex)
          (coconeTransformationVertex c)).val).postcomp g) := by
  rw [functorIso_postcomp_eq_mapIso]
  exact vertexIso_map_heq_of_heq _ _
    (coconeIntervalFiberHomIso_source_point_vertex c a l)
    (coconeIntervalFiberHomIso_target_point_vertex c a l)
    (coconeIntervalFiberHomIso_app_heq_unit c a l)
    ((ihom (leftUnstraightening F)).map g)

end SerrePositivity.InfinityCategories.F2
