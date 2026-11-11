module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalHomPointComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeIntervalTransportUnit

/-!
概要：元の余錐の区間 Hom 比較の成分を、元の単位作用による前合成へ戻す。
方針：同じ係数での二座標の射を元の単位作用と係数制限に分解する。
規約：元の指定比較を保持。使われ方：元の定値三角形の因子消去との接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の Hom 比較の一点成分は、同じ定値輸送比較の一点制限を元の単位で前合成した値。 -/
lemma coconeIntervalFiberHomIso_app_heq_unit {B T : SSet.{u + 1}}
    [Quasicategory T] {F : B ⟶ SpaceInfinity.{u}}
    (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace c.vertex z) (l : T _⦋0⦌) :
    HEq ((coconeIntervalFiberHomIso c a).app l)
      (((constantDiagramMappingTransportIso B a).precomp (lift (𝟙 _) (SSet.const l))).precomp
        (leftUnstraighteningMappingVertexMap F (SSet.const c.vertex)
          (coconeTransformationVertex c)).val) := by
  refine (coconeIntervalFiberHomIso_app_heq_constant c a l).trans ?_
  refine (functorIso_precomp_heq_of_map_eq (constantDiagramMappingTransportIso B a)
    (coconeIntervalTransportSource_point c l)).trans ?_
  exact heq_of_eq (functorIso_precomp_precomp (constantDiagramMappingTransportIso B a)
    (lift (𝟙 _) (SSet.const l))
    (leftUnstraighteningMappingVertexMap F (SSet.const c.vertex)
      (coconeTransformationVertex c)).val).symm

end SerrePositivity.InfinityCategories.F2
