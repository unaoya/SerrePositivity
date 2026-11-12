module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningEvaluation

/-!
概要：同じ元の区間族の終点表示の変更は、Hom 比較の成分と値への像を保持する。
方針：終点の等式と同じ族の型付き一致だけを消去する。
規約：元の比較を保持。使われ方：既存の下側輸送因子の raw/native 表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ元の族の終点表示だけの変更は、同じ Hom 比較の指定成分を保持する。 -/
lemma coconeIntervalFiberHomIso_app_heq_of_target_eq {B T : SSet.{u + 1}}
    [Quasicategory T] {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
    (a : T ⟶ intervalMappingSpace c.vertex z) (a' : T ⟶ intervalMappingSpace c.vertex z')
    (ha : HEq a a') (l : T _⦋0⦌) :
    HEq ((coconeIntervalFiberHomIso c a).app l) ((coconeIntervalFiberHomIso c a').app l) := by
  cases hz
  cases eq_of_heq ha
  rfl

/-- 同じ元の族の終点表示変更は、指定成分の元の fiber の値への像も保持する。 -/
lemma coconeIntervalFiberHomIso_app_value_heq_of_target_eq {B T : SSet.{u + 1}}
    [Quasicategory T] {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
    {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')
    (a : T ⟶ intervalMappingSpace c.vertex z) (a' : T ⟶ intervalMappingSpace c.vertex z')
    (ha : HEq a a') (l : T _⦋0⦌) :
    HEq (VertexIso.map ((coconeIntervalFiberHomIso c a).app l)
      ((ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom))
      (VertexIso.map ((coconeIntervalFiberHomIso c a').app l)
        ((ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z').hom)) := by
  cases hz
  cases eq_of_heq ha
  rfl

end SerrePositivity.InfinityCategories.F2
