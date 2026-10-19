module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFunctorInitialBoundary
public import SerrePositivity.InfinityCategories.F1B.KanInitialBoundaryHom

/-!
概要：fiber ごとに普遍な相対 join 図式から出る大域的な写像空間の制限の同値。
方針：通常の関手の制限の始点境界充填から写像空間と h Fun の Hom へ移す。
規約：相手の図式には普遍性を要求しない。
使われ方：点ごとの Kan 条件から大域的な普遍写像性へ進む主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：普遍な相対 join 図式から任意の図式への右写像空間は左端への制限で同値となる。
方針：全 fiber の余極限性から通常の制限の相対始点境界充填を得て模型比較へ渡す。
規約：H の全 fiber の普遍性だけを使い、G の普遍性は仮定しない。
使われ方：相対 join の大域的な普遍写像性。 -/
lemma kanRelativeJoinFunctor_pinchedHomMap_equivalence {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (H G : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap ((pre (relativeJoinInl p (𝟙 C))).app D)
        (functorVertex H) (functorVertex G)) :=
  kanPinchedHomMap_equivalence_of_initialBoundary _ _ _
    (kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p H hcol)

/-- 概要：普遍な相対 join 図式から出る h Fun の Hom の制限は全単射。
方針：相対始点境界充填の一般の Hom 全単射を関手単体集合へ適用する。
規約：制限の作用は既存のホモトピー圏の関手の map。
使われ方：元の Kan 変換に対する大域的な自然変換の普遍性への接続。 -/
lemma kanRelativeJoinFunctor_homMap_bijective {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (H G : relativeJoin p (𝟙 C) ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H)) :
    Function.Bijective (((hoFunctor.map ((pre (relativeJoinInl p (𝟙 C))).app D)).toFunctor.map) :
      FunctorHom H G →
        FunctorHom (relativeJoinInl p (𝟙 C) ≫ H) (relativeJoinInl p (𝟙 C) ≫ G)) :=
  kanHoFunctorMap_bijective_of_initialBoundary _ _ _
    (kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p H hcol)

end SerrePositivity.InfinityCategories.F1B
