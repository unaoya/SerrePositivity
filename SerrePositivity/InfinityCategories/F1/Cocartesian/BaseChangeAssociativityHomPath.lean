module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityYoneda
public import SerrePositivity.InfinityCategories.F1.InvertibleFunctorEdgePathEdgeFamily

/-!
概要：既存の元の結合比較辺を、同じ全高次の可逆 path の族にする。
方針：既存の同じ辺の可逆性を使い、元の区間族を包含後に厳密に回収する。
規約：結合比較の代表を選び直さない。
使われ方：元の第二比較の分解の Hom 比較 span。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 既存の元の結合比較辺を保つ、全 fibration 上の同じ可逆 path の族。 -/
def cocartesianBaseChangeAssociativityHomPath :
    CocartesianFibrationInfinity (nerve C) ⟶
      equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  invertibleFunctorEdgePath (cocartesianBaseChangeAssociativityEdge l k).toTruncated
    (cocartesianBaseChangeAssociativityEdge_isInvertible l k)

/-- 同じ可逆 path の包含は、既存の元の結合比較の区間族そのもの。 -/
lemma cocartesianBaseChangeAssociativityHomPath_ι :
    cocartesianBaseChangeAssociativityHomPath l k ≫ equivalencePathι _ =
      cocartesianBaseChangeAssociativityIntervalFamily l k :=
  invertibleFunctorEdgePath_ι_of_edge_family
    (A := CocartesianFibrationInfinity (nerve C))
    (Y := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))
    (cocartesianBaseChangeAssociativityEdge l k)
    (cocartesianBaseChangeAssociativityEdge_isInvertible l k)
    (cocartesianBaseChangeAssociativityIntervalFamily l k)
    (cocartesianBaseChangeAssociativityEdge_yoneda l k)

/-- 同じ path の零端点は、元の二回の底変換に続く元の分類主写像。 -/
lemma cocartesianBaseChangeAssociativityHomPath_zero :
    cocartesianBaseChangeAssociativityHomPath l k ≫ equivalencePathEndpoint _ 0 =
      cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianFibrationInfinityBaseChange (nerveMap l) ≫
          cocartesianStraighteningCoherentMap A := invertibleFunctorEdgePath_zero _ _

/-- 同じ path の一端点は、元の直接の底変換に続く元の分類主写像。 -/
lemma cocartesianBaseChangeAssociativityHomPath_one :
    cocartesianBaseChangeAssociativityHomPath l k ≫ equivalencePathEndpoint _ 1 =
      cocartesianFibrationInfinityBaseChange (nerveMap (l ⋙ k)) ≫
        cocartesianStraighteningCoherentMap A := invertibleFunctorEdgePath_one _ _

end SerrePositivity.InfinityCategories
