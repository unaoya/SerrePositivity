module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedProbeFrame
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorPrecompositionFamily

/-!
# 元の自由単位による正規化 Hom 前合成の全区間族

概要：実自由単位の前合成は、同じ全複体 dg nerve の単位辺の前合成を表す。
方針：任意の複体射の全族公式へ元の随伴の単位を代入する。
規約：任意可換環・任意パラメータ K で元の単位を保つ。
使われ方：自由 probe 単位と U の導来作用の全族比較の始域側。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma freeUnitNormalizedHom_family (X Y : Complex A) (K : SSet.{u + 1})
    (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A ((operad A).freeAlgebraFunctor.obj X).carrier)).obj Y)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A)
      (g ≫ SSet.uliftFunctor.{u + 1, u}.map
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorFamily A).map
          ((operad A).freeAlgebraAdjunction.unit.app X))).app Y) ≫
            (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A X Y).hom) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        ((operad A).freeAlgebraAdjunction.unit.app X)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A)
        (g ≫ (_root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso A
          ((operad A).freeAlgebraFunctor.obj X).carrier Y).hom) :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorPinchedIso_precomp_family A Y
    ((operad A).freeAlgebraAdjunction.unit.app X) K g

end SerrePositivity.EInfinity.BarrattEccles
