module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnitAmbientHom
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDerivedPrecompositionFamily

/-!
# 元の導来単位が表す実正規化 Hom 前合成の全族

概要：同じ自由単位の正規化 Hom 前合成は、元の導来単位成分の前合成を任意 K で表す。
方針：元の閉辺の分解像を同じ導来単位の回収成分へ同定する。
規約：元の導来単位と全比較を保ち、零単体だけの一致で代用しない。
使われ方：標準 U 単位誘導射と実自由/導来 Hom span の全三角形の始域側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma freeProbeDerivedUnitNormalizedHom_family (X Y : Complex A) (K : SSet.{u + 1})
    (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A
        ((freeProbeFunctor A).obj X).carrier)).obj Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ SSet.uliftFunctor.{u + 1, u}.map
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((normalizedSimplexTensorFamily A).map
        ((operad A).freeAlgebraAdjunction.unit.app
          ((ComplexLimits.framedLimitProbeFunctor A).obj X)))).app Y) ≫
      (normalizedTensorPinchedIso A ((ComplexLimits.framedLimitProbeFunctor A).obj X) Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((ComplexLimits.framedLimitProbeFunctor A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (complexSemifreeResolutionInfinity A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((ComplexLimits.framedLimitProbeFunctor A).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (freeProbeDerivedUnitAmbientHom A X) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫
        (normalizedTensorPinchedIso A ((freeProbeFunctor A).obj X).carrier Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((freeProbeFunctor A).obj X).carrier) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (complexSemifreeResolutionInfinity A)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((freeProbeFunctor A).obj X).carrier) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) := by
  rw [freeProbeDerivedUnitAmbientHom_eq]
  exact normalizedTensorHom_precomp_family_map A (complexSemifreeResolutionInfinity A)
    (X := ((freeProbeFunctor A).obj X).carrier)
    (X' := (ComplexLimits.framedLimitProbeFunctor A).obj X) Y
    ((operad A).freeAlgebraAdjunction.unit.app
      ((ComplexLimits.framedLimitProbeFunctor A).obj X)) K g

end SerrePositivity.EInfinity.BarrattEccles
