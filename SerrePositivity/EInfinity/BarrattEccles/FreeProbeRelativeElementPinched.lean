module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementRoof
public import SerrePositivity.EInfinity.BarrattEccles.CAlgLocalizationSource
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinched
/-! 概要：同じ自由列の全 roof 族を既存 CAlg_R の pinched Hom へ送る。
方針：元の hammock・Ex∞・coherent 比較と既存の局所化同値を合成する。
規約：全要素圏と実局所化源の両頂点を保持する。
使われ方：標準単位比較の全族三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite Hammock _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：同じ全 roof を既存 CAlg_R の pinched 全族にする。
方針：元の全単体写像を同じ比較射で後合成する。
規約：実局所化源の両頂点を保持。使われ方：全族単位比較。 -/
def freeProbeRelativeElementPinchedMap : nerve (freeProbeRelativeElementIndex A X B) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((cAlgLocalizationSource A).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X)))
      ((cAlgLocalizationSource A).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))) :=
  freeProbeRelativeElementRoofMap A X B ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
      (freeProbeRelativeElementSource A X) (ULiftHom.objUp.{u + 1, u + 1} B) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence (cofibrantAlgebraRelativeCategory A)).hom
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X)))
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)))

end SerrePositivity.EInfinity.BarrattEccles
