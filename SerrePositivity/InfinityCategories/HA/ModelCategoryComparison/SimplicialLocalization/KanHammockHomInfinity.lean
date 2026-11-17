module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.EnrichedHomYoneda
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomCoherent

/-!
概要：元の Kan hammock Hom の全実現を正本の共変 Hom 全図式へ送る。
方針：原本 Yoneda の一つの全比較に同じ局所化頂点を代入する。
規約：点ごとの Hom 同値や新たな存在仮定で置き換えない。
使われ方：right frame の終端から指定局所化への全標的比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet _root_.Opposite
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

/-- 概要：同じ元の全 Kan Hom 実現と正本 Hom∞ の全標的同型。
方針：元の局所化頂点の等式で原本の全 Yoneda 同型を整える。
規約：全高次作用を保持。使われ方：指定局所化輸送への無条件の入力。 -/
def kanHammockHomInfinityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomCoherent C X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C).app
        (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) := by
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X = ComposableArrows.mk₀ X := ComposableArrows.ext₀ rfl
  rw [hx]
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomYonedaIso ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
