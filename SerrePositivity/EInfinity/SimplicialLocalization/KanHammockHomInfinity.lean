module

public import SerrePositivity.EInfinity.FrameHom.EnrichedHomYoneda
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomCoherent

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet Opposite
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

/-- 概要：同じ元の全 Kan Hom 実現と正本 Hom∞ の全標的同型。
方針：元の局所化頂点の等式で原本の全 Yoneda 同型を整える。
規約：全高次作用を保持。使われ方：指定局所化輸送への無条件の入力。 -/
def kanHammockHomInfinityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kanHammockHomCoherent C X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((hammockLocalizationNerveMap C).app
        (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) := by
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X = ComposableArrows.mk₀ X := ComposableArrows.ext₀ rfl
  rw [hx]
  rw [hammockLocalizationNerveMap_vertex]
  exact enrichedHomYonedaIso ((kanHammockSourceFunctor C).obj X)

end SerrePositivity.EInfinity.SimplicialLocalization
