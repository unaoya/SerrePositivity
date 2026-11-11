module

public import SerrePositivity.EInfinity.FrameHom.RightFrameTerminalRealization
public import SerrePositivity.EInfinity.FrameHom.HomInfinityLocalizationTransport

/-!
概要：同じ終端図式から指定局所化の正本 Hom 図式への比較を Yoneda の一入力へ還元する。
方針：構成済みの実終端同型・全 Yoneda 比較・同じ K と全二胞体の輸送を合成する。
規約：Yoneda 入力は原本の供給待ちであり、この補助入口だけで完成としない。
使われ方：Ind-S (8) の公開全図式比較の直接代入。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SerrePositivity.EInfinity.SimplicialLocalization
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  {G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q}
  (c : CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G)

/-- 概要：同じ終端から指定 G の共変 Hom への全図式比較の実還元。
方針：同じ終端実現に全 Yoneda 比較を前合成し、同じ指定 K・二胞体の輸送を合成する。
規約：唯一の追加比較は全 FunctorIso であり、点ごとの弱同値ではない。
使われ方：原本 Yoneda 全比較の代入後の主入口。 -/
def rightFrameTerminalHomIso_of_yonedaIso
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)).app
        (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (rightFrameHammockCoherentDiagram q r 6)
      (SSet.uliftFunctor.{max u v + 1, max u v}.map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))) :=
  rightFrameHammockTerminalRealizationIso q r ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp h (SSet.uliftFunctor.{max u v + 1, max u v}.map
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))) ≪≫
    c.homInfinityTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))

end SerrePositivity.EInfinity.FrameHom
