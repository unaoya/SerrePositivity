module

public import SerrePositivity.DifferentialGraded.Algebras.FrameComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameTerminalHomReduction

/-!
概要：実 dg モデルの指定局所化への全 Hom 比較を原本 Yoneda の一入力へ還元する。
方針：同じ実自由分解・right frame・指定局所化比較を完成済みの全図式還元へ代入する。
規約：この条件付き補助入口だけで供給完了とはしない。
使われ方：Ind-S (8) の全比較を代入する dg 主入口の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

/-- 概要：同じ実 dg 終端から指定局所化の正本 Hom 関手への全図式比較の還元。
方針：実分解の入力を放電済みの同じ局所化比較を代入する。
規約：唯一の追加仮定は原本側の全 Yoneda 同型。
使われ方：原本比較の公開後の直接代入。 -/
def frameTerminalHomIso_of_yonedaIso {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q)
      (_hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))))
      (X : Mon (Complex R)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))).app (op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
          (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) 6)
        (SSet.uliftFunctor.{u + 2, u + 1}.map G ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))) := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro G hG X h
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameTerminalHomIso_of_yonedaIso
    ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X) (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R)
    (_root_.SerrePositivity.DGAlgebra.frameLocalizationComparison R G hG) h

/-- 概要：同じ実 dg right frame の始端から正本の共変 Hom 図式への全比較の還元。
方針：元の六辺の全比較を同じ終端の還元へ合成する。
規約：cofibrant 源・任意標的、モデルや分解の追加入力なし。
使われ方：Sp の実 right frame 図式から指定局所化の Hom への主比較の構成。 -/
def frameCoherentHomIso_of_yonedaIso {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q)
      (_hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))))
      (X : Mon (Complex R)), IsCofibrant X →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))).app (op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
          (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) 0)
        (SSet.uliftFunctor.{u + 2, u + 1}.map G ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))) := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro G hG X hX h
  exact _root_.SerrePositivity.DGAlgebra.rightFrameHammockCoherentComparison R X hX ≪≫
    _root_.SerrePositivity.DGAlgebra.frameTerminalHomIso_of_yonedaIso R G hG X h

end SerrePositivity.DGAlgebra
