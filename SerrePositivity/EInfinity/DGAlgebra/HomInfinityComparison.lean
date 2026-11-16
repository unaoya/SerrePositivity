module

public import SerrePositivity.EInfinity.DGAlgebra.FrameComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHomInfinity

/-!
概要：実 dg right frame と指定局所化の正本共変 Hom の無条件の全比較。
方針：実自由分解・同じ局所化比較・原本 Yoneda 全同型を代入する。
規約：追加の比較・モデル・分解の存在仮定を残さない。
使われ方：Sp β6 f4d の全標的自然性と全添字図式の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory _root_.HomotopicalAlgebra SSet Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped Simplicial
variable (R : Type u) [CommRing R]

/-- 概要：同じ実 dg 終端から指定局所化の正本 Hom 関手への全図式同型。
方針：実分解の入力を放電済みの同じ局所化比較を代入する。
規約：原本 Yoneda 全比較も代入済み。
使われ方：Sp の終端図式から正本 Hom∞ への主入口。 -/
def frameTerminalHomIso {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q)
      (_hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))))
      (X : Mon (Complex R)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram ((sourceFrameFamily R).atObject X)
          (rightFrameFamily R) 6)
        (SSet.uliftFunctor.{u + 2, u + 1}.map G ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))) := by
  letI _modelInst := modelCategory R
  intro G hG X
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameTerminalHomIso
    ((sourceFrameFamily R).atObject X) (rightFrameFamily R)
    (frameLocalizationComparison R G hG)

/-- 概要：同じ実 dg right frame の始端から正本の共変 Hom 図式への全同型。
方針：元の六辺の全比較を同じ終端の無条件比較へ合成する。
規約：cofibrant 源・任意標的、モデルや分解の追加入力なし。
使われ方：Sp の実 right frame 図式から指定局所化の Hom への主比較の構成。 -/
def frameCoherentHomIso {Q : SSet.{u + 1}} [Quasicategory Q] :
    letI _modelInst := modelCategory R
    ∀ (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R))).category ⟶ Q)
      (_hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory (Mon (Complex R)))))
      (X : Mon (Complex R)), IsCofibrant X →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram ((sourceFrameFamily R).atObject X)
          (rightFrameFamily R) 0)
        (SSet.uliftFunctor.{u + 2, u + 1}.map G ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject (Mon (Complex R)) X)))) := by
  letI _modelInst := modelCategory R
  intro G hG X hX
  exact rightFrameHammockCoherentComparison R X hX ≪≫
    frameTerminalHomIso R G hG X

end SerrePositivity.EInfinity.DGAlgebra
