module

public import SerrePositivity.EInfinity.BarrattEccles.CAlg
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNervePrecomposition

/-!
# 任意可換環の元の cofibrant 入力から既存 CAlg_R への実関手

概要：元の DK 相対圏の nerve を既存の CAlg_R へ送り、元の擬同型を反転する。
方針：同じ実局所化写像・同じ頂点比較・全標的の前合成比較を代入する。
規約：Hom の ULift・元の環・元の cofibrant 入力を保持する。
使われ方：E2b の全反転関手圏による ∞ 局所化の入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A]

def cAlgLocalizationSource :
    nerve (cofibrantAlgebraRelativeCategory A).category ⟶ CAlg_R A :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (cofibrantAlgebraRelativeCategory A)

lemma cAlgLocalizationSource_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (cAlgLocalizationSource A)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory A)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_inverts (cofibrantAlgebraRelativeCategory A)

def cAlgLocalizationSource_vertexIso (X : (cofibrantAlgebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
      (cAlgVertexEquiv A (show CAlgSimplicialCategory A from X)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_vertexIso (cofibrantAlgebraRelativeCategory A) X

lemma cAlgLocalizationSource_isLocalization_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (cAlgLocalizationSource A)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory A)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory A)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_isLocalization_iff (cofibrantAlgebraRelativeCategory A)

end SerrePositivity.EInfinity.BarrattEccles
