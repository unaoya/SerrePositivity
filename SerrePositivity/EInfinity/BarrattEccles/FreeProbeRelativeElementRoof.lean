module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementRecovery
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofSameUniverseComparison
/-! 概要：同じ要素圏上の自由列を全単体の相対 roof へ送る。
方針：元の左脚・評価と全縦弱同値を LeftRoof の既存構成へ代入する。
規約：同じ Hom 宇宙と全要素圏を保持する。
使われ方：標準単位比較の CAlg_R 全 pinched 族への入口。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：同じ全自由列の二列 roof 図式。
方針：元の augmentation・評価を既存 LeftRoof へ代入。
規約：全縦弱同値を保持。使われ方：全単体の hammock 比較。 -/
def freeProbeRelativeElementRoof : freeProbeRelativeElementIndex A X B ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (cofibrantAlgebraRelativeCategory A).weakEquivalences _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word
      (freeProbeRelativeElementSource A X) (ULiftHom.objUp.{u + 1, u + 1} B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram (cofibrantAlgebraRelativeCategory A).weakEquivalences
    (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
    (freeProbeRelativeElementAugmentation_weak A X B)
    (freeProbeRelativeElementEvaluation A X B)
    (fun f => freeProbeRelativeElementColumn_map_weak A X B f)

/-- 概要：全要素圏 nerve から元の hammock 余極限への実写像。
方針：SameUniverse の既存全単体入口を使う。
規約：全パラメータを保持。使われ方：CAlg_R の全 pinched 族。 -/
def freeProbeRelativeElementRoofMap : nerve (freeProbeRelativeElementIndex A X B) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (freeProbeRelativeElementSource A X) (ULiftHom.objUp.{u + 1, u + 1} B) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap
    (cofibrantAlgebraRelativeCategory A).weakEquivalences (freeProbeRelativeElementRoof A X B)

end SerrePositivity.EInfinity.BarrattEccles
