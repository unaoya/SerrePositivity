module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanEnrichedMap
public import SerrePositivity.EInfinity.SimplicialLocalization.Nerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
# 相対関手が誘導する局所化の coherent nerve の射

概要：Dwyer–Kan の相対係数関手を局所化の quasicategory の間の射へ送る。
方針：同じ Kan 豊穣係数関手に既存の coherent nerve の後合成を使う。
規約：頂点での作用は元の相対関手の対象写像そのもの。
使われ方：E 代数の忘却関手や離散対象関手の ∞ 関手化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory
open SerrePositivity.InfinityCategories

/-- 概要：相対関手は局所化の coherent nerve の射を誘導する（HTT §1.1.5）。
方針：元の Kan 豊穣係数関手へ同じ coherent nerve の後合成を適用する。
規約：始域・終域は構成済みの局所化 quasicategory。
使われ方：具体的な相対関手の ∞ 関手化の界面。 -/
def localizationNerveMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    localizationNerve C ⟶ localizationNerve D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (kanLocalizationEnrichedMap F)

/-- 概要：局所化の nerve の係数射は元の対象の頂点を保つ（HTT §1.1.5）。
方針：同じ coherent nerve の頂点自然性を使う。
規約：同じ対象表示と係数の対象写像を保持する。
使われ方：忘却関手などの頂点での計算。 -/
lemma localizationNerveMap_vertex {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (X : KanLocalizationCategory C) :
    (localizationNerveMap F).app (Opposite.op (SimplexCategory.mk 0))
        (localizationNerveVertexEquiv C X) =
      localizationNerveVertexEquiv D (F.functor.obj X) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((localizationNerveMap F).app (Opposite.op (SimplexCategory.mk 0))
      (localizationNerveVertexEquiv C X))).symm

end SerrePositivity.EInfinity.SimplicialLocalization
