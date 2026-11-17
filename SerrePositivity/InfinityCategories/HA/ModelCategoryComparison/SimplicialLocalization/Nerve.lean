module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanEnrichment
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices

/-!
# Kan 化した単体的局所化の coherent nerve

概要：Dwyer–Kan の具体的な単体的局所化から coherent nerve を構成する。
方針：実際の局所 Kan な豊穣圏に HTT 1.1.5.10 の既存の定理を適用する。
規約：Mathlib の SimplicialNerve を使い、局所 Kan 性は構成から供給する。
使われ方：CAlg_R の具体的な quasicategory とその頂点。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- 概要：Kan 化した単体的局所化の coherent nerve（Dwyer–Kan、HTT 1.1.5）。
方針：元の Kan 化した単体的圏へ Mathlib の SimplicialNerve を適用する。
規約：元の対象と同じ Ex∞ Hom を使う。
使われ方：E 代数相対圏の ∞ 圏化の対象。 -/
def localizationNerve (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : SSet.{u} :=
  SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C)

/-- 概要：構成した coherent nerve は quasicategory（HTT 1.1.5.10）。
方針：実際の Hom の Kan 性を既存の coherent nerve の定理へ代入する。
規約：単体集合のモデル構造やホーン充填の入力仮定を加えない。
使われ方：CAlg_R の ∞ 圏構造。 -/
instance localizationNerve_quasicategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    SSet.Quasicategory (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory _

/-- 概要：元の対象を同じ coherent nerve の頂点として表す（HTT 1.1.5）。
方針：元の単体的圏の対象と coherent nerve の頂点の既存の同値を使う。
規約：同型類や π₀ へ対象を落とさない。
使われ方：元の E 代数・離散可換代数からの頂点の供給。 -/
def localizationNerveVertexEquiv (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C ≃ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve C) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv _

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
