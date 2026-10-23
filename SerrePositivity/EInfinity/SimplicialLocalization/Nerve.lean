module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanEnrichment
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices

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

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory
open scoped Simplicial

/-- 概要：Kan 化した単体的局所化の coherent nerve（Dwyer–Kan、HTT 1.1.5）。
方針：元の Kan 化した単体的圏へ Mathlib の SimplicialNerve を適用する。
規約：元の対象と同じ Ex∞ Hom を使う。
使われ方：E 代数相対圏の ∞ 圏化の対象。 -/
def localizationNerve (C : RelativeCategory.{u}) : SSet.{u} :=
  SimplicialNerve (KanLocalizationCategory C)

/-- 概要：構成した coherent nerve は quasicategory（HTT 1.1.5.10）。
方針：実際の Hom の Kan 性を既存の coherent nerve の定理へ代入する。
規約：単体集合のモデル構造やホーン充填の入力仮定を加えない。
使われ方：CAlg_R の ∞ 圏構造。 -/
instance localizationNerve_quasicategory (C : RelativeCategory.{u}) :
    SSet.Quasicategory (localizationNerve C) :=
  SerrePositivity.InfinityCategories.Coherent.simplicialNerve_quasicategory _

/-- 概要：元の対象を同じ coherent nerve の頂点として表す（HTT 1.1.5）。
方針：元の単体的圏の対象と coherent nerve の頂点の既存の同値を使う。
規約：同型類や π₀ へ対象を落とさない。
使われ方：元の E 代数・離散可換代数からの頂点の供給。 -/
def localizationNerveVertexEquiv (C : RelativeCategory.{u}) :
    KanLocalizationCategory C ≃ (localizationNerve C) _⦋0⦌ :=
  SerrePositivity.InfinityCategories.coherentNerveVertexEquiv _

end SerrePositivity.EInfinity.SimplicialLocalization
