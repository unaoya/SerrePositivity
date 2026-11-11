module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanMapLaws
public import SerrePositivity.EInfinity.SimplicialLocalization.NerveMap

/-!
# 相対圏から局所化の coherent nerve への関手

概要：Dwyer–Kan の同じ局所化 nerve の係数射を厳密な関手に束ねる。
方針：Kan 化した豊穣係数関手の恒等・合成を coherent nerve の後合成で送る。
規約：対象・Hom・単位・合成を元の構成のまま保持する。
使われ方：忘却や離散対象の ∞ 関手の合成の整合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory
open SerrePositivity.InfinityCategories

/-- 概要：恒等相対関手は局所化 nerve の恒等射を誘導する（HTT §1.1.5）。
方針：同じ Kan 豊穣係数関手の恒等則を nerve へ送る。
規約：元の coherent nerve を使う。
使われ方：局所化 nerve の係数関手の恒等則。 -/
lemma localizationNerveMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    localizationNerveMap (𝟙 C) = 𝟙 (localizationNerve C) := by
  unfold localizationNerveMap
  rw [kanLocalizationEnrichedMap_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id (KanLocalizationCategory C)

/-- 概要：相対関手の合成は局所化 nerve の射の合成を誘導する（HTT §1.1.5）。
方針：同じ Kan 豊穣係数関手の合成則を nerve へ送る。
規約：元の相対関手の合成順序を保持する。
使われ方：忘却や離散対象の係数関手の合成則。 -/
lemma localizationNerveMap_comp {C D E : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) (G : D ⟶ E) :
    localizationNerveMap (F ≫ G) = localizationNerveMap F ≫ localizationNerveMap G := by
  unfold localizationNerveMap
  rw [kanLocalizationEnrichedMap_comp]
  rfl

/-- 概要：相対圏の単体的局所化の coherent nerve は関手をなす（Dwyer–Kan）。
方針：同じ対象・係数射と厳密な恒等・合成則を束ねる。
規約：全ての値は構成済みの quasicategory。
使われ方：具体的なモデルの ∞ 関手の関手的な供給。 -/
def localizationNerveFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ SSet.{u} where
  obj := localizationNerve
  map := localizationNerveMap
  map_id := localizationNerveMap_id
  map_comp := localizationNerveMap_comp

end SerrePositivity.EInfinity.SimplicialLocalization
