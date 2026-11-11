module

public import SerrePositivity.EInfinity.SimplicialLocalization.Hom
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
# 固定対象を持つ Dwyer–Kan の単体的豊穣圏

概要：Dwyer–Kan の Hom の単体集合と次数ごとの合成を厳密な豊穣圏へ束ねる。
方針：単位則と結合則を各次数の元の局所化圏の公理で照合する。
規約：Hom の Kan 性と元の Map^h との比較は後続で証明する。
使われ方：Kan 化と coherent nerve による CAlg_R の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory MonoidalCategory

/-- 概要：固定対象の単体的局所化の対象の型（Dwyer–Kan）。
方針：元の相対圏の対象を同じ型の別名として使う。
規約：元の通常圏の Category instance を変更しない。
使われ方：単体的豊穣構造を持つ対象の供給。 -/
def LocalizationObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : Type u := C.category

/-- 概要：元の固定対象と同じ Hom は単体的豊穣圏をなす（Dwyer–Kan）。
方針：同じ単体的単位・合成と各次数の単位則・結合則を束ねる。
規約：全恒等式を厳密に証明し、Hom の Kan 性は仮定しない。
使われ方：Kan 化する前の単体的局所化。 -/
instance localizationEnrichedCategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    EnrichedCategory SSet.{u} (LocalizationObjects C) where
  Hom X Y := localizationHom C X Y
  id X := localizationIdentity C X
  comp X Y Z := localizationComposition C X Y Z
  id_comp X Y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change 𝟙 _ ≫ f = f
    exact Category.id_comp f
  comp_id X Y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change f ≫ 𝟙 _ = f
    exact Category.comp_id f
  assoc W X Y Z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    change (q.1 ≫ q.2.1) ≫ q.2.2 = q.1 ≫ (q.2.1 ≫ q.2.2)
    exact Category.assoc _ _ _

/-- 概要：同じ単体的局所化の標準的な基礎の単体的圏（Dwyer–Kan）。
方針：Mathlib の ForgetEnrichment で単体的単位からの Hom を基礎圏にする。
規約：元の対象と豊穣 Hom を保持する。
使われ方：Hom の Kan 化と coherent nerve。 -/
abbrev LocalizationCategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :=
  ForgetEnrichment SSet.{u} (LocalizationObjects C)

/-- 概要：基礎圏は同じ Hom の単体的圏構造を持つ（Dwyer–Kan）。
方針：ForgetEnrichment の標準的な豊穣通常圏構造を使う。
規約：新たな合成・単位・Hom を選ばない。
使われ方：coherent nerve の入力。 -/
instance localizationSimplicialCategory (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    SimplicialCategory (LocalizationCategory C) :=
  inferInstanceAs (EnrichedOrdinaryCategory SSet.{u}
    (ForgetEnrichment SSet.{u} (LocalizationObjects C)))

/-- 概要：基礎の単体的圏の Hom は元の同じ局所化 Hom（Dwyer–Kan）。
方針：ForgetEnrichment の豊穣 Hom の定義を評価する。
規約：Hom を離散化せず全単体を保持する。
使われ方：後続の Kan 化との実際の Hom の比較。 -/
lemma localizationCategory_sHom (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : LocalizationCategory C) :
    SimplicialCategory.sHom X Y = localizationHom C X Y := rfl

end SerrePositivity.EInfinity.SimplicialLocalization
