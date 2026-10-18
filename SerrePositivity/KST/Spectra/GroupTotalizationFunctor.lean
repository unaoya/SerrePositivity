module

public import SerrePositivity.KST.Spectra.GroupTotalizationMap

/-!
概要：通常の群 cochain の Tot の Kan Ω 列の関手性。
方針：各段が通常の Tot の射である式を使い、関手法則と BK 比較の自然性を示す。
規約：BF 置換前の Kan 列の圏の厳密な関手。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。通常の Tot による hG の関手的な模型。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の群 cochain の Tot の Kan Ω 列は同変射に関する厳密な関手。
方針：各段の cochain と通常の Tot の合成関手の恒等・合成法則を使う。
規約：構造射は密度の同型で移した構造を使う。
使われ方：Goerss–Jardine VIII §§1–2。対象と射を含む通常の Tot の Kan 模型。 -/
def totalizationKanFunctor (G : Type u) [Group G] : GroupAction.{u} G ⥤ KanSequence.{u} where
  obj A := totalizationKan A
  map f := totalizationKanMap f
  map_id A := by
    apply KanSequence.Hom.ext_app
    intro n
    change (totalizationKanMap (𝟙 A)).app n = 𝟙 (totalizationLevel A n).space
    rw [totalizationKanMap_app]
    exact CategoryTheory.Functor.map_id ((levelFunctor G n) ⋙ PointedTotalization.functor) A
  map_comp f g := by
    apply KanSequence.Hom.ext_app
    intro n
    change (totalizationKanMap (f ≫ g)).app n =
      (totalizationKanMap f).app n ≫ (totalizationKanMap g).app n
    rw [totalizationKanMap_app, totalizationKanMap_app, totalizationKanMap_app]
    exact CategoryTheory.Functor.map_comp ((levelFunctor G n) ⋙ PointedTotalization.functor) f g

/-- 概要：通常の Tot の Kan 列から BK end の Kan 列への比較は同変射に自然。
方針：各段の通常の Tot の射への式と密度の係数への自然性を使う。
規約：構造可換射の厳密な等式。
使われ方：Goerss–Jardine VIII §§1–2。hG と通常の Tot の射の模型比較。 -/
lemma totalizationKanComparison_natural {G : Type u} [Group G]
    {A B : GroupAction.{u} G} (f : A ⟶ B) :
    (totalizationKanMap f).comp (totalizationKanComparison B) =
      (totalizationKanComparison A).comp (fixedPointKanMap f) := by
  apply KanSequence.Hom.ext_app
  intro n
  change (totalizationKanMap f).app n ≫ (totalizationLevelIso B n).hom =
    (totalizationLevelIso A n).hom ≫ (fixedPointKanMap f).app n
  rw [totalizationKanMap_app]
  exact totalizationEndIso_natural G (Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down ((GroupAction.diagramFunctor G).map f))
    (OmegaSpectrum.levelEvaluation n))

end

end SerrePositivity.KST.Spectra.GroupActionCochains
