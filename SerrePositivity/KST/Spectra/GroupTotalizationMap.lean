module

public import SerrePositivity.KST.Spectra.GroupTotalizationSequence
public import SerrePositivity.KST.Spectra.GroupTotalizationNaturality
public import SerrePositivity.KST.Spectra.KanSequenceLevelIsoMap
public import SerrePositivity.KST.Spectra.GroupActionCochainFunctor
public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitMap

/-!
概要：同変なスペクトル射が通常の群 cochain の Tot の Kan Ω 列に誘導する厳密な射。
方針：BK end の射を段の同型で共役し、各成分が通常の Tot の射そのものであると示す。
規約：単射構造射の置換前の列の射であり、構造は指定した密度比較による移送。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。hG と通常の Tot の関手的な比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G] {A B : GroupAction.{u} G}

/-- 概要：同変射を置換前の hG の Kan end の厳密な射へ送る。
方針：作用図式の自然変換を Kan end の関手へ渡す。
規約：各段は点つき end の係数への後合成。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot の射を比較する BK 側の射。 -/
def fixedPointKanMap (f : A ⟶ B) : KanSequence.Hom
    (homotopyFixedPointsKan A) (homotopyFixedPointsKan B) :=
  KanSequence.homotopyLimitMap (Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down ((GroupAction.diagramFunctor G).map f))
    OmegaSpectrum.forgetToKan)

/-- 概要：同変射を通常の群 Tot の Kan Ω 列の厳密な射へ送る。
方針：BK end の射を密度の段の同型で共役する。
規約：各段が通常の Tot の射であることを後の式で確認する。
使われ方：Goerss–Jardine VIII §§1–2。通常の Tot のスペクトル列の射への作用。 -/
def totalizationKanMap (f : A ⟶ B) : KanSequence.Hom (totalizationKan A) (totalizationKan B) :=
  KanSequence.changeLevelsMap (totalizationLevel A) (totalizationLevel B)
    (totalizationLevelIso A) (totalizationLevelIso B) (fixedPointKanMap f)

/-- 概要：通常の Tot の列の射の各段は余単体 cochain の射から誘導する通常の Tot の射。
方針：密度比較の係数への自然性で共役の同型を相殺する。
規約：各段の点つき射の厳密な等式。
使われ方：Goerss–Jardine VIII §§1–2。Tot の対象と射の具体的な整合性。 -/
lemma totalizationKanMap_app (f : A ⟶ B) (n : ℕ) :
    (totalizationKanMap f).app n = PointedTotalization.map (levelMap f n) := by
  rw [totalizationKanMap, KanSequence.changeLevelsMap_app]
  have h := totalizationEndIso_natural G (Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down ((GroupAction.diagramFunctor G).map f))
    (OmegaSpectrum.levelEvaluation n))
  change PointedTotalization.map (levelMap f n) ≫ (totalizationLevelIso B n).hom =
    (totalizationLevelIso A n).hom ≫ (fixedPointKanMap f).app n at h
  apply (cancel_mono (totalizationLevelIso B n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h.symm

end

end SerrePositivity.KST.Spectra.GroupActionCochains
