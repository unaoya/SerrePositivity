module

public import SerrePositivity.KST.Spectra.GroupPointedTotalization
public import SerrePositivity.KST.Spectra.KanSequenceLevelIso
public import SerrePositivity.KST.Spectra.FixedPointSpectra

/-!
概要：群 cochain の通常の Tot を各段に持つ Kan Ω 列とその BF 置換。
方針：段ごとの点つき密度の同型で BK end の構造を移し、単射構造射へ置換する。
規約：構造射は指定した同型による移送で定義する。∞ 極限性は主張しない。
使われ方：Goerss–Jardine VIII §§1–2、BF 1978 §2、HA §1.4.2。hG と通常の Tot の具体的な模型。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {G : Type u} [Group G] (A : GroupAction.{u} G)

/-- 概要：群 cochain の通常の Tot を段とする点つき Kan 複体。
方針：EG の重みと BK end の同型から Kan 性を移す。
規約：Reedy 置換なしの通常の Tot そのもの。
使われ方：Goerss–Jardine VIII §§1–2。通常の Tot の Kan Ω 列の各段。 -/
def totalizationLevel (n : ℕ) : PointedKanComplex.{u} where
  space := PointedTotalization.obj (level A n)
  kan := by
    let : ∀ i, KanComplex
        (((AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙
          OmegaSpectrum.levelEvaluation n).obj i).right) :=
      fun _ ↦ inferInstanceAs (KanComplex (A.V.level n).space.right)
    exact totalization_kanComplex G
      (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙ OmegaSpectrum.levelEvaluation n)

/-- 概要：通常の Tot の各段と hG の Kan end の各段との点つき同型。
方針：密度と EG の重みの比較を作用のスペクトル段の係数へ適用する。
規約：各段の厳密な点つき同型。
使われ方：Goerss–Jardine VIII §§1–2。Ω 構造の移送に指定する同型。 -/
def totalizationLevelIso (n : ℕ) :
    (totalizationLevel A n).space ≅ ((homotopyFixedPointsKan A).level n).space :=
  totalizationEndIso G
    (AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A ⋙ OmegaSpectrum.levelEvaluation n)

/-- 概要：群 cochain の通常の Tot の段に hG の構造射を移した Kan 列。
方針：随伴構造射を密度の点つき同型で共役して uncurry する。
規約：この宣言は移送による構造射を定義する。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot による hG の Kan Ω 模型。 -/
def totalizationKan : KanSequence.{u} :=
  KanSequence.changeLevels (homotopyFixedPointsKan A) (totalizationLevel A) (totalizationLevelIso A)

/-- 概要：通常の Tot の列は Ω 条件を満たす。
方針：BK end の Ω 条件を各段の点つき同型で移す。
規約：零次数を含む全基点 π_* 同型を使う。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot の BF 置換の入力。 -/
lemma totalizationKan_omegaCondition : (totalizationKan A).OmegaCondition := by
  apply KanSequence.changeLevels_omegaCondition
  exact KanSequence.homotopyLimit_omegaCondition _
    (fun i ↦ (((AsSmall.down ⋙ (GroupAction.diagramFunctor G).obj A).obj i)).toKanSequence_omega)

/-- 概要：通常の Tot の Kan Ω 列から hG の Kan end への厳密な比較射。
方針：各段の指定した密度の同型を構造可換射に束ねる。
規約：単射構造射の置換前の列の射。
使われ方：Goerss–Jardine VIII §§1–2、BF 1978 §2。hG と通常の Tot の比較。 -/
def totalizationKanComparison : KanSequence.Hom (totalizationKan A) (homotopyFixedPointsKan A) :=
  KanSequence.changeLevelsProjection _ _ _

/-- 概要：通常の Tot の Ω 列を単射構造射へ置換した BF 対象。
方針：本レーンの Kan Ω 列の cofibrant 置換を適用する。
規約：群の有限性を要求しない実際のスペクトル。
使われ方：BF 1978 §2、HA §1.4.2。通常の Tot の BF 模型。 -/
def totalizationSpectrum : OmegaSpectrum.{u} :=
  (totalizationKan A).cofibrantOmegaSpectrum (totalizationKan_omegaCondition A)

/-- 概要：通常の Tot の BF 模型から hG の Kan end への厳密な比較。
方針：単射置換の比較と段の同型による比較を合成する。
規約：hG の BF 模型との比較は同じ Kan end を介する。
使われ方：BF 1978 §2、HA §1.4.2。各段の π_* 同型による具体的な模型比較。 -/
def totalizationSpectrumComparison :
    KanSequence.Hom (totalizationSpectrum A).toKanSequence (homotopyFixedPointsKan A) :=
  (KanSequence.replacementProjection (totalizationKan A)).comp (totalizationKanComparison A)

/-- 概要：通常の Tot の BF 比較は各段で全基点 π_* 同型。
方針：単射置換の比較の同型性と密度の同型を合成する。
規約：零次数を含む。Sp の ∞ 極限性は含まない。
使われ方：BF 1978 §2、Goerss–Jardine I §7。hG の模型の置換への独立性。 -/
lemma totalizationSpectrumComparison_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((totalizationSpectrumComparison A).app n).right := by
  let e : ((totalizationKan A).level n).space.right ≅
      ((homotopyFixedPointsKan A).level n).space.right :=
    PointedSimplicialSet.forget.mapIso (totalizationLevelIso A n)
  exact (KanSequence.replacementProjection_piIsomorphism (totalizationKan A) n).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e)

end

end SerrePositivity.KST.Spectra.GroupActionCochains
