module

public import SerrePositivity.KST.Spectra.GroupAction
public import SerrePositivity.KST.Spectra.PointedHomotopyLimit
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
概要：群作用の hG と余単体対象の homotopy Tot のレベルごとの点つき Kan 複体。
方針：実際の作用図式と余単体図式に点つき Bousfield–Kan end を段ごとに適用する。
規約：この段階ではレベルごとの構成だけ。BF 構造射と ∞ 極限性は同時に主張しない。
使われ方：BF 1978 §2、HA §1.4.2、Kerodon 7.5.4.6（Tag 03BB）。L9e の対象の実構成の出発点。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：スペクトルの群作用の n 段の homotopy fixed points。
方針：一対象の群圏上の実際の作用図式を段評価し、その点つき Kan end を取る。
規約：通常の fixed points の厳密な極限とは区別する。
使われ方：BF 1978 §2、HA §1.4.2。hG のレベルごとの対象。 -/
def homotopyFixedLevel {G : Type u} [Group G] (A : GroupAction.{u} G) (n : ℕ) :
    PointedSimplicialSet.{u} :=
  PointedHomotopyLimit.obj
    (AsSmall.down ⋙ ((GroupAction.diagramFunctor G).obj A) ⋙ OmegaSpectrum.levelEvaluation n)

/-- 概要：hG の各段は Kan 複体。
方針：作用図式の各値は元の同じ Kan 段であり、点つき end のホーン充填を使う。
規約：有限群でなくても成立する。
使われ方：BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB）。hG の Kan 列の構成。 -/
instance homotopyFixedLevel_kanComplex {G : Type u} [Group G] (A : GroupAction.{u} G) (n : ℕ) :
    KanComplex (homotopyFixedLevel A n).right := by
  let : ∀ i, KanComplex
      (((AsSmall.down ⋙ ((GroupAction.diagramFunctor G).obj A) ⋙
        OmegaSpectrum.levelEvaluation n).obj i).right) :=
    fun _ ↦ inferInstanceAs (KanComplex (A.V.level n).space.right)
  exact PointedHomotopyLimit.kanComplex _

/-- 概要：同変な BF 射は hG の各段の実際の点つき射を誘導する。
方針：作用図式の自然変換を段評価して end の関手へ渡す。
規約：射は全て厳密な点つき射。
使われ方：BF 1978 §2、HA §1.4.2。hG のレベルごとの関手性。 -/
def homotopyFixedLevelMap {G : Type u} [Group G] {A B : GroupAction.{u} G}
    (f : A ⟶ B) (n : ℕ) : homotopyFixedLevel A n ⟶ homotopyFixedLevel B n :=
  PointedHomotopyLimit.map (Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down ((GroupAction.diagramFunctor G).map f))
    (OmegaSpectrum.levelEvaluation n))

/-- 概要：余単体 BF 対象の homotopy totalization の n 段。
方針：AsSmall で添字圏の宇宙を揃え、段評価の点つき Bousfield–Kan end を取る。
規約：Reedy 充填を使う通常の Tot との比較は別に扱う。
使われ方：BF 1978 §2、HA §1.4.2、Kerodon 7.5.4.6（Tag 03BB）。余単体対象のレベルごとの Kan 模型。 -/
def homotopyTotalizationLevel (X : CosimplicialObject OmegaSpectrum.{u}) (n : ℕ) :
    PointedSimplicialSet.{u} :=
  PointedHomotopyLimit.obj (AsSmall.down ⋙ X ⋙ OmegaSpectrum.levelEvaluation n)

/-- 概要：homotopy totalization の各段は Kan。
方針：全ての余単体次数の段が Kan であることを end の Kan 性へ渡す。
規約：一般の厳密極限が Kan であるとは主張しない。
使われ方：BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB）。Tot の Kan 列のレベル。 -/
instance homotopyTotalizationLevel_kanComplex (X : CosimplicialObject OmegaSpectrum.{u}) (n : ℕ) :
    KanComplex (homotopyTotalizationLevel X n).right := by
  let : ∀ i, KanComplex
      (((AsSmall.down ⋙ X ⋙ OmegaSpectrum.levelEvaluation n).obj i).right) :=
    fun i ↦ inferInstanceAs (KanComplex ((X.obj (AsSmall.down.obj i)).level n).space.right)
  exact PointedHomotopyLimit.kanComplex _

/-- 概要：余単体 BF 対象の射は homotopy totalization の各段に作用する。
方針：AsSmall の忘却を前合成し、段評価して end の関手に送る。
規約：通常の余単体対象の自然変換を入力とする。
使われ方：BF 1978 §2、HA §1.4.2。Tot のレベルごとの射。 -/
def homotopyTotalizationLevelMap {X Y : CosimplicialObject OmegaSpectrum.{u}}
    (f : X ⟶ Y) (n : ℕ) : homotopyTotalizationLevel X n ⟶ homotopyTotalizationLevel Y n :=
  PointedHomotopyLimit.map (Functor.whiskerRight (Functor.whiskerLeft AsSmall.down f)
    (OmegaSpectrum.levelEvaluation n))

end

end SerrePositivity.KST.Spectra
