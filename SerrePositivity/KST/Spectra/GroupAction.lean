module

public import SerrePositivity.KST.Spectra.KanSequenceForgetful
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor
public import Mathlib.CategoryTheory.Action.Basic

/-!
概要：BF スペクトルの厳密な群作用と段・整数次数への作用。
方針：作用を通常の圏の End への準同型として与え、評価と π_* の関手で移す。
規約：作用の法則は厳密。homotopy fixed points の構成と ∞ 極限の比較は分ける。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。L9e の作用図式の入力。
-/

@[expose] public section

universe u v

open CategoryTheory

namespace SerrePositivity.KST.Spectra

/-- 概要：BF スペクトルの厳密な群作用の圏。
方針：既存の通常の圏の作用の定義を使う。
規約：群の有限性は構成では不要。
使われ方：BF 1978 §2、HA §1.4.2。hG の入力となる作用と同変射。 -/
abbrev GroupAction (G : Type v) [Group G] := Action OmegaSpectrum.{u} G

namespace GroupAction

noncomputable section

variable (G : Type v) [Group G]

/-- 概要：厳密な群作用を一対象の群圏上の実際の作用図式へ送る。
方針：作用と一対象圏の関手の標準の同値の順関手を使う。
規約：この図式の単なる厳密極限を hG と呼ばない。
使われ方：BF 1978 §2、HA §1.4.2。余単体置換の作用図式。 -/
def diagramFunctor : GroupAction.{u} G ⥤ (SingleObj G ⥤ OmegaSpectrum.{u}) :=
  Action.FunctorCategoryEquivalence.functor

/-- 概要：群作用を各段の点つき Kan 複体の作用へ評価する。
方針：段評価関手を作用の圏へ移す。
規約：各段の作用の法則も厳密。
使われ方：BF 1978 §2、HTT A.3.3。レベルごとの hG の入力。 -/
def levelFunctor (n : ℕ) : GroupAction.{u} G ⥤ Action PointedSimplicialSet.{u} G :=
  (OmegaSpectrum.levelEvaluation n).mapAction G

/-- 概要：群作用を単射性を忘れた Kan 列の作用へ移す。
方針：BF 忘却関手の作用への拡張を使う。
規約：各段と構造射の同変性を保持する。
使われ方：BF 1978 §2。Tot の後での単射置換を分離する。 -/
def kanSequenceFunctor : GroupAction.{u} G ⥤ Action KanSequence.{u} G :=
  OmegaSpectrum.forgetToKan.mapAction G

/-- 概要：群作用は全整数次数の可換ホモトピー群に作用する。
方針：実際の BF 射から構成した π_j の関手を作用の圏へ移す。
規約：整数次数の群は乗法記法。
使われ方：BF 1978 §2、HA §1.4.2。有理群コホモロジーに用いる係数の作用。 -/
def homotopyFunctor (j : ℤ) : GroupAction.{u} G ⥤ Action CommGrpCat.{u} G :=
  (OmegaSpectrum.homotopyFunctor j).mapAction G

end

end GroupAction

end SerrePositivity.KST.Spectra
