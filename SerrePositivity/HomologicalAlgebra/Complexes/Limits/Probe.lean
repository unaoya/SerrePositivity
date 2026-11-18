module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitProbe

/-!
# 全複体図式の極限計算に使う同じ試験始域

概要：Hovey §2.3・§5 の複体の具体的な cofibrant 置換を再利用する。
方針：既存の同じ分解・試験始域・比較射を名前に束ねる。
規約：元の複体の cofibrancy は仮定しない。
使われ方：底の計算対象との比較で試験始域を共有する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：試験始域の同じ生成分解（Hovey §2.3）。
方針：既存の複体の I・J 分解を再利用する。
規約：分解を再選択しない。
使われ方：始域 frame の構成。 -/
abbrev mappingCofibrantFactorization := _root_.SerrePositivity.EInfinity.BarrattEccles.carrierProbeFactorization A

/-- 概要：同じ複体の試験始域（Hovey §5）。
方針：既存の cofibrant 置換関手の値を使う。
規約：底の比較と同じ対象。
使われ方：右 frame の錐。 -/
abbrev framedLimitProbe := _root_.SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbe A

/-- 概要：同じ試験始域から元の複体への比較（Hovey §5）。
方針：元の比較自然変換を評価する。
規約：元の複体射を保持する。
使われ方：局所化後の置換の相殺。 -/
abbrev framedLimitProbeComparison (Y : Complex A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbeComparison A).app Y

/-- 概要：同じ試験始域は cofibrant（Hovey §2.3）。
方針：既存の具体的な分解の保証を使う。
規約：元の複体に条件を付けない。
使われ方：反対終域の fibrancy。 -/
lemma framedLimitProbe_cofibrant (Y : Complex A) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    IsCofibrant (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbe_cofibrant A Y

/-- 概要：同じ試験始域比較は擬同型（Hovey §2.3）。
方針：元の自明 fibration の保証を使う。
規約：元の比較射そのもの。
使われ方：局所化での反転。 -/
lemma framedLimitProbeComparison_quasiIso (Y : Complex A) :
    QuasiIso (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbeComparison_quasiIso A Y

end SerrePositivity.ComplexLimits
