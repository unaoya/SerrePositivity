module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementColumn
/-! 概要：持ち上げた自由列と両自然変換から元の列を厳密に回収する。
方針：Hom の ULift と cofibrant 包含を同じ射の定義に戻す。
規約：全要素圏と元の augmentation・評価を保持する。
使われ方：全族 roof の忘却像と元の単位公式の照合。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：相対列の包含像は元の自由列。
方針：両持ち上げを展開する。規約：全射を保持。
使われ方：全パラメータの通常図式比較。 -/
lemma freeProbeRelativeElementColumn_comp_inclusion :
    freeProbeRelativeElementColumn A X B ⋙ cofibrantAlgebraDKInclusion A =
      ULiftHom.down.{u, u + 1, u + 1} ⋙ freeProbeElementColumn A X B.obj := rfl

/-- 概要：相対 augmentation は包含で元の成分へ戻る。
方針：Hom の ULift を戻す。規約：元の全要素を保持。
使われ方：元の単位と augmentation の比較。 -/
lemma freeProbeRelativeElementAugmentation_inclusion (s : freeProbeRelativeElementIndex A X B) :
    (cofibrantAlgebraDKInclusion A).map ((freeProbeRelativeElementAugmentation A X B).app s) =
      (freeProbeElementColumnAugmentation A X B.obj).app
        (ULiftHom.objDown.{u + 1, u + 1} s) := rfl

/-- 概要：相対評価は包含で元の評価成分へ戻る。
方針：Hom の ULift を戻す。規約：同じ評価射を保持。
使われ方：元の随伴単位と評価の比較。 -/
lemma freeProbeRelativeElementEvaluation_inclusion (s : freeProbeRelativeElementIndex A X B) :
    (cofibrantAlgebraDKInclusion A).map ((freeProbeRelativeElementEvaluation A X B).app s) =
      (freeProbeElementColumnEvaluation A X B.obj).app
        (ULiftHom.objDown.{u + 1, u + 1} s) := rfl

end SerrePositivity.EInfinity.BarrattEccles
