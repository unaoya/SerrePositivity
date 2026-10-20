module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramModel
public import SerrePositivity.EInfinity.BarrattEccles.DiagramForget

/-!
# 図式忘却と具体的な複体図式モデルの照合

概要：BM 命題 4.1・Hovey §2.3 の図式忘却を底の具体的な射影モデルへ接続する。
方針：頂点ごとの擬同型と全次数全射の同じクラスを照合する。
規約：既存の図式忘却と元の複体図式を保持する。
使われ方：導来忘却による一般 homotopy 極限の比較。
-/

@[expose] public section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.Diagram

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：底の図式モデルの弱同値は既存の頂点ごとの擬同型（Hovey §2.3）。
方針：具体的なモデルの弱同値フィールドを評価する。
規約：導来図式忘却の元の反転クラスと厳密に同じ。
使われ方：既存の局所化関手を具体的な図式モデルで使う。 -/
lemma carrierModelCategory_weakEquivalences :
    @weakEquivalences (K ⥤ Complex A) _
      (CarrierDiagram.projectiveModelCategory A K).categoryWithWeakEquivalences =
        objectwiseQuasiIsos A K := rfl

/-- 概要：図式忘却は具体的な両射影モデルに対して右 Quillen（BM 命題 4.1）。
方針：元の二つの右類の頂点ごとの定義を使う。
規約：両モデルは局所的に選び、元の図式に cofibrancy は要求しない。
使われ方：底への導来図式忘却と極限の比較。 -/
lemma forget_isRightQuillen :
    let := projectiveModelCategory A K
    let := CarrierDiagram.projectiveModelCategory A K
    SerrePositivity.Quillen.IsRightQuillen (forget A K) := by
  let := projectiveModelCategory A K
  let := CarrierDiagram.projectiveModelCategory A K
  constructor
  · intro F G f hf
    exact hf
  · intro F G f hf
    exact hf

end SerrePositivity.EInfinity.BarrattEccles.Diagram
