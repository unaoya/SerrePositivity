module

public import SerrePositivity.KST.Descent.WeightedCechDerivedFubini
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-!
# Čech の反復計算に使う射影的 fibrancy

## 概要
射影的図式の fibrancy と各成分の fibrancy を比較し、重みつき錐関手への適用を準備する。

## 方針
評価の右 Quillen 性と、終対象への射の点ごとの fibration の判定を使う。

## 規約
右クラスの点ごとの判定だけを使い、cofibration への同じ主張はしない。

## 使われ方
論文 補題 3.2・3.3 の独立な行・外側の fibrant 置換による導来 Fubini。
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

/-- 概要：実際の射影的図式は各成分が fibrant であることと同値（補題 3.2）。
方針：順方向は右 Quillen 評価、逆方向は終対象への各成分の fibration を使う。
規約：任意の生成された模型に適用する。使われ方：反復重みつき錐への fibrancy の供給。 -/
theorem cechDiagram_isFibrant_iff (F : K ⥤ C) :
    let := Projective.modelCategory K I J
    IsFibrant F ↔ ∀ k, IsFibrant (F.obj k) := by
  let := Projective.modelCategory K I J
  constructor
  · intro hF k
    have := hF
    have := Projective.evaluation_isRightQuillen K I J k
    have : (Projective.evaluation K (C := C) k).IsRightAdjoint :=
      (Projective.adjunction K k).isRightAdjoint
    exact Quillen.isFibrant_obj (Projective.evaluation K k) F
  · intro hF
    apply (isFibrant_iff F).mpr
    apply (Projective.fibration_iff_objectwise K I J _).mpr
    intro k
    exact (isFibrant_iff_of_isTerminal ((terminal.from F).app k)
      (terminalIsTerminal.isTerminalObj ((CategoryTheory.evaluation K C).obj k) _)).mp (hF k)

end SerrePositivity.KST.Descent
