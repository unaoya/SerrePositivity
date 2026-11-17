module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.DoubleOpposite
public import SerrePositivity.EInfinity.ComplexLimits.RightFrames
public import SerrePositivity.EInfinity.BarrattEccles.CotensorCarrier
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization

/-!
# 小図式の右 frame の重み付き end

概要：Hovey §5.4 の右 frame から任意の小図式と単体的重みの実際の対象を構成する。
方針：反対圏の重み付き実現を反転し、射の普遍性を随伴で表す。
規約：重みの cofibrancy は対象の存在には不要。一般 homotopy 極限性は別に証明する。
使われ方：E2a-4 の一般 homotopy 極限の計算対象。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：複体図式のすべての値に同じ関手的右 frame を適用する（Hovey §5.2）。
方針：反対化した図式へ関手的な frame の族を後合成する。
規約：元の図式のすべての射と合成を保持する。
使われ方：重み付き end の係数となる余単体的な反対図式。 -/
def rightFrameDiagram (F : K ⥤ (Complex A)) :
    Kᵒᵖ ⥤ SimplexCategory ⥤ (Complex A)ᵒᵖ := by
  let := projectiveModelCategory A
  exact F.op ⋙ (rightFrameFamily A).obj


/-- 概要：小さい 複体図式の重み付き右 frame の end（Hovey §5.4）。
方針：元の重みを二重反対化し、反対圏の重み付き実現を反転する。
規約：任意の単体的重み、重みの射に反変、値は元の 複体。
使われ方：一般 homotopy 極限の具体的な計算対象を供給する。 -/
def weightedCotensor (F : K ⥤ (Complex A)) :
    (K ⥤ SSet.{u})ᵒᵖ ⥤ (Complex A) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K ⋙
    FrameWeightRealization.functor Kᵒᵖ (rightFrameDiagram A K F)).leftOp

/-- 概要：重み付き end への射は右 frame への重み付き錐に一致する（Hovey §5.4）。
方針：反対圏の Hom の同値と重み付き実現の実際の随伴を使う。
規約：錐は実際の単体集合の図式間の自然変換として記述する。
使われ方：homotopy 極限の普遍性と底の複体での比較。 -/
def weightedCotensorHomEquiv (F : K ⥤ (Complex A))
    (W : K ⥤ SSet.{u}) (Y : (Complex A)) :
    (Y ⟶ (weightedCotensor A K F).obj (op W)) ≃
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W ⟶
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj (op Y)) :=
  (show (Y ⟶ (weightedCotensor A K F).obj (op W)) ≃
      ((FrameWeightRealization.functor Kᵒᵖ (rightFrameDiagram A K F)).obj
        ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W) ⟶ op Y) from
    { toFun := fun f => f.op
      invFun := fun f => f.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    ((FrameWeightRealization.adjunction Kᵒᵖ (rightFrameDiagram A K F)).homEquiv
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W) (op Y))

end SerrePositivity.EInfinity.ComplexLimits
