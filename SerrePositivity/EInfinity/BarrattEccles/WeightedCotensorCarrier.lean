module

public import SerrePositivity.EInfinity.BarrattEccles.WeightedCotensor
public import SerrePositivity.EInfinity.BarrattEccles.CotensorCarrier

/-!
# 小図式の重み付き右 frame の底の比較

概要：BM §1・Hovey §5.4 の小図式の重み付き end は同じ底の複体の end で計算する。
方針：忘却の反対関手による重み付き実現の Kan 拡張保存を使う。
規約：任意の小図式・単体的重み、元の右 frame をそのまま使う。
使われ方：一般 homotopy 極限の候補の忘却後の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：小図式の選んだ右 frame を同じ底の複体図式へ移す（BM §1）。
方針：frame の各成分を反対忘却で後合成する。
規約：添字圏・全単体作用素・全図式射を保持する。
使われ方：底の複体に値を取る重み付き end の係数。 -/
def carrierRightFrameDiagram (F : K ⥤ (operad A).Algebra) :
    Kᵒᵖ ⥤ SimplexCategory ⥤ (Complex A)ᵒᵖ :=
  rightFrameDiagram A K F ⋙
    (Functor.whiskeringRight SimplexCategory _ _).obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).op

/-- 概要：同じ右 frame の底で計算する小図式の重み付き end（BM §1、Hovey §5.4）。
方針：複体の反対圏で重み付き実現を取り、反転する。
規約：重みの cofibrancy や単体集合のモデル構造は存在には不要。
使われ方：E 代数の重み付き end の実際の底の対象。 -/
def carrierWeightedCotensor (F : K ⥤ (operad A).Algebra) :
    (K ⥤ SSet.{u})ᵒᵖ ⥤ Complex A :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K ⋙
    FrameWeightRealization.functor Kᵒᵖ (carrierRightFrameDiagram A K F)).leftOp

/-- 概要：重み付き E 代数の end の底は同じ複体の end（BM §1、Hovey §5.4）。
方針：積添字の Yoneda に沿う左 Kan 拡張の保存同型を反対化する。
規約：任意の小図式と任意の単体的重み、置換は再選択しない。
使われ方：一般 homotopy 極限候補の底の計算。 -/
def weightedCotensorCarrierIso (F : K ⥤ (operad A).Algebra) (W : K ⥤ SSet.{u}) :
    ((weightedCotensor A K F).obj (op W)).carrier ≅
      (carrierWeightedCotensor A K F).obj (op W) := by
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)
  have : U.IsRightAdjoint := (operad A).freeAlgebraAdjunction.isRightAdjoint
  exact ((U.op.leftKanExtensionCompIsoOfPreserves
    (FrameWeightRealization.source Kᵒᵖ (rightFrameDiagram A K F))
    uliftYoneda.{u,u,u}).app
      ((FrameWeightRealization.weightsEquivalence Kᵒᵖ).functor.obj
        ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W))).unop.symm

end SerrePositivity.EInfinity.BarrattEccles
