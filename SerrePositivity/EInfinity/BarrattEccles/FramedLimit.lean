module

public import SerrePositivity.EInfinity.BarrattEccles.WeightedCotensorCarrier
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointReplacement
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
# Cofibrant な一点重みの右 frame の end の関手

概要：Hovey §5.4 の一般 homotopy 極限の計算対象を小図式全体に関手的に構成する。
方針：関手的右 frame と実際の Yoneda の左 Kan 拡張を指定した重みで評価する。
規約：対象と射を構成する。ホモトピー不変性・右導来極限の普遍性は別に証明する。
使われ方：E2a-4 の一般 homotopy 極限の計算モデル。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]


/-- 概要：元の小図式を反対圏の右 frame の図式へ関手的に移す（Hovey §5.2）。
方針：図式圏の反対化と関手的右 frame の後合成を使う。
規約：図式射の合成を厳密に保つ。
使われ方：重み付き実現の係数に関する自然性。 -/
def rightFrameDiagramFamily :
    (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ Kᵒᵖ ⥤ SimplexCategory ⥤ (operad A).Algebraᵒᵖ := by
  let := modelCategory A
  exact (Functor.opUnopEquiv K (operad A).Algebra).functor ⋙
    (Functor.whiskeringRight Kᵒᵖ _ _).obj (rightFrameFamily A).obj

/-- 概要：反対圏での重み付き右 frame の end の関手（Hovey §5.4）。
方針：図式の反対化・右 frame・随伴で自然な重み付き実現・重みでの評価を合成する。
規約：すべての操作は厳密な関手で、各対象ごとの選択から自然性を仮定しない。
使われ方：元の E 代数圏に値を取る計算関手の構成。 -/
def framedLimitOpFunctor : (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ (operad A).Algebraᵒᵖ := by
  exact rightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ ⋙
    (CategoryTheory.evaluation _ (operad A).Algebraᵒᵖ).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)

/-- 概要：小図式の射影 cofibrant な一点重みの右 frame の end の関手（Hovey §5.4）。
方針：反対圏で構成した関手を unop する。
規約：任意の小図式と全図式射、単体集合のモデル存在の仮定なし。
使われ方：一般 homotopy 極限の導来普遍性を証明する元の計算関手。 -/
def framedLimitFunctor : (K ⥤ (operad A).Algebra) ⥤ (operad A).Algebra :=
  (framedLimitOpFunctor A K).unop

/-- 概要：計算関手の各値は選んだ重みの実際の右 frame の end（Hovey §5.4）。
方針：合成関手の対象の式を評価する。
規約：重みや frame の置換を選び直さない。
使われ方：構成済みの重み付き Hom と底の比較を計算関手へ移す。 -/
lemma framedLimitFunctor_obj (F : K ⥤ (operad A).Algebra) :
    (framedLimitFunctor A K).obj F =
      (weightedCotensor A K F).obj (op (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)) := rfl

/-- 概要：計算関手の底は同じ重みと frame の複体の end（BM §1、Hovey §5.4）。
方針：一般の重み付き end の底の比較を選んだ一点重みで評価する。
規約：元の図式の底の複体で計算する。
使われ方：一般 homotopy 極限の忘却後の計算同型の対象。 -/
def framedLimitCarrierIso (F : K ⥤ (operad A).Algebra) :
    ((framedLimitFunctor A K).obj F).carrier ≅
      (carrierWeightedCotensor A K F).obj (op (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)) :=
  weightedCotensorCarrierIso A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)

end SerrePositivity.EInfinity.BarrattEccles
