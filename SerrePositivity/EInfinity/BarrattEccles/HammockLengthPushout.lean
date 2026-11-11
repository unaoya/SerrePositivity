module

public import SerrePositivity.EInfinity.BarrattEccles.HammockLengthBoundary
public import SerrePositivity.EInfinity.Hammock.LengthStagePushout

/-!
# 任意の可換環上の元の長さ段階の pushout

概要：実際の E 代数の次段階は、元の境界に沿った二つの最大交互語の貼り合わせである。
方針：実際の graph 図式の proper 性を、元の標準射の pushout の普遍性へ代入する。
規約：モデル構造等を追加の入力にはしない。弱同値不変性は後続。
使われ方：元の三列の標準射の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

def algebraHammockStageBoundarySum (n : ℕ) : SSet.{u + 1} :=
  Hammock.stageBoundarySum (algebraHammockGraphDiagram A X Y) n

def algebraHammockStageTopSum (n : ℕ) : SSet.{u + 1} :=
  Hammock.stageTopSum (algebraHammockGraphDiagram A X Y) n

def algebraHammockStageBoundarySumInclusion (n : ℕ) :
    algebraHammockStageBoundarySum A X Y n ⟶ algebraHammockStageTopSum A X Y n :=
  Hammock.stageBoundarySumInclusion (algebraHammockGraphDiagram A X Y) n

def algebraHammockStageBoundaryAttach (n : ℕ) :
    algebraHammockStageBoundarySum A X Y n ⟶ algebraHammockLengthStage A X Y n :=
  Hammock.stageBoundaryAttach n (algebraHammockGraphDiagram_proper A X Y)

def algebraHammockStageTopInclusion (n : ℕ) :
    algebraHammockStageTopSum A X Y n ⟶ algebraHammockLengthStage A X Y (n + 1) :=
  Hammock.stageTopInclusion (algebraHammockGraphDiagram A X Y) n

lemma algebraHammockStageBoundaryAttach_fac (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n =>
      (algebraHammockLengthBoundary A X Y n a.val).toFunctor) a ≫
        algebraHammockStageBoundaryAttach A X Y n =
      algebraHammockLengthBoundaryToStage A X Y n a.val :=
  Hammock.stageBoundaryAttach_fac n (algebraHammockGraphDiagram_proper A X Y) a

lemma algebraHammockStageTopInclusion_fac (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => algebraHammockGraph A a.val X Y) a ≫
        algebraHammockStageTopInclusion A X Y n =
      algebraHammockLengthStageInclusion A X Y (n + 1) a.val a.property.1.le :=
  Hammock.stageTopInclusion_fac (algebraHammockGraphDiagram A X Y) n a

/-- 元の前段階・二つの最大交互語・境界による、実際の次段階の pushout。 -/
lemma algebraHammockLengthStage_isPushout (n : ℕ) :
    IsPushout (algebraHammockStageBoundaryAttach A X Y n)
      (algebraHammockStageBoundarySumInclusion A X Y n)
      (algebraHammockLengthTransition A X Y (Nat.le_succ n))
      (algebraHammockStageTopInclusion A X Y n) :=
  Hammock.lengthStage_isPushout n (algebraHammockGraphDiagram_proper A X Y)

end SerrePositivity.EInfinity.BarrattEccles
