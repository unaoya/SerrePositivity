module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackFiberIso
public import SerrePositivity.InfinityCategories.F2.FiberwiseIntervalPullbackLifting
public import SerrePositivity.InfinityCategories.F2.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanLimits

/-!
概要：元の三値の path 引き戻しを元の全空間の Kan 模型へ入れる実際の値射。
方針：厳密な fiber 同型の逆、fiber の包含、元の Kan 置換の単位を合成する。
規約：元の三座標を選び直さない。
使われ方：一般 coherent な引き戻しの有限射と境界を元の値で検出する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の三値の path 引き戻しから全空間への実際の射。
方針：構成した fiber 同型の逆を元の fiber の包含と合成する。
規約：元の底の頂点。使われ方：相対有限検出の値の包含。 -/
def fiberwisePullbackValueToTotal {E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌) :
    intervalPullback (vertexFiberMap (f ≫ p) p f rfl b) (vertexFiberMap (g ≫ p) p g rfl b) ⟶
      fiberwiseIntervalPullback p f g :=
  (fiberwisePullbackFiberIso p f g b).inv ≫
    vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b

/-- 概要：元の三つの全空間が left fibration なら値の path 引き戻しは Kan。
方針：全空間の left fibration の fiber の Kan 性を厳密な同型で移す。
規約：底の充填性は不要。使われ方：検出した有限ホモトピーを元の値に戻す。 -/
instance fiberwisePullbackValue_kanComplex {E D H B : SSet.{u}}
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (b : B _⦋0⦌) :
    KanComplex (intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b)) := by
  have := vertexFiber_kanComplex_of_leftFibration (fiberwiseIntervalPullbackProjection p f g) b
  exact HomotopyLimits.kanComplex_of_iso (fiberwisePullbackFiberIso p f g b)

end SerrePositivity.InfinityCategories.F2
