module
public import SerrePositivity.KST.SConstruction.CofiberUnitPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

/-! # 四角形の対角から上辺・右辺への二つの三角形 prism
概要：対角辺を上辺または右辺へ動かし、終点を固定した比較を作る。
方針：区間の二座標の max を一方の成分に入れる。
規約：false は上辺、true は右辺。使われ方：切断の下辺の coherent な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 四角形の対角辺。 -/
def arrowSquareDiagonal : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] := lift (𝟙 _) (𝟙 _)

/-- 対角を上辺または右辺へ動かす、時刻を第一因子とした prism。 -/
def arrowTrianglePrism (b : Bool) : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  if b then lift intervalMax (snd _ _) else lift (snd _ _) intervalMax

/-- 三角形 prism の時刻零は対角辺。 -/
lemma arrowTrianglePrism_zero (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ arrowTrianglePrism b = arrowSquareDiagonal := by
  cases b <;> apply SSet.yonedaEquiv.injective <;> apply Prod.ext <;>
    apply stdSimplex.ext <;> intro r <;> fin_cases r <;> rfl

/-- 三角形 prism の時刻一は上辺または右辺。 -/
lemma arrowTrianglePrism_one (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ arrowTrianglePrism b =
      (if b then _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge else _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge) := by
  cases b <;> apply SSet.yonedaEquiv.injective <;> apply Prod.ext <;>
    apply stdSimplex.ext <;> intro r <;> fin_cases r <;> rfl

/-- 三角形 prism の始点での辺は元の左辺または下辺。 -/
lemma arrowTrianglePrism_source (b : Bool) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        arrowTrianglePrism b = (if b then _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge else _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) := by
  cases b <;> apply SSet.yonedaEquiv.injective <;> apply Prod.ext <;>
    apply stdSimplex.ext <;> intro r <;> fin_cases r <;> rfl

/-- 三角形 prism の終点での辺は右上角に定値。 -/
lemma arrowTrianglePrism_target (b : Bool) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        arrowTrianglePrism b =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  cases b <;> apply SSet.yonedaEquiv.injective <;> apply Prod.ext <;>
    apply stdSimplex.ext <;> intro r <;> fin_cases r <;> rfl

end SerrePositivity.KST.SConstruction
