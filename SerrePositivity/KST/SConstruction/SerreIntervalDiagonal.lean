module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaps
public import SerrePositivity.DifferentialGraded.Complexes.Braiding

/-! # 元の鎖区間の Serre 対角
概要：零頂点をその二重 tensor、辺を zero⊗edge+edge⊗one に送る chain map を作る。
方針：元の disk 生成元の普遍性で対角を作り、同じ生成元で評価を回収する。
規約：辺の向きと tensor の因子順を保持する。使われ方：cubical dg nerve の tensor 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- Serre 対角の元の辺の像。 -/
def serreIntervalDiagonalEdge : (serreInterval A ⊗ serreInterval A).X (-1) :=
  ιTensorObj (serreInterval A) (serreInterval A) 0 (-1) (-1) (by omega)
      ((cycleFromUnit _ (serreIntervalZero A)).val ⊗ₜ[A] serreIntervalEdge A) +
    ιTensorObj (serreInterval A) (serreInterval A) (-1) 0 (-1) (by omega)
      (serreIntervalEdge A ⊗ₜ[A] (cycleFromUnit _ (serreIntervalOne A)).val)

/-- 元の鎖区間上の Serre 対角 chain map。 -/
def serreIntervalDiagonal : serreInterval A ⟶ serreInterval A ⊗ serreInterval A :=
  serreIntervalLift A ((λ_ (𝟙_ (Complex A))).inv ≫
    (serreIntervalZero A ⊗ₘ serreIntervalZero A)) (serreIntervalDiagonalEdge A)

/-- Serre 対角は元の零頂点をその二重 tensor へ写す。 -/
lemma serreIntervalDiagonal_zero :
    serreIntervalZero A ≫ serreIntervalDiagonal A =
      (λ_ (𝟙_ (Complex A))).inv ≫ (serreIntervalZero A ⊗ₘ serreIntervalZero A) :=
  serreIntervalLift_zero A _ _

/-- Serre 対角は元の辺を zero⊗edge+edge⊗one へ写す。 -/
lemma serreIntervalDiagonal_edge :
    (serreIntervalDiagonal A).f (-1) (serreIntervalEdge A) = serreIntervalDiagonalEdge A :=
  serreIntervalLift_edge A _ _

end SerrePositivity.KST.SConstruction
