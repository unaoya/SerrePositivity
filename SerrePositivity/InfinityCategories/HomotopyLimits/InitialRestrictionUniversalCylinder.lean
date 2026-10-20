module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionSectionComparison
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.InitialEvaluationHomotopyTriangle

/-!
概要：普遍前置の始点へ至る評価固定の円柱と、その Hom への射影を構成する。
方針：前置写像の厳密な評価式から始対象の切断と比較し、既存の Hom 前合成へ射影する。
規約：底の同じ前置写像を使う。使われ方：元の HL・HR と同じ射の類の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
  (hc : IsInitialVertex c)
local notation "Φ" => initialRestrictionTotalPrecomposition p q r hr d e y
local notation "L" => leftFibrationInitialSection p d hd y ≫ Φ
local notation "R" => vertexFiberMap p q r hr y
local notation "P" => leftFibrationInitialProjection q c y ≫
  Iso.hom (leftFibrationInitialBaseIso q c y)

/-- 普遍前置の始点を、元の制限と同じ全族の評価を全時刻固定して結ぶデータ。 -/
def initialRestrictionUniversalCylinderData : InitialEvaluationCylinder q c y R hc L :=
  initialEvaluationCylinder q c y R hc L (by
    rw [Category.assoc, initialRestrictionTotalPrecomposition_evaluation,
      ← Category.assoc (leftFibrationInitialSection p d hd y)
        (leftFibrationInitialEvaluation p d y),
      leftFibrationInitialSection_evaluation, Category.id_comp])
local notation "U" => initialRestrictionUniversalCylinderData p q r hr d hd e y hc

/-- 同じ普遍前置の始点へ至る円柱を、既存の Hom 前合成の表示へ射影する。 -/
def initialRestrictionUniversalHomCylinder : SSet.Homotopy
    (R ≫ leftFibrationInitialHomComparison q c hc y)
    (leftFibrationInitialHomComparison p d hd y ≫
      initialRestrictionHomPrecomposition p q r hr d e y) :=
  homotopyEndpointTransport (functorHomotopyPostcomp (U).homotopy P)
    (by simp only [leftFibrationInitialHomComparison, Category.assoc])
    ((Category.assoc (leftFibrationInitialSection p d hd y) Φ P).trans
      ((congrArg (leftFibrationInitialSection p d hd y ≫ ·)
        (initialRestrictionTotalPrecomposition_pinched p q r hr d e y)).trans
          (by simp only [leftFibrationInitialHomComparison, Category.assoc])))

/-- Hom への円柱の射影は、同じ普遍前置を使った中間円柱の raw な像である。 -/
lemma initialRestrictionUniversalHomCylinder_projection :
    (initialRestrictionUniversalHomCylinder p q r hr d hd e y hc).h = (U).homotopy.h ≫ P :=
  homotopyEndpointTransport_raw _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
