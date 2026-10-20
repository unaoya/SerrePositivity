module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackConeComparisonNaturality
public import SerrePositivity.InfinityCategories.F2.KanConeConstantDiagramEdges
public import SerrePositivity.InfinityCategories.F2.KanConeConstantDiagramComparison

/-!
概要：元の全空間錐比較の定値な図式辺・対角・図式比較の厳密な簡約。
方針：元の図式円柱の定値性を零・一次・二次で評価する。
規約：指定比較の値を保持。使われ方：元の二射影・path との最終照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：元の図式成分は元の値の恒等射。
方針：定値な円柱の頂点。規約：射の等式。使われ方：脚の比較の始域の簡約。 -/
lemma fiberwisePullbackConeDiagramComponent_eq_id (i : AsSmall.{u} WalkingCospan) :
    kanConeDiagramComponent (fiberwisePullbackNativeConeHomotopy p f g) i =
      𝟙 ((kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).obj i) :=
  kanConeDiagramComponent_eq_id (fiberwisePullbackNativeConeHomotopy p f g)
    (fiberwisePullbackNativeConeHomotopy_diagram p f g) i

/-- 概要：元の図式対角は元の図式射。
方針：定値な円柱の辺。規約：射の等式。使われ方：指定共有面の簡約。 -/
lemma fiberwisePullbackConeDiagramDiagonal_eq_map
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    kanConeDiagramDiagonal (fiberwisePullbackNativeConeHomotopy p f g) a =
      (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a :=
  kanConeDiagramDiagonal_eq_map (fiberwisePullbackNativeConeHomotopy p f g)
    (fiberwisePullbackNativeConeHomotopy_diagram p f g) a

/-- 概要：図式側の指定二次比較は等式から来る同型。
方針：元の二単体の精密化の定値性。規約：指定値。使われ方：二次の整合式の簡約。 -/
lemma fiberwisePullbackConeDiagramComparisonIso_isFunctorEqIso
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramComparisonIso (fiberwisePullbackNativeConeHomotopy p f g) a) :=
  kanConeDiagramComparisonIso_isFunctorEqIso (fiberwisePullbackNativeConeHomotopy p f g)
    (fiberwisePullbackNativeConeHomotopy_diagram p f g) a

/-- 概要：各脚の元の指定比較を恒等図式成分を消した同じ頂点間の同型にする。
方針：成分の厳密な恒等性だけで端点を輸送。
規約：元の上下三角形の値を保持。使われ方：元の具体的な二射影との整合。 -/
def fiberwisePullbackConeLegIso (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g i)
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i) :=
  functorIsoOfEq (fiberwisePullbackConeLegComparisonIso p f g i) (by
    rw [fiberwisePullbackConeDiagramComponent_eq_id]
    exact Category.comp_id _) rfl

/-- 概要：恒等成分の消去は元の指定比較の値を保持する。
方針：端点の輸送。規約：型付きの一致。使われ方：指定三角形の最終整合。 -/
lemma fiberwisePullbackConeLegIso_heq (i : AsSmall.{u} WalkingCospan) :
    HEq (fiberwisePullbackConeLegIso p f g i) (fiberwisePullbackConeLegComparisonIso p f g i) :=
  functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
