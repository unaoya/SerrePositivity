module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanNativeConeTriangle

/-!
概要：全空間引き戻し錐の指定三角形と、同じ円柱の上下の比較ホモトピー。
方針：元の比較辺と恒等図式辺を一般の Kan 錐の読み戻しへ入力する。
規約：存在命題から代表を選び直さない。使われ方：元の指定 path との二次の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：全空間の native 錐の元の二単体の指定ホモトピー。
方針：錐の三角形をそのまま読み戻す。規約：元の形状射。使われ方：二次の可換性。 -/
def fiberwisePullbackNativeConeTriangleHomotopy
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    SSet.Homotopy (fiberwisePullbackNativeConeKanLeg p f g j)
      (fiberwisePullbackNativeConeKanLeg p f g i ≫
        (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a) :=
  kanNativeConeTriangleHomotopy (fiberwisePullbackNativeCone p f g) _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _)) a

/-- 概要：全錐比較の元の対角辺を Kan 射にする。
方針：指定円柱の対角を読み戻す。規約：全一単体を保持。使われ方：上下の共通対角。 -/
def fiberwisePullbackNativeConeDiagonal (i : AsSmall.{u} WalkingCospan) :
    fiberwisePullbackTotalKanObject p f g ⟶
      (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).obj i :=
  kanConeHomotopyDiagonal (fiberwisePullbackNativeConeHomotopy p f g) _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _)) i

/-- 概要：下側の指定三角形は共通対角と元の native な脚を結ぶ。
方針：元の図式辺の恒等性を使う。規約：円柱の代表は元のまま。使われ方：脚の指定比較。 -/
def fiberwisePullbackNativeConeLowerHomotopy (i : AsSmall.{u} WalkingCospan) :
    SSet.Homotopy (fiberwisePullbackNativeConeDiagonal p f g i)
      (fiberwisePullbackNativeConeKanLeg p f g i) := by
  let V := (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).obj i
  have hv := (kanDiagramCoherentNerve_vertex
    (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)) i).trans
      (spaceInfinityVertex_eq_coherent _)
  have hr : (coneHomotopyDiagramEdge (fiberwisePullbackNativeConeHomotopy p f g)
      (ULift.up (ComposableArrows.mk₀ i))).edge = (coherentNerveEdge (𝟙 V)).edge := by
    rw [fiberwisePullbackNativeConeHomotopy_diagramEdge]
    calc
      _ = PinchedHom.constant (coherentNerveVertex V) 1 :=
        congrArg (fun v => PinchedHom.constant v 1) hv
      _ = _ := by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl
  let e := kanConeHomotopyLower (fiberwisePullbackNativeConeHomotopy p f g) _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _))
    i (𝟙 V) hr
  exact { h := e.h, h₀ := e.h₀, h₁ := e.h₁.trans (Category.comp_id _), rel := e.rel }

/-- 概要：上側の指定三角形は共通対角と元の比較・区間錐の脚の合成を結ぶ。
方針：元の頂点比較辺を使う。規約：同じ円柱・同じ対角。使われ方：脚の指定比較。 -/
def fiberwisePullbackNativeConeUpperHomotopy (i : AsSmall.{u} WalkingCospan) :
    SSet.Homotopy (fiberwisePullbackNativeConeDiagonal p f g i)
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i) :=
  kanConeHomotopyUpper (fiberwisePullbackNativeConeHomotopy p f g) _ _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _))
    ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _)) i
    (fiberwisePullbackComparisonKanMap p f g) (fiberwisePullbackNativeConeHomotopy_apexEdge p f g)

end SerrePositivity.InfinityCategories.F2
