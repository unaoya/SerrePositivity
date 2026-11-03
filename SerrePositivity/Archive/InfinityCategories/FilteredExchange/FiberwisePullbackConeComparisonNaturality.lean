module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackFirstTetrahedronRelation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeComparisonNaturality

/-!
概要：元の全空間引き戻し比較の脚と両錐の指定三角形の整合式。
方針：元の全錐円柱の三つの四面体の関係から共有面を消去する。
規約：元の比較射・頂点・指定同型を保持。使われ方：元の path と余極限錐への接続。
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

/-- 概要：元の上下三角形による全空間錐の各脚の指定比較。
方針：同じ対角射を消去。規約：元の値を保持。使われ方：図式射に沿う整合式。 -/
def fiberwisePullbackConeLegComparisonIso (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g i ≫
      kanConeDiagramComponent (fiberwisePullbackNativeConeHomotopy p f g) i)
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i) :=
  kanConeLegComparisonIso (fiberwisePullbackNativeConeHomotopy p f g) _ _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _))
    ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _))
    (fiberwisePullbackComparisonKanMap p f g) (fiberwisePullbackNativeConeHomotopy_apexEdge p f g) i

/-- 概要：元の全空間錐の指定三角形のホモトピー類。
方針：元の二単体を読む。規約：代表を選び直さない。使われ方：二次の整合式。 -/
def fiberwisePullbackConeTriangleIso {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    FunctorIso (fiberwisePullbackNativeConeKanLeg p f g j)
      (fiberwisePullbackNativeConeKanLeg p f g i ≫
        (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a) :=
  kanNativeConeTriangleIso (fiberwisePullbackNativeCone p f g) _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _)) a

/-- 概要：元の脚の指定比較は元と区間の錐の指定三角形に対して整合する。
方針：元の円柱に対する三つの四面体の合成則から共有面を消去する。
規約：指定同型の値の等式。使われ方：元の path への最終照合。 -/
lemma fiberwisePullbackConeLegComparisonIso_naturality
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    (fiberwisePullbackConeTriangleIso p f g a).postcomp
        (kanConeDiagramComponent (fiberwisePullbackNativeConeHomotopy p f g) j) ≪≫
      (kanConeDiagramComparisonIso (fiberwisePullbackNativeConeHomotopy p f g) a).precomp
        (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
          ((kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).obj i).obj from
            fiberwisePullbackNativeConeKanLeg p f g i) ≪≫
      (fiberwisePullbackConeLegComparisonIso p f g i).postcomp
        ((kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a) =
    fiberwisePullbackConeLegComparisonIso p f g j ≪≫
      (kanNativeConeTriangleIso
        (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)) _
        ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _)) a).precomp
          (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
            (fiberwisePullbackTargetKanObject f g).obj from
              fiberwisePullbackComparisonKanMap p f g) :=
  kanConeLegComparisonIso_naturality (fiberwisePullbackNativeConeHomotopy p f g) _ _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _))
    ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _))
    (fiberwisePullbackComparisonKanMap p f g) (fiberwisePullbackNativeConeHomotopy_apexEdge p f g) a

end SerrePositivity.InfinityCategories.F2
