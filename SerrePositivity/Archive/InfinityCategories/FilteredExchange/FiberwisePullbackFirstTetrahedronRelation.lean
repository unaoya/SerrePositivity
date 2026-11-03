module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackSpecifiedTriangles
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeFirstTetrahedronRelation

/-!
概要：元の全空間引き戻し比較の最初の三単体の指定合成則。
方針：元の比較辺を一般の Kan 錐の円柱の合成則へ入力する。
規約：元の頂点・比較射・全錐円柱を保持。使われ方：指定 path との最終整合。
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

/-- 概要：元の全空間錐の上側比較の指定ホモトピー類。
方針：元の円柱の上三角形。規約：元の比較射。使われ方：第一の合成則。 -/
def fiberwisePullbackNativeConeUpperIso (i : AsSmall.{u} WalkingCospan) :
    FunctorIso (fiberwisePullbackNativeConeDiagonal p f g i)
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i) :=
  kanConeUpperIso (fiberwisePullbackNativeConeHomotopy p f g) _ _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _))
    ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _))
    (fiberwisePullbackComparisonKanMap p f g) (fiberwisePullbackNativeConeHomotopy_apexEdge p f g) i

/-- 概要：第一の共有面は元の対角射と図式射の指定比較。
方針：元の二単体を読む。規約：共有面を選び直さない。使われ方：内部同型の消去。 -/
def fiberwisePullbackFirstInteriorIso {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    FunctorIso (fiberwisePullbackNativeConeDiagonal p f g j)
      (fiberwisePullbackNativeConeDiagonal p f g i ≫
        (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a) :=
  kanConeFirstInteriorIso (fiberwisePullbackNativeConeHomotopy p f g) _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _)) a

/-- 概要：元の全空間比較の上二脚と区間錐の指定三角形の第一の整合式。
方針：元の比較辺・円柱を四面の合成則へ同時に入力する。
規約：指定同型の値の等式。使われ方：中央・最後の式と合わせた内部同型の消去。 -/
lemma fiberwisePullbackFirstTetrahedron_relation
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    fiberwisePullbackNativeConeUpperIso p f g j ≪≫
        (kanNativeConeTriangleIso
          (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)) _
          ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _)) a).precomp
            (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
              (fiberwisePullbackTargetKanObject f g).obj from
                fiberwisePullbackComparisonKanMap p f g) =
      fiberwisePullbackFirstInteriorIso p f g a ≪≫
        (fiberwisePullbackNativeConeUpperIso p f g i).postcomp
          ((kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a) :=
  kanConeFirstTetrahedron_relation (fiberwisePullbackNativeConeHomotopy p f g) _ _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _))
    ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _))
    (fiberwisePullbackComparisonKanMap p f g) (fiberwisePullbackNativeConeHomotopy_apexEdge p f g) a

end SerrePositivity.InfinityCategories.F2
