module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackConeConstantDiagram
public import SerrePositivity.InfinityCategories.F2.FunctorIsoConstantSquare

/-!
概要：恒等図式成分を消した全空間引き戻し錐の脚の指定比較の自然性。
方針：元の三整合式からの自然性に定値図式の厳密な簡約を合成する。
規約：元の比較射と指定同型の値を保持。使われ方：元の path との照合。
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

/-- 概要：元の脚の指定比較は両錐の元の三角形に対して整合する。
方針：恒等成分・等式からの図式同型を全錐の自然性から同時に消去する。
規約：元の全空間頂点と比較射を保持。使われ方：二脚の可換性と指定 path の比較。 -/
lemma fiberwisePullbackConeLegIso_naturality
    {i j : AsSmall.{u} WalkingCospan} (a : i ⟶ j) :
    fiberwisePullbackConeTriangleIso p f g a ≪≫
        (fiberwisePullbackConeLegIso p f g i).postcomp
          ((kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a) =
      fiberwisePullbackConeLegIso p f g j ≪≫
        (kanNativeConeTriangleIso
          (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)) _
          ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _)) a).precomp
            (show (fiberwisePullbackTotalKanObject p f g).obj ⟶
              (fiberwisePullbackTargetKanObject f g).obj from
                fiberwisePullbackComparisonKanMap p f g) := by
  exact functorIso_constant_square
    ((kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).map a)
    (kanConeDiagramComponent (fiberwisePullbackNativeConeHomotopy p f g) i)
    (kanConeDiagramComponent (fiberwisePullbackNativeConeHomotopy p f g) j)
    (fiberwisePullbackConeTriangleIso p f g a) _
    (fiberwisePullbackConeLegComparisonIso p f g i)
    (fiberwisePullbackConeLegComparisonIso p f g j)
    (kanConeDiagramComparisonIso (fiberwisePullbackNativeConeHomotopy p f g) a)
    (fiberwisePullbackConeLegIso p f g i) (fiberwisePullbackConeLegIso p f g j)
    (fiberwisePullbackConeDiagramComponent_eq_id p f g i)
    (fiberwisePullbackConeDiagramComponent_eq_id p f g j)
    (fiberwisePullbackConeDiagramComparisonIso_isFunctorEqIso p f g a)
    (fiberwisePullbackConeLegIso_heq p f g i) (fiberwisePullbackConeLegIso_heq p f g j)
    (fiberwisePullbackConeLegComparisonIso_naturality p f g a)

end SerrePositivity.InfinityCategories.F2
