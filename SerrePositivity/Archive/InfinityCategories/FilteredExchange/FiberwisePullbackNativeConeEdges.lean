module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackNativeConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction

/-!
概要：全空間 Kan 引き戻し錐の比較辺を元の比較射と恒等図式辺へ同定する。
方針：全錐円柱の二制限を各頂点で評価する。
規約：頂点辺は元の比較射、図式辺は恒等。使われ方：元の三射影と native 錐の脚の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：全錐比較の頂点辺は元の Kan 比較射の coherent な辺の一単体そのもの。
方針：頂点の指定 prism を評価する。規約：辺の代表を変更しない。使われ方：脚の自然性。 -/
lemma fiberwisePullbackNativeConeHomotopy_apexEdge :
    (coneHomotopyApexEdge (fiberwisePullbackNativeConeHomotopy p f g)).edge =
      (coherentNerveEdge (fiberwisePullbackComparisonKanMap p f g)).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have h := homotopyVertexEdge_prism (fiberwisePullbackNativeConeHomotopy p f g)
    (joinInl _ J) (fiberwisePullbackComparisonApexPrism p f g)
    (fiberwisePullbackNativeConeHomotopy_apex p f g) (SSet.yonedaEquiv (𝟙 _))
  calc
    _ = _ := h
    _ = _ := SSet.yonedaEquiv_symm_app_id
      (coherentNerveEdge (fiberwisePullbackComparisonKanMap p f g)).edge

/-- 概要：全錐比較の図式辺は元の図式の値で定値な一単体。
方針：図式の定値制限を頂点で評価。規約：全ての添字。使われ方：恒等図式辺の消去。 -/
lemma fiberwisePullbackNativeConeHomotopy_diagramEdge
    (i : ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (AsSmall.{u} WalkingCospan))) _⦋0⦌) :
    (coneHomotopyDiagramEdge (fiberwisePullbackNativeConeHomotopy p f g) i).edge =
      PinchedHom.constant ((kanDiagramCoherentNerve
        (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g))).app
          (Opposite.op ⦋0⦌) i) 1 :=
  homotopyVertexEdge_constant (fiberwisePullbackNativeConeHomotopy p f g) (joinInr _ _) _
    (fiberwisePullbackNativeConeHomotopy_diagram p f g) i

/-- 概要：各 native 脚は、比較先の脚を元の比較の頂点辺で前合成したものに一致する。
方針：全錐の自然性で図式の恒等辺を消す。
規約：ホモトピー圏での可換式。使われ方：構成済み比較の三射影と脚の照合。 -/
lemma fiberwisePullbackNativeCone_leg_naturality
    (i : ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (AsSmall.{u} WalkingCospan))) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk (nativeConeLeg (fiberwisePullbackNativeCone p f g) i) =
      SSet.Truncated.HomotopyCategory.homMk
        (coneHomotopyApexEdge (fiberwisePullbackNativeConeHomotopy p f g)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (nativeConeLeg (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)) i) := by
  have hd : coneHomotopyDiagramEdge (fiberwisePullbackNativeConeHomotopy p f g) i =
      SSet.Truncated.Edge.id (X := (truncation 2).obj SpaceInfinity.{u})
        ((kanDiagramCoherentNerve (kanPullbackDiagram
          (continuousKanMap f) (continuousKanMap g))).app (Opposite.op ⦋0⦌) i) := by
    apply SSet.Truncated.Edge.ext
    rw [fiberwisePullbackNativeConeHomotopy_diagramEdge, pinchedConstant_one]
  have h := coneHomotopy_leg_naturality (fiberwisePullbackNativeConeHomotopy p f g) i
  rw [hd, SSet.Truncated.HomotopyCategory.homMk_id, Category.comp_id] at h
  exact h

end SerrePositivity.InfinityCategories.F2
