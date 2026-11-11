module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomLiftPrism
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomTransportAction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeExtensionHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ConstantBaseEndpointHomotopy

/-!
概要：既存の点 Hom の族と全始点の輸送作用を、同じ底と始点を保つ実際の円柱で比較する。
方針：両方の持ち上げを同じ相対延長空間内で結び、その同じ円柱を終点で評価する。
規約：元の点 Hom の族・底の全 Hom 円柱・初期値を同時に保持する。
使われ方：指定 fiber 経路に沿う輸送作用の変化を、既存の全 Hom 族へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (d : E _⦋0⦌) (b : B _⦋0⦌)

/-- 元の点を、その底の上の同じ fiber 頂点として表示する。 -/
def pointHomSourceVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (p.app (Opposite.op ⦋0⦌) d)) _⦋0⦌ :=
  ⟨d, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩

/-- 同じ底と初期値を保持する、二つの実際の点 Hom 円柱の比較データ。 -/
structure PointHomActionComparison where
  homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomLiftPrism p d b)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportPrismAt p (p.app (Opposite.op ⦋0⦌) d) b (pointHomSourceVertex p d))
  projection : homotopy.h ≫ p =
    fst ((Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b) Δ[1] ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism (p.app (Opposite.op ⦋0⦌) d) b
  initial : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b) ▷
      (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst ((Δ[0] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b) Δ[1] ≫
      snd (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b) ≫ SSet.const d

/-- 元の両円柱と、その底・初期値の条件を保った同じ比較を選ぶ。 -/
def pointHomActionComparison : PointHomActionComparison p d b :=
  Classical.choice (by
    let Z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b
    let β := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism (p.app (Opposite.op ⦋0⦌) d) b
    let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ Z
    let v := snd (Δ[0] : SSet.{u}) Z ≫ SSet.const d
    have hW : i ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomLiftPrism p d b = v := by
      dsimp only [i, v]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Z ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomLiftPrism_zero]
    have hU : i ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportPrismAt p (p.app (Opposite.op ⦋0⦌) d) b
        (pointHomSourceVertex p d) = v := by
      dsimp only [i, v]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Z ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportPrismAt_zero]
      rfl
    have hv : v ≫ p = i ≫ β := by rw [← hW, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomLiftPrism_projection]
    obtain ⟨H, hH, hI⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension p β i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 Z) v hv _ _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomLiftPrism_projection p d b)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportPrismAt_projection p _ b (pointHomSourceVertex p d)) hW hU
    exact ⟨⟨H, hH, by simpa only [Category.assoc] using hI⟩⟩)

/-- 終点で評価した同じ円柱による、既存の全 Hom の族と全始点の作用の比較。 -/
def pointHomActionComparisonHomotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p d b)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportActionAt p (p.app (Opposite.op ⦋0⦌) d) b (pointHomSourceVertex p d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy p (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism (p.app (Opposite.op ⦋0⦌) d) b)
    (pointHomActionComparison p d b).homotopy (pointHomActionComparison p d b).projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _) b (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomBasePrism_one _ b) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomLiftPrism_one p d b) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportPrismAt_one p _ b (pointHomSourceVertex p d))

/-- 公開した全 Hom 比較の円柱は、同じ相対円柱の終点での制限そのもの。 -/
lemma pointHomActionComparisonHomotopy_projection :
    (pointHomActionComparisonHomotopy p d b).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) b) ▷ (Δ[1] : SSet.{u})) ≫
        (pointHomActionComparison p d b).homotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy_projection _ _ _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
