module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilyCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootEdgeFamily

/-!
概要：元の左三角形の共通 Hom 族から native な共通脚の前合成へ、終点固定円柱を射影する。
方針：長辺 02 の全族の同じ切断比較円柱を始点へ制限し、既存の両端係数公式を適用する。
規約：裸のホモトピー存在命題から代表を選ばない。元の辺全体と終点固定条件を保持する。
使われ方：共通 end の左制限から得た第三辺を native な共通成分へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "e" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "F" => specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))

/-- 元の長辺 02 の族を切断による族へ比較する、終点を固定した実際の円柱データ。 -/
def specifiedCoconeLeftRootNativeCylinderData : CosliceEdgeFamilyCylinder e y F :=
  cosliceEdgeFamilyCylinder e y F

set_option maxHeartbeats 800000 in
-- 指定余錐の頂点と長辺 02 の全 Hom の表示を両端で同時に照合する。
/-- 同じ終点固定円柱から作る、元の左三角形の全 Hom 族と native な共通脚の前合成の比較。 -/
def specifiedCoconeLeftRootNativeCylinder : @SSet.Homotopy
    (pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y)
    (pinchedHomLeft c.vertex y)
    (specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
      leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom)
    (specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y) := by
  let H := functorHomotopyPostcomp
    (cosliceEdgeFamilyPrecompositionCylinder e y F (coconeVertexDiagram c)
      (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))
      (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)
      (specifiedCoconeNativeRootEdge_target hp p c hc dB dC))
    (leftFibrationInitialBaseIso q c y).hom
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y ≫
          leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom
        exact H.h₀.trans ((congrArg (fun k ↦ k ≫ (leftFibrationInitialBaseIso q c y).hom)
          (specifiedCoconeLeftRootBaseEdgeFiberFamily_source hp p c hc dB dC y)).trans
            (Category.assoc _ _ _))
      h₁ := by
        change SSet.ι₁ ≫ H.h = specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y
        exact H.h₁.trans ((congrArg (fun k ↦
          (k ≫ cosliceEdgeFiberPrecomposition e (coconeVertexDiagram c)
            (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))
            (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)
            (specifiedCoconeNativeRootEdge_target hp p c hc dB dC) y) ≫
              (leftFibrationInitialBaseIso q c y).hom)
          (specifiedCoconeLeftRootBaseEdgeFiberFamily_target hp p c hc dB dC y)).trans
            (Category.assoc _ _ _))
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- native な前合成への比較は、終点を固定した元の全辺の円柱の同じ始点射影である。 -/
lemma specifiedCoconeLeftRootNativeCylinder_projection :
    (specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y).h =
      (specifiedCoconeLeftRootNativeCylinderData hp p c hc dB dC y).homotopy.h ≫
        normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2))
          (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) y ≫
          (leftFibrationInitialBaseIso q c y).hom := by
  change (cosliceEdgeFamilyPrecompositionCylinder e y F (coconeVertexDiagram c)
      (coconeVertexDiagram (partialColimitSpecifiedPathCocone hp p c hc dB dC))
      (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)
      (specifiedCoconeNativeRootEdge_target hp p c hc dB dC)).h ≫ _ = _
  exact (congrArg (fun k ↦ k ≫ (leftFibrationInitialBaseIso q c y).hom)
    (cosliceEdgeFamilyPrecompositionCylinder_projection e y F _ _ _ _)).trans
      (Category.assoc _ _ _)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
