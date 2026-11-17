module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotNativeSectionsRecovery
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsTriangle

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBE Totの全BK切断三角形を、同じ指定次数のfiberで評価する。
方針：同じ全切断三角形をfiber評価で後合成し、評価と後合成の厳密な自然性を使う。
規約：IS-W2 R02〜R03の既存の合成・余単位則。全高次単体の比較を保持する。
使われ方：同じ指定BK点と標準脚の評価の、元の分類変換との照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotNativeFiberRecoveryModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotNativeFiberRecoveryFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeFiberRecoveryCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y
local instance strictBETotNativeFiberRecoveryKan (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex

/-- 元の全BK切断比較の復元三角形は、同じ次数のfiber評価とも全関手同型で一致する。 -/
def strictBETotBKNativeSections_fiber_reconstruction
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (b : (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) _⦋0⦌) :
    let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    let η := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsFiberEvaluation q b ≫
              vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
                (leftStraighteningInfinityReconstruction_projection q) b)
      ((bousfieldKanSectionsIso H).hom ≫ simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b) := by
  let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let p := weightedNerveProjection H
  let q := coherentConeProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram A K F)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  let η := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeClassificationIso A K F Y
  have h := FunctorIso.postcomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKNativeSections_reconstruction A K F Y)
    (simplicialSectionsFiberEvaluation r b)
  have hq := simplicialSectionsFiberEvaluation_naturality q r
    (leftStraighteningInfinityReconstruction q)
    (leftStraighteningInfinityReconstruction_projection q) b
  have hp := simplicialSectionsFiberEvaluation_naturality p r
    (classifiedFibrationTransport p q η) (classifiedFibrationTransport_projection p q η) b
  simp only [Category.assoc] at h
  rw [hq, hp] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
