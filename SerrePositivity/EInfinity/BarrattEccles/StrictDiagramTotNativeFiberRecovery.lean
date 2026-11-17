module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotNativeSectionsRecovery
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsTriangle

/-!
概要：元のBE Totの全BK切断三角形を、同じ指定次数のfiberで評価する。
方針：同じ全切断三角形をfiber評価で後合成し、評価と後合成の厳密な自然性を使う。
規約：IS-W2 R02〜R03の既存の合成・余単位則。全高次単体の比較を保持する。
使われ方：同じ指定BK点と標準脚の評価の、元の分類変換との照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotNativeFiberRecoveryModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotNativeFiberRecoveryFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeFiberRecoveryCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y
local instance strictBETotNativeFiberRecoveryKan (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex

/-- 元の全BK切断比較の復元三角形は、同じ次数のfiber評価とも全関手同型で一致する。 -/
def strictBETotBKNativeSections_fiber_reconstruction
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra)
    (b : (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) _⦋0⦌) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    let η := strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsFiberEvaluation q b ≫
              vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
                (leftStraighteningInfinityReconstruction_projection q) b)
      ((bousfieldKanSectionsIso H).hom ≫ simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b) := by
  let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
  let p := weightedNerveProjection H
  let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  let η := strictBETotBKNativeClassificationIso A K F Y
  have h := FunctorIso.postcomp (strictBETotBKNativeSections_reconstruction A K F Y)
    (simplicialSectionsFiberEvaluation r b)
  have hq := simplicialSectionsFiberEvaluation_naturality q r
    (leftStraighteningInfinityReconstruction q)
    (leftStraighteningInfinityReconstruction_projection q) b
  have hp := simplicialSectionsFiberEvaluation_naturality p r
    (classifiedFibrationTransport p q η) (classifiedFibrationTransport_projection p q η) b
  simp only [Category.assoc] at h
  rw [hq, hp] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
