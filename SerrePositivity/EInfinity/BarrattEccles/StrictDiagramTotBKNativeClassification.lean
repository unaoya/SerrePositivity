module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotBKClassification
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.CoherentConeLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction

/-!
概要：元のBK係数のleft fibrationと同じ頂点のnative錐のleft fibrationを全分類で比較する。
方針：通常のnerveでの分類の表現比較と、同じcosliceの指定引き戻しの基底変更則を使う。
規約：IS-W2 R02〜R03の既存比較の貼り合わせ。元の底・頂点を保持する。
使われ方：同じBK切断空間から元のnative錐空間への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKNativeClassificationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotBKNativeClassificationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotBKNativeClassificationCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

local instance strictBETotBKNativeCoefficientKan (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex
    (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj _)
  infer_instance

/-- 同じ大きい添字の図式を、CAlgの元の宇宙で読む。 -/
def strictBETotUniverseSourceDiagram (F : K ⥤ (operad A).Algebra) :
    nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶ CAlg_R A :=
  nerveMap (strictBETotProbeFrameIndex A K F) ≫ strictBETotModelSource A

/-- 分類の底の宇宙変更は、元の全図式の同じ宇宙変更射。 -/
theorem strictBETotUniverseSourceDiagram_lift (F : K ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotUniverseSourceDiagram A K F) =
      strictBETotUniverseDiagram A K F := rfl

/-- 元のweighted nerveと、同じ元の頂点のnative錐の射影の全分類比較。 -/
def strictBETotBKNativeClassificationIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso
      (leftStraighteningInfinityDiagram (weightedNerveProjection
        (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget)))
      (leftStraighteningInfinityDiagram (coherentConeProjection
        (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
          (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)))) := by
  let p := weightedNerveProjection (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget)
  let R := nativeLeftTransportRepresentation p
  have hc : FunctorIso (leftStraighteningCandidate p) (leftStraighteningInfinityDiagram p) :=
    (nerveStraighteningRepresentationIso p R).trans
      (leftStraighteningInfinityDiagram_representationIso p R).symm
  have hb := strictBETotBKClassificationIso A K F Y
  change FunctorIso (leftStraighteningCandidate p) _ at hb
  have hd := hc.symm.trans hb
  have he := leftStraighteningInfinityDiagram_baseChangeIso
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))))
    (strictBETotUniverseSourceDiagram A K F)
  rw [strictBETotUniverseSourceDiagram_lift] at he
  exact hd.trans he

end SerrePositivity.EInfinity.BarrattEccles
