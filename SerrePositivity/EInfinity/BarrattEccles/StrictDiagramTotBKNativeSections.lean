module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotBKNativeClassification
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanSectionsIso

/-!
概要：同じBE TotのEx∞ BK係数から、元の同じ頂点のnative錐の切断模型へ戻す。
方針：元の二つの射影の全分類同型にR03bを適用し、元の切断模型の指定同型を合成する。
規約：IS-W2 R03bのBEへの適用。元の頂点・全図式を保持する。
使われ方：指定BK点の像を同じnative join錐へ変換する入口。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKNativeSectionsModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotBKNativeSectionsFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotBKNativeSectionsCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y
local instance strictBETotBKNativeSectionsCoefficientKan (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] simplicialSections_kanComplex bousfieldKanHolim_kanComplex

/-- 同じBK切断と元のnative錐切断模型との実際の同値。 -/
def strictBETotBKNativeSectionsEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    QCatEquivalence
      (bousfieldKanHolim (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget))
      (coherentConeSectionSpace (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) :=
  (qCatEquivalenceOfIso (bousfieldKanSectionsIso
    (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget))).trans
      ((classifiedLeftFibrationSectionsEquivalence _ _
        (strictBETotBKNativeClassificationIso A K F Y)).trans
          (qCatEquivalenceOfIso (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
            ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))))

end SerrePositivity.EInfinity.BarrattEccles
