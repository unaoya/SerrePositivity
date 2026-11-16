module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalBKProbeCone
public import SerrePositivity.EInfinity.HomotopyWeight.ProjectiveWeightComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：元のprobe錐空間から同じBK切断空間への実写像は、ホモトピー同値で指定点を保つ。
方針：同じ右frameのHomのKan性と、指定BK重み比較のHom不変性を使う。
規約：IS-W2 R02〜R03の同じ写像の照合。native join錐の普遍性をここでは主張しない。
使われ方：全Hom∞比較と指定native錐への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKSectionsModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotBKSectionsProbeCofibrant (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

/-- 元の同じprobeと右frameの係数図式の各値はKan。 -/
theorem strictBETotProbeCoefficients_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    SSet.KanComplex ((strictBETotProbeCoefficients A K F Y).obj i) := by
  letI probeFibrantOp := fibrantOp_of_cofibrant (framedLimitProbe A Y)
  exact cosimplicialHom_kanComplex _ (rightFrame_cofibrant A (F.obj i.unop.unop))
    (fun f => rightFrame_homotopicallyConstant A (F.obj i.unop.unop) f)
    (op (framedLimitProbe A Y))

/-- 同じprobe係数の指定BK制限は、実際のホモトピー同値。 -/
theorem strictBETotProbeBKRestriction_homotopyEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
      (strictBETotProbeCoefficients A K F Y)) :=
  HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant _ _ _ _
    (HomotopyWeight.bousfieldKanWeight_cofibrant _)
    (HomotopyWeight.framedLimitWeight_cofibrant _)
    (HomotopyWeight.bkFramedWeightComparison_weak _) _ (strictBETotProbeCoefficients_kanComplex A K F Y)

/-- 元のprobe錐空間から、同じ係数を持つnative BK切断空間への二つの指定写像の合成。 -/
def strictBETotProbeConeBKMap (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    ((framedLimitConeSpace A K Y).obj F) ⟶
      weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ) (strictBETotProbeCoefficients A K F Y) :=
  ((HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
    (HomotopyWeight.framedLimitWeight K)).hom.app (strictBETotProbeCoefficients A K F Y)) ≫
      weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
        (strictBETotProbeCoefficients A K F Y)

/-- 同じ二つの実写像の合成は、元の全probe錐空間についてホモトピー同値。 -/
theorem strictBETotProbeConeBKMap_homotopyEquivalence
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (strictBETotProbeConeBKMap A K F Y) := by
  let H := strictBETotProbeCoefficients A K F Y
  have hH := strictBETotProbeCoefficients_kanComplex A K F Y
  letI sourceKan := HomotopyWeight.coneSpace_kanComplex Kᵒᵖᵒᵖ
    (HomotopyWeight.framedLimitWeight K) (HomotopyWeight.framedLimitWeight_cofibrant K) H hH
  letI middleKan := HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant
    Kᵒᵖᵒᵖ (HomotopyWeight.framedLimitWeight K)
      (HomotopyWeight.framedLimitWeight_cofibrant K) H hH
  letI targetKan := HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant
    Kᵒᵖᵒᵖ (bousfieldKanWeight Kᵒᵖᵒᵖ) (HomotopyWeight.bousfieldKanWeight_cofibrant Kᵒᵖᵒᵖ) H hH
  letI nativeFunctorKan : SSet.KanComplex
      ((weightedSectionsFunctor (HomotopyWeight.framedLimitWeight K)).obj H) := by
    change SSet.KanComplex (weightedSections (HomotopyWeight.framedLimitWeight K) H)
    exact middleKan
  have hi := (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    ((HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
      (HomotopyWeight.framedLimitWeight K)).app H)).isQCatEquivalence.isSimplicialHomotopyEquivalence
  exact hi.comp (strictBETotProbeBKRestriction_homotopyEquivalence A K F Y)

/-- 同じ実写像は、元の普遍probe錐の同じ指定点を保つ。 -/
theorem strictBETotProbeConeBKMap_point (F : K ⥤ (operad A).Algebra) :
    ((strictBETotProbeConeBKMap A K F ((framedLimitFunctor A K).obj F)).app (op ⦋0⦌))
      (strictBETotUniversalProbeConePoint A K F) = strictBETotUniversalBKProbeConePoint A K F :=
  strictBETotUniversalBKProbeConePoint_comparison A K F

end SerrePositivity.EInfinity.BarrattEccles
