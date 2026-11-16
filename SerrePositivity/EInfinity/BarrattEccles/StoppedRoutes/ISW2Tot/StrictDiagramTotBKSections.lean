module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniversalBKProbeCone
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のprobe錐空間から同じBK切断空間への実写像は、ホモトピー同値で指定点を保つ。
方針：同じ右frameのHomのKan性と、指定BK重み比較のHom不変性を使う。
規約：IS-W2 R02〜R03の同じ写像の照合。native join錐の普遍性をここでは主張しない。
使われ方：全Hom∞比較と指定native錐への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SSet
open _root_.SerrePositivity.DiagramModel _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKSectionsModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotBKSectionsProbeCofibrant (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y

/-- 元の同じprobeと右frameの係数図式の各値はKan。 -/
theorem strictBETotProbeCoefficients_kanComplex (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    SSet.KanComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y).obj i) := by
  letI probeFibrantOp := fibrantOp_of_cofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)
  exact cosimplicialHom_kanComplex _ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrame_cofibrant A (F.obj i.unop.unop))
    (fun f => _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrame_homotopicallyConstant A (F.obj i.unop.unop) f)
    (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y))

/-- 同じprobe係数の指定BK制限は、実際のホモトピー同値。 -/
theorem strictBETotProbeBKRestriction_homotopyEquivalence (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant _ _ _ _
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanWeight_cofibrant _)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant _)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison_weak _) _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients_kanComplex A K F Y)

/-- 元のprobe錐空間から、同じ係数を持つnative BK切断空間への二つの指定写像の合成。 -/
def strictBETotProbeConeBKMap (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace A K Y).obj F) ⟶
      weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y) :=
  ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).hom.app (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y)) ≫
      weightedSectionsPre (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y)

/-- 同じ二つの実写像の合成は、元の全probe錐空間についてホモトピー同値。 -/
theorem strictBETotProbeConeBKMap_homotopyEquivalence
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeConeBKMap A K F Y) := by
  let H := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y
  have hH := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients_kanComplex A K F Y
  letI sourceKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_kanComplex Kᵒᵖᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) H hH
  letI middleKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant
    Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) H hH
  letI targetKan := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSections_kanComplex_of_projective_cofibrant
    Kᵒᵖᵒᵖ (bousfieldKanWeight Kᵒᵖᵒᵖ) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanWeight_cofibrant Kᵒᵖᵒᵖ) H hH
  letI nativeFunctorKan : SSet.KanComplex
      ((weightedSectionsFunctor (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).obj H) := by
    change SSet.KanComplex (weightedSections (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) H)
    exact middleKan
  have hi := (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).app H)).isQCatEquivalence.isSimplicialHomotopyEquivalence
  exact hi.comp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeBKRestriction_homotopyEquivalence A K F Y)

/-- 同じ実写像は、元の普遍probe錐の同じ指定点を保つ。 -/
theorem strictBETotProbeConeBKMap_point (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeConeBKMap A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).app (op ⦋0⦌))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeConePoint A K F) = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeConePoint A K F :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeConePoint_comparison A K F

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
