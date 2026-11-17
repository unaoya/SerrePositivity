module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceTargetFiber
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoConstantFamily

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の同じ標的置換単位の逆を全パラメータで回収する。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

variable (A : Type u) [CommRing A]
local instance jointTargetUnitLawModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointTargetUnitLawFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 指定された元の構成の値を保つ照合則。 -/
theorem strictBETotTargetReplacementNativeIso_symm_constant_family
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    (constantFunctorCompIso
      (nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P))
      (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).symm
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P))
            (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P)))).hom ≫
      (constantFunctorCompIso
        (nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P))
        (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).hom =
      constantFunctorHomMap
        (nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).app
          (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))).inv := by
  have h := sameFunctorIso_constant_family
    (nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).symm
    (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))
  rw [FunctorIso.app_symm] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
