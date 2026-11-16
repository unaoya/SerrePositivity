module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetFiber
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoConstantFamily

/-!
概要：元の同じ標的置換単位の逆を全パラメータで回収する。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointTargetUnitLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointTargetUnitLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 指定された元の構成の値を保つ照合則。 -/
theorem strictBETotTargetReplacementNativeIso_symm_constant_family
    (P : strictBETotJointHomIndex A) :
    (constantFunctorCompIso
      (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
      (nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (strictBETotTargetReplacementNativeIso A).symm
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (strictBETotJointSourceCoefficients A)).obj P))
            (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))).hom ≫
      (constantFunctorCompIso
        (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
        (strictBETotModelSource A)).hom =
      constantFunctorHomMap
        (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
        ((strictBETotTargetReplacementNativeIso A).app
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))).inv := by
  have h := sameFunctorIso_constant_family
    (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
    (strictBETotTargetReplacementNativeIso A).symm
    (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
  rw [FunctorIso.app_symm] at h
  exact h

end SerrePositivity.EInfinity.BarrattEccles
