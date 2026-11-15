module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPrefix
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixColumnRoof

/-!
概要：元の pinched roof の全 interval 族を同じ列の合成として表す。
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
namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointRoofColumnLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofColumnLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じroof全族の任意の後合成は、同じ全augmentationの逆と評価の像。 -/
theorem strictBETotJointSourceRoofPinchedComparison_column_roof
    {E : SSet.{u+1}} [Quasicategory E] (P : strictBETotJointHomIndex A)
    (F : SimplicialLocalization.kanHammockNerve
      (modelRelativeCategory (operad A).Algebra) ⟶ E) :
    let R := modelRelativeCategory (operad A).Algebra
    let V := strictBETotJointSourceRoofFrameDiagram A P
    let p := strictBETotJointSourceRoofFrameAugmentation A P
    let hp := strictBETotJointSourceRoofFrameAugmentation_weak A P
    Arrow.mk
      (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom
        ((strictBETotJointSourceRoofPinchedComparison A P ≫
          SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F _ _) ≫
          SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk
      ((FrameHom.NerveColumn.augmentationIso
        (SimplicialLocalization.hammockLocalizationNerveMap R ≫ F) V p
        (SimplicialLocalization.RoofPrefix.postcomp_augmentation_invertible R V p hp F)).inv ≫
        FrameHom.NerveColumn.hom
          (SimplicialLocalization.hammockLocalizationNerveMap R ≫ F)
          (strictBETotJointSourceRoofFrameEvaluation A P)) := by
  dsimp only
  rw [strictBETotJointSourceRoofPinchedComparison,
    strictBETotJointSourceRoofKanComparison_prefix]
  exact SimplicialLocalization.RoofPrefix.native_family_postcomp_column_roof_arrow
    (modelRelativeCategory (operad A).Algebra)
    (strictBETotJointSourceRoofFrameDiagram A P)
    (strictBETotJointSourceRoofFrameAugmentation A P)
    (strictBETotJointSourceRoofFrameAugmentation_weak A P)
    (strictBETotJointSourceRoofFrameEvaluation A P)
    (strictBETotJointSourceRoofFrameDiagram_weak A P) F

end SerrePositivity.EInfinity.BarrattEccles
