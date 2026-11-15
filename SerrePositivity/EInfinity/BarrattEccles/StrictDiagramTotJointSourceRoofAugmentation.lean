module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofFrame
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceAugmentationComparison

/-!
概要：元の probe 比較を含む同じ全 augmentation を記録する。
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
local instance jointRoofAugmentationLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofAugmentationLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じsource-frameのaugmentationを元のprobe比較と合成する全変換。 -/
def strictBETotJointSourceRoofFullAugmentation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop) :=
  strictBETotJointSourceRoofFrameAugmentation A P ≫
    (CategoryTheory.Functor.const _).map
      ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        (framedLimitProbeComparison A (AsSmall.down.obj P).1.unop))

/-- 元の全augmentationの成分は、同じ二つの元の射の合成。 -/
theorem strictBETotJointSourceRoofFullAugmentation_app
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointSourceRoofFullAugmentation A P).app s =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        ((strictBETotJointRoofResolution A P).augmentation.app s.unop.obj.unop ≫
          framedLimitProbeComparison A (AsSmall.down.obj P).1.unop) := by
  exact ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map_comp _ _).symm

/-- 同じ合成は、元の全パラメータのaugmentationの同じ成分そのもの。 -/
theorem strictBETotJointSourceRoofFullAugmentation_original
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointSourceRoofFullAugmentation A P).app s =
      (strictBETotJointSourceFrameAugmentation A).app
        ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤
          strictBETotJointSourceFrameIndex A).obj
            ((AsSmall.down.obj P).1.unop, s.unop.obj.unop)) := by
  rw [strictBETotJointSourceRoofFullAugmentation_app]
  rfl

/-- 元のfull augmentationの各成分も、元のモデル弱同値。 -/
theorem strictBETotJointSourceRoofFullAugmentation_weak
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFullAugmentation A P).app s) := by
  rw [strictBETotJointSourceRoofFullAugmentation_original]
  exact strictBETotJointSourceFrameAugmentation_weak A _

end SerrePositivity.EInfinity.BarrattEccles
