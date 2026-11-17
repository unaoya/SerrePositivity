module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofFrame
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceAugmentationComparison

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の probe 比較を含む同じ全 augmentation を記録する。
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
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

variable (A : Type u) [CommRing A]
local instance jointRoofAugmentationLawModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointRoofAugmentationLawFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 同じsource-frameのaugmentationを元のprobe比較と合成する全変換。 -/
def strictBETotJointSourceRoofFullAugmentation (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (AsSmall.down.obj P).1.unop) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameAugmentation A P ≫
    (CategoryTheory.Functor.const _).map
      ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj P).1.unop))

/-- 元の全augmentationの成分は、同じ二つの元の射の合成。 -/
theorem strictBETotJointSourceRoofFullAugmentation_app
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P).app s =
      (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A P).augmentation.app s.unop.obj.unop ≫
          _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj P).1.unop) := by
  exact ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map_comp _ _).symm

/-- 同じ合成は、元の全パラメータのaugmentationの同じ成分そのもの。 -/
theorem strictBETotJointSourceRoofFullAugmentation_original
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P).app s =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra × SimplexCategory ⥤
          _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A).obj
            ((AsSmall.down.obj P).1.unop, s.unop.obj.unop)) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_app]
  rfl

/-- 元のfull augmentationの各成分も、元のモデル弱同値。 -/
theorem strictBETotJointSourceRoofFullAugmentation_weak
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).weakEquivalences
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P).app s) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_original]
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_weak A _

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
