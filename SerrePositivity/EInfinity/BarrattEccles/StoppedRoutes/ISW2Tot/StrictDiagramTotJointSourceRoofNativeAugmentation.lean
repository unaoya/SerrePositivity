module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofParameter
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnWhiskering

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の全 augmentation 同型を同じ roof の列の同型へ制限する。
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
local instance jointRoofNativeAugmentationLawModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointRoofNativeAugmentationLawFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 同じ元のfull augmentationの辺を元のモデル源が反転する。 -/
theorem strictBETotJointSourceRoofFullAugmentation_inverted
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    IsInvertibleEdge ((nerve.edgeMk
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P).app s)).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_arrows
    (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_isLocalization A).choose _
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_weak A P s)

/-- 元の同じ全augmentation同型を制限すると、同じroofの全変換の同型そのもの。 -/
theorem strictBETotJointSourceFrameAugmentationIso_roof_restriction
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    HEq ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P)))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_inverted A P)) := by
  have h0 := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_precomp
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_inverted A)
  have h1 := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_heq
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_evaluation A P)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_constant A P)
    (CategoryTheory.Functor.whiskerLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex_augmentation A P)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
    (fun s => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_inverted A
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofParameterIndex A P).obj s))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_inverted A P)
  have h2 := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_augmentation
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation A P)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFullAugmentation_inverted A P)
  exact h0.trans (h1.trans (heq_of_eq h2))

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
