module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofParameter
public import SerrePositivity.EInfinity.FrameHom.NerveColumnWhiskering

/-!
概要：元の全 augmentation 同型を同じ roof の列の同型へ制限する。
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
local instance jointRoofNativeAugmentationLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofNativeAugmentationLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じ元のfull augmentationの辺を元のモデル源が反転する。 -/
theorem strictBETotJointSourceRoofFullAugmentation_inverted
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    IsInvertibleEdge ((nerve.edgeMk
      ((strictBETotJointSourceRoofFullAugmentation A P).app s)).map
      (strictBETotModelSource A)).toTruncated :=
  SimplicialLocalization.weakNerveEdges_inverts_arrows
    (modelRelativeCategory (operad A).Algebra) (strictBETotModelSource A)
    (strictBETotModelSource_isLocalization A).choose _
    (strictBETotJointSourceRoofFullAugmentation_weak A P s)

/-- 元の同じ全augmentation同型を制限すると、同じroofの全変換の同型そのもの。 -/
theorem strictBETotJointSourceFrameAugmentationIso_roof_restriction
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (strictBETotJointRoofParameterIndex A P)))
      (FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFullAugmentation A P)
        (strictBETotJointSourceRoofFullAugmentation_inverted A P)) := by
  have h0 := sameNerveTransformationPostIso_precomp
    (strictBETotJointRoofParameterIndex A P) (strictBETotJointSourceFrameAugmentation A)
    (strictBETotModelSource A) (strictBETotJointSourceFrameAugmentation_inverted A)
  have h1 := sameNerveTransformationPostIso_heq
    (strictBETotJointRoofParameterIndex_evaluation A P)
    (strictBETotJointRoofParameterIndex_constant A P)
    (CategoryTheory.Functor.whiskerLeft (strictBETotJointRoofParameterIndex A P)
      (strictBETotJointSourceFrameAugmentation A))
    (strictBETotJointSourceRoofFullAugmentation A P)
    (strictBETotJointRoofParameterIndex_augmentation A P)
    (strictBETotModelSource A)
    (fun s => strictBETotJointSourceFrameAugmentation_inverted A
      ((strictBETotJointRoofParameterIndex A P).obj s))
    (strictBETotJointSourceRoofFullAugmentation_inverted A P)
  have h2 := sameNerveTransformationPostIso_augmentation
    (strictBETotJointSourceRoofFrameDiagram A P)
    (strictBETotJointSourceRoofFullAugmentation A P)
    (strictBETotModelSource A) (strictBETotJointSourceRoofFullAugmentation_inverted A P)
  exact h0.trans (h1.trans (heq_of_eq h2))

end SerrePositivity.EInfinity.BarrattEccles
