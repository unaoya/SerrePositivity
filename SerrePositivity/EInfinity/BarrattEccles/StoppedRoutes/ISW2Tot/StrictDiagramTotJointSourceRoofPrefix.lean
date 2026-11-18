module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofGraph

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の弱比較を同じ roof prefix の全写像として回収する。
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
local instance jointRoofPrefixLawModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointRoofPrefixLawFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の実roof比較は、同じfiber上のRoofPrefixの全族そのもの。 -/
theorem strictBETotJointSourceRoofKanComparison_prefix
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofKanComparison A P =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.familyMap
        (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameAugmentation A P)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameAugmentation_weak A P)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram_weak A P) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  let W := weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
  let X := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop
  let Y := (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2
  let q := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A P
  let K := (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y
  let τ := ((elementsOppositeUniverseNerveIso.{u+1,u} K).hom ≫
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofNerveMap W q.obj q.augmentation q.augmentation_weakEquivalence
      (fun f => q.homotopicallyConstant f)).app n σ
  change (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app n
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso W X Y).hom.app n
      ((graphInclusion W X Y LeftRoof.word).app n τ)) =
    (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app n
      ((graphInclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W)
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj X)
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj Y)
        LeftRoof.word).app n ((nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameZigzag A P)).app n σ))
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso_graph_point]
  have h := congrArg (fun f => f.app n σ) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameZigzag_nerve A P)
  change τ ⋙ RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.up W) =
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameZigzag A P)).app n σ at h
  exact congrArg (fun z =>
    (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app n
      ((graphInclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W)
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj X)
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).obj Y)
        LeftRoof.word).app n z)) h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
