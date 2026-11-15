module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofGraph

/-!
概要：元の弱比較を同じ roof prefix の全写像として回収する。
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
local instance jointRoofPrefixLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofPrefixLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の実roof比較は、同じfiber上のRoofPrefixの全族そのもの。 -/
theorem strictBETotJointSourceRoofKanComparison_prefix
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofKanComparison A P =
      SimplicialLocalization.RoofPrefix.familyMap
        (modelRelativeCategory (operad A).Algebra)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFrameAugmentation A P)
        (strictBETotJointSourceRoofFrameAugmentation_weak A P)
        (strictBETotJointSourceRoofFrameEvaluation A P)
        (strictBETotJointSourceRoofFrameDiagram_weak A P) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  let W := weakEquivalences (operad A).Algebra
  let X := framedLimitProbe A (AsSmall.down.obj P).1.unop
  let Y := (rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2
  let q := strictBETotJointRoofResolution A P
  let K := (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y
  let τ := ((elementsOppositeUniverseNerveIso.{u+1,u} K).hom ≫
    FrameHom.frameLeftRoofNerveMap W q.obj q.augmentation q.augmentation_weakEquivalence
      (fun f => q.homotopicallyConstant f)).app n σ
  change (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app n
    ((Hammock.AsSmallComparison.colimitIso W X Y).hom.app n
      ((graphInclusion W X Y LeftRoof.word).app n τ)) =
    (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app n
      ((graphInclusion (Hammock.AsSmallComparison.weak W)
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj X)
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj Y)
        LeftRoof.word).app n ((nerveMap (strictBETotJointSourceRoofFrameZigzag A P)).app n σ))
  rw [Hammock.AsSmallComparison.colimitIso_graph_point]
  have h := congrArg (fun f => f.app n σ) (strictBETotJointSourceRoofFrameZigzag_nerve A P)
  change τ ⋙ RelativeZigzagFunctor.functor (Hammock.AsSmallComparison.up W) =
    (nerveMap (strictBETotJointSourceRoofFrameZigzag A P)).app n σ at h
  exact congrArg (fun z =>
    (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _).app n
      ((graphInclusion (Hammock.AsSmallComparison.weak W)
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj X)
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj Y)
        LeftRoof.word).app n z)) h

end SerrePositivity.EInfinity.BarrattEccles
