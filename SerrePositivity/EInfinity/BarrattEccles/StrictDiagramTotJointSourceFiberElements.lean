module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPairing
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberInclusion

/-!
概要：元の指定fiberの要素を、同じsource-frameの実射のラベルへ戻す。
方針：通常のfiber包含と元の全要素のdownを合成する。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance jointFiberElementsModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointFiberElementsFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩



/-- 元の指定fiberの要素を、同じ元のsource-frameの実射へ戻す通常の関手。 -/
def strictBETotJointSourceFiberElements (P : strictBETotJointHomIndex A) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P ⥤
      FrameHom.SourceFrameArrowElements (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A)) :=
  simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
    strictBETotJointSourceElementsDown A

/-- 同じ元の底と単体次数を、元のsource-frameのパラメータとして回収する。 -/
theorem strictBETotJointSourceFiberElements_parameters (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    ((strictBETotJointSourceFiberElements A P).obj s).obj = (AsSmall.down.obj P, s.obj) := rfl

/-- 元のラベルは、元のULiftされたHom単体のdownそのもの。 -/
theorem strictBETotJointSourceFiberElements_value (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    FrameHom.sourceFrameArrowValue (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A))
      ((strictBETotJointSourceFiberElements A P).obj s) = s.val.down := rfl

/-- 元のpairingへのfiber制限は、同じ通常の要素圏の包含を通る同じnerve射。 -/
theorem strictBETotJointSourceFiberPairing_eq (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
      strictBETotJointSourceNativePairing A =
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourceNativePairing A := by
  rw [simplicialElementsFiberInclusion_eq_nerveMap]
end SerrePositivity.EInfinity.BarrattEccles
