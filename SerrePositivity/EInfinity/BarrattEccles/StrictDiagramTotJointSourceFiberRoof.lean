module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberElements
public import SerrePositivity.EInfinity.FrameHom.LiftedSourceFrameFiberRoof

/-!
概要：元のnative fiberの要素を、同じ固定始域roofの反対圏へ移す。
方針：同じsource-frame係数へ既存の要素圏の移送を特殊化し、元のラベルと照合する。
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
local instance jointFiberRoofModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointFiberRoofFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩




/-- 元の同じ二変数のfiber係数を、同じ固定始域のroofの反対圏へ移す。 -/
def strictBETotJointSourceFiberRoofEquivalence (P : strictBETotJointHomIndex A) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P ≌
      (CostructuredArrow ((strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))ᵒᵖ :=
  FrameHom.liftedSourceFrameFiberRoofEquivalence (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A)) P

/-- 同じ元のHom単体の次数を、同じroofの次数として回収する。 -/
theorem strictBETotJointSourceFiberRoofEquivalence_degree (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    (((strictBETotJointSourceFiberRoofEquivalence A P).functor.obj s).unop).left =
      s.obj.unop := rfl

/-- roofの同じラベルは、元のnative pairingへ渡した同じsource-frameの実射。 -/
theorem strictBETotJointSourceFiberRoofEquivalence_pairingValue
    (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    (((strictBETotJointSourceFiberRoofEquivalence A P).functor.obj s).unop).hom =
      FrameHom.sourceFrameArrowValue (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))
        ((strictBETotJointSourceFiberElements A P).obj s) := rfl
end SerrePositivity.EInfinity.BarrattEccles
