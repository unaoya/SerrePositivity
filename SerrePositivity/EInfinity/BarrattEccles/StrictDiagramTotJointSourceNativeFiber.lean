module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberMap

/-!
概要：元のBEのnative Hom比較射を、同じ元のfiber包含へ制限する。
方針：元の全要素上の写像と元の単位を固定する延長の三角形を、そのままfiberへ移す。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (A : Type u) [CommRing A]
local instance jointNativeFiberModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeFiberFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全要素上の同じnative Hom写像の、同じ指定fiberへの制限。 -/
def strictBETotJointSourceNativeFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      vertexFiber (strictBETotJointNativeHomProjection A) (nerveVertex P) :=
  simplicialElementsFiberMap (strictBETotJointSourceCoefficients A)
    (strictBETotJointNativeHomProjection A) (strictBETotJointSourceNativeHomMap A)
    (strictBETotJointSourceNativeHomMap_projection A) P

/-- 元の同じ全要素の置換単位のfiber制限は、R03gから来る弱同値。 -/
theorem strictBETotJointSourceFiberUnit_isWeakHomotopyEquivalence (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P) :=
  simplicialElementsFiberUnit_isWeakHomotopyEquivalence (strictBETotJointSourceCoefficients A) P

/-- 元の単位を固定する任意の同じ延長は、同じfiberで元のnative制限写像を回収する。 -/
theorem strictBETotJointSourceNativeFiberUnit_map
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
      vertexFiberMap _ (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) =
        strictBETotJointSourceNativeFiberMap A P :=
  simplicialElementsFiberUnit_map (strictBETotJointSourceCoefficients A)
    (strictBETotJointNativeHomProjection A) (strictBETotJointSourceNativeHomMap A)
    (strictBETotJointSourceNativeHomMap_projection A) m hm hu P
end SerrePositivity.EInfinity.BarrattEccles
