module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberUnit

/-!
概要：元の全要素圏から底上の全写像を、同じ元のfiber包含へ制限する。
方針：元の単位を固定した延長の三角形を、その同じfiberへの制限へ移す。
規約：充填性や同値性を仮定せず、元の写像の厳密な等式だけを記録する。
使われ方：同じnative Hom比較射のfiberを元の全要素上の実射へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 元の底上の全写像を、同じ指定fiber包含へ制限する。 -/
def simplicialElementsFiberMap {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F)) (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ vertexFiber p (nerveVertex i) :=
  vertexFiberLift _ _ (simplicialElementsFiberInclusion F i ≫ h) (by
    rw [Category.assoc, hh, simplicialElementsFiberInclusion_projection])

/-- 元の単位を固定する同じ延長は、同じfiberでも元の全要素上の写像を回収する。 -/
theorem simplicialElementsFiberUnit_map {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F))
    (m : (simplicialElementsReplacement F).left ⟶ E)
    (hm : m ≫ p = (simplicialElementsReplacement F).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left ≫ m = h) (i : I) :
    simplicialElementsFiberUnit F i ≫ vertexFiberMap _ p m hm (nerveVertex i) =
      simplicialElementsFiberMap F p h hh i := by
  apply vertexFiber_hom_ext p (nerveVertex i)
  rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, simplicialElementsFiberUnit,
    vertexFiberLift_ι, Category.assoc, hu, simplicialElementsFiberMap, vertexFiberLift_ι]
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
