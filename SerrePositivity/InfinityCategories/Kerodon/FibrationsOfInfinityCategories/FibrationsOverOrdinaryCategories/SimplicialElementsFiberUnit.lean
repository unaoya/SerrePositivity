module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckFiberUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsClassification

/-!
概要：元の全要素圏の同じ置換単位の指定fiberへの制限を、同じGrothendieck表示で検査する。
方針：同じ二つの表示の厳密な往復と元の単位の自然性で、R03gの同じ写像へ移す。
規約：元の包含・置換・単位を保ち、別のfiber同値を選ばない。
使われ方：元のnative Hom写像のfiberの同値性とroof比較の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ元の全要素射影の元の連続left-fibration置換。 -/
abbrev simplicialElementsReplacement : Over (nerve I) :=
  (continuousLeftFibrationReplacement (nerve I)).obj
    (Over.mk (nerveMap (simplicialTotalElementsProjection F)))

/-- 同じstrictなGrothendieck表示から元の全要素圏へ戻した指定fiber包含。 -/
def simplicialElementsFiberInclusion (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ nerve (SimplicialTotalElements F) :=
  grothendieckFiberInclusion (simplicialElementsCatDiagram F) i ≫
    nerveMap (simplicialElementsGrothendieckForward F)

/-- 同じ指定fiber包含の元の底への射影。 -/
theorem simplicialElementsFiberInclusion_projection (i : I) :
    simplicialElementsFiberInclusion F i ≫ nerveMap (simplicialTotalElementsProjection F) =
      SSet.const (nerveVertex i) := by
  have hp : nerveMap (simplicialElementsGrothendieckForward F) ≫
      nerveMap (simplicialTotalElementsProjection F) =
        nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F)) := by
    change nerveMap (simplicialElementsGrothendieckForward F ⋙ simplicialTotalElementsProjection F) = _
    rw [simplicialElementsGrothendieckForward_projection]
  rw [simplicialElementsFiberInclusion, Category.assoc, hp, grothendieckFiberInclusion_projection]

/-- 同じ元の全要素圏の置換単位を、同じ指定頂点のfiberへ制限する。 -/
def simplicialElementsFiberUnit (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶
      vertexFiber (simplicialElementsReplacement F).hom (nerveVertex i) :=
  vertexFiberLift _ _
    (simplicialElementsFiberInclusion F i ≫
      ((continuousLeftFibrationReplacementUnit (nerve I)).app
        (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left) (by
      rw [Category.assoc, ((continuousLeftFibrationReplacementUnit (nerve I)).app
        (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).w]
      exact simplicialElementsFiberInclusion_projection F i)

/-- 同じ二つの表示の元の置換比較を、同じ指定fiberへ制限する。 -/
def simplicialElementsFiberComparison (i : I) :
    vertexFiber (simplicialElementsReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (grothendieckReplacement (simplicialElementsCatDiagram F)).hom (nerveVertex i) :=
  vertexFiberMap _ _ (simplicialElementsGrothendieckReplacementMap F).left
    (simplicialElementsGrothendieckReplacementMap F).w (nerveVertex i)

/-- 同じ元の単位のfiberへの制限は、元のGrothendieck単位と厳密に両立。 -/
theorem simplicialElementsFiberUnit_comparison (i : I) :
    simplicialElementsFiberUnit F i ≫ simplicialElementsFiberComparison F i =
      grothendieckFiberUnit (simplicialElementsCatDiagram F) i := by
  apply vertexFiber_hom_ext
    (grothendieckReplacement (simplicialElementsCatDiagram F)).hom (nerveVertex i)
  rw [Category.assoc, simplicialElementsFiberComparison, vertexFiberMap_ι,
    ← Category.assoc, simplicialElementsFiberUnit, vertexFiberLift_ι]
  rw [Category.assoc, simplicialElementsGrothendieckReplacementMap_unit F]
  rw [grothendieckFiberUnit, vertexFiberLift_ι]
  change (grothendieckFiberInclusion (simplicialElementsCatDiagram F) i ≫
    nerveMap (simplicialElementsGrothendieckForward F)) ≫
      (nerveMap (simplicialElementsGrothendieckInverse F) ≫ _) = _
  have hi : nerveMap (simplicialElementsGrothendieckForward F) ≫
      nerveMap (simplicialElementsGrothendieckInverse F) = 𝟙 _ := rfl
  simp only [Category.assoc]
  rw [← Category.assoc (nerveMap (simplicialElementsGrothendieckForward F))
    (nerveMap (simplicialElementsGrothendieckInverse F)), hi, Category.id_comp]

/-- 同じ元の置換比較のfiberへの制限は同値。 -/
theorem simplicialElementsFiberComparison_isQCatEquivalence (i : I) :
    IsQCatEquivalence (simplicialElementsFiberComparison F i) :=
  SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    _ _ (simplicialElementsGrothendieckReplacementMap F).left
    (simplicialElementsGrothendieckReplacementMap F).w
    (simplicialElementsGrothendieckReplacementMap_isPrecompositionEquivalence F) (nerveVertex i)

/-- 元の全要素圏の同じ置換単位の指定fiber制限へ、R03gの弱同値判定を移す。 -/
theorem simplicialElementsFiberUnit_isWeakHomotopyEquivalence (i : I) :
    IsWeakHomotopyEquivalence (simplicialElementsFiberUnit F i) := by
  have hc := (simplicialElementsFiberComparison_isQCatEquivalence F i).isWeakHomotopyEquivalence
  have h := grothendieckFiberUnit_isWeakHomotopyEquivalence (simplicialElementsCatDiagram F) i
  rw [← simplicialElementsFiberUnit_comparison F i] at h
  exact hc.cancel_right h
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
