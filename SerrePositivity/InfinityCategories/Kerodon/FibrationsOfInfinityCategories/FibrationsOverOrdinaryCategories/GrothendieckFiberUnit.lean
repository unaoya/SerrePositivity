module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanClassification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanSourceReplacement

/-!
概要：元のGrothendieck置換単位を、同じ係数の指定fiberへ制限する。
方針：元のstrictなweighted nerve同型と定値fiber包含を通して元の単位を使う。
規約：同じ単位・比較射・全単体を保持する。
使われ方：BEの元の全要素圏の置換fiberと元のroof比較の照合。
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
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 同じ元のGrothendieck射影の元の連続left-fibration置換。 -/
abbrev grothendieckReplacement : Over (nerve I) :=
  (continuousLeftFibrationReplacement (nerve I)).obj
    (Over.mk (nerveMap (Grothendieck.forget F)))

/-- 元のstrictなweighted nerve同型で表した同じ定値fiberの包含。 -/
def grothendieckFiberInclusion (i : I) : nerve (F.obj i) ⟶ nerve (Grothendieck F) :=
  weightedNerveConstantLift (F ⋙ nerveFunctor) i ≫ (grothendieckWeightedNerveIso F).inv

/-- 同じfiber包含の元の底への射影。 -/
theorem grothendieckFiberInclusion_projection (i : I) :
    grothendieckFiberInclusion F i ≫ nerveMap (Grothendieck.forget F) = SSet.const (nerveVertex i) := by
  rw [grothendieckFiberInclusion, Category.assoc, ← grothendieckWeightedNerveIso_projection F,
    Iso.inv_hom_id_assoc, weightedNerveConstantLift_projection]

/-- 同じ元の単位を、指定された同じ底のfiberへ制限する。 -/
def grothendieckFiberUnit (i : I) :
    nerve (F.obj i) ⟶ vertexFiber (grothendieckReplacement F).hom (nerveVertex i) :=
  vertexFiberLift _ _
    (grothendieckFiberInclusion F i ≫
      ((continuousLeftFibrationReplacementUnit (nerve I)).app
        (Over.mk (nerveMap (Grothendieck.forget F)))).left) (by
      rw [Category.assoc, ((continuousLeftFibrationReplacementUnit (nerve I)).app
        (Over.mk (nerveMap (Grothendieck.forget F)))).w]
      exact grothendieckFiberInclusion_projection F i)
/-- 元の同じ全Kan比較の、指定された同じfiberへの制限。 -/
def grothendieckFiberComparison (i : I) :
    vertexFiber (grothendieckReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (weightedNerveProjection (grothendieckKanCoefficients F)) (nerveVertex i) :=
  vertexFiberMap _ _ (grothendieckKanCoefficientComparison F)
    (grothendieckKanCoefficientComparison_projection F) (nerveVertex i)

/-- 同じ単位のfiber制限と同じKan比較の合成は、元の係数単位そのもの。 -/
theorem grothendieckFiberUnit_comparison (i : I) :
    grothendieckFiberUnit F i ≫ grothendieckFiberComparison F i =
      (grothendieckKanCoefficientUnit F).app i ≫
        weightedNerveFiberMap (grothendieckKanCoefficients F) i := by
  apply vertexFiber_hom_ext (weightedNerveProjection (grothendieckKanCoefficients F)) (nerveVertex i)
  rw [Category.assoc, grothendieckFiberComparison, vertexFiberMap_ι,
    ← Category.assoc, grothendieckFiberUnit, vertexFiberLift_ι]
  rw [Category.assoc, grothendieckKanCoefficientComparison_unit F]
  change (weightedNerveConstantLift (F ⋙ nerveFunctor) i ≫
    (grothendieckWeightedNerveIso F).inv) ≫
      (grothWeightedNerveForward F ≫ weightedNerveMap (grothendieckKanCoefficientUnit F)) = _
  change (weightedNerveConstantLift (F ⋙ nerveFunctor) i ≫
    (grothendieckWeightedNerveIso F).inv) ≫
      ((grothendieckWeightedNerveIso F).hom ≫ weightedNerveMap (grothendieckKanCoefficientUnit F)) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change weightedNerveConstantLift (F ⋙ nerveFunctor) i ≫
    weightedNerveMap (grothendieckKanCoefficientUnit F) =
      (grothendieckKanCoefficientUnit F).app i ≫
        weightedNerveConstantLift (grothendieckKanCoefficients F) i
  exact weightedNerveConstantLift_map _ _
local instance grothendieckFiberCoefficientsKan :
    ∀ i, KanComplex ((grothendieckKanCoefficients F).obj i) := fun i => by
  change KanComplex (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj
    (nerve (F.obj i)))
  infer_instance
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の全Kan比較の前合成同値性を、同じfiberの同値へ制限する。 -/
theorem grothendieckFiberComparison_isQCatEquivalence (i : I) :
    IsQCatEquivalence (grothendieckFiberComparison F i) :=
  SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    _ _ (grothendieckKanCoefficientComparison F)
    (grothendieckKanCoefficientComparison_projection F)
    (grothendieckKanCoefficientComparison_isPrecompositionEquivalence F) (nerveVertex i)

/-- R03g：同じ元のGrothendieck置換単位の指定fiberへの制限は弱同値。 -/
theorem grothendieckFiberUnit_isWeakHomotopyEquivalence (i : I) :
    IsWeakHomotopyEquivalence (grothendieckFiberUnit F i) := by
  have hc := (grothendieckFiberComparison_isQCatEquivalence F i).isWeakHomotopyEquivalence
  have hu : IsWeakHomotopyEquivalence ((grothendieckKanCoefficientUnit F).app i) := by
    change IsWeakHomotopyEquivalence
      (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
        (nerve (F.obj i)))
    intro K hK
    exact (homotopyEquivalence_pre_of_anodyne _
      (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _) K).mapPiZero_bijective
  have hv : IsWeakHomotopyEquivalence (weightedNerveFiberMap (grothendieckKanCoefficients F) i) :=
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
      (asIso (weightedNerveFiberMap (grothendieckKanCoefficients F) i))).isQCatEquivalence.isWeakHomotopyEquivalence
  have h := hu.comp hv
  rw [← grothendieckFiberUnit_comparison F i] at h
  exact hc.cancel_right h
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
