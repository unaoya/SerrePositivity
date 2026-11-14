module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentProductPointedFiber
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.SmallPointedFiberNaturality

/-!
概要：点ごとの coherent 積の元の小さい全空間作用は、各 fiber で二つの fiber の積への同値。
方針：縮小の fiber 同型と厳密に可換な二射影を組にし、普遍 fiber の同値性を反映する。
規約：底は任意の小さい単体集合。使われ方：元の pullback への比較射の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌)

/-- 元の指定全空間作用を小さい fiber に制限して組にする。 -/
def coherentProductSmallFiberMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G)) b ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) b :=
  lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst F G)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap_projection _ _ _) b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd F G)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap_projection _ _ _) b)

/-- 元の小さい二射影の対は、持ち上げた普遍 fiber の同じ対と厳密に可換。 -/
lemma coherentProductSmallFiberMap_pointed :
    (SSet.uliftFunctor.{u + 1, u}).map (coherentProductSmallFiberMap F G b) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) b)).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso F b).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso G b).hom) =
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) b).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductPointedFiberMap F G b := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst F G)
            (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap_projection _ _ _) b) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso F b).hom := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        rfl
      _ = _ := by
        have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso_naturality (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) F
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex F G) b
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalFst,
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductPointedFiberMap, Category.assoc, lift_fst] using h
  · calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd F G)
            (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap_projection _ _ _) b) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso G b).hom := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        rfl
      _ = _ := by
        have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso_naturality (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) G
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex F G) b
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductTotalSnd,
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductPointedFiberMap, Category.assoc, lift_snd] using h

/-- 同じ小さい全空間作用の二つの fiber 射の対は、元の宇宙で同値。 -/
lemma coherentProductSmallFiberMap_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coherentProductSmallFiberMap F G b) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) b)).isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductPointedFiberMap_isQCatEquivalence F G b)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProduct F G) b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentProductPointedFiberMap F G b) at h
  rw [← coherentProductSmallFiberMap_pointed] at h
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G) b))).isQCatEquivalence.comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.tensor_isQCatEquivalence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso F b)).isQCatEquivalence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smallPointedFiberIso G b)).isQCatEquivalence)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan _).mp (ht.cancel_right h)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
