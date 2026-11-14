module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDiagram
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorPinchedIso
public import SerrePositivity.EInfinity.FrameHom.FrameIndexAugmentation
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
概要：元の全正規化 Hom 単体図式から同じ pinched Hom への大域族を構成する。
方針：要素圏の明示的な宇宙比較と元の終端 augmentation・実 Hom 同型を合成する。
規約：同じ全単体・全作用素を保つ。
使われ方：全自然変換からの実屋根と、元の Hom 自身の大域評価族との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementLiftMap : normalizedTensorElementIndex A X Y ⥤
    ULiftHom.{u + 1} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y).Elements)ᵒᵖ) :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙ ULiftHom.up

def normalizedTensorElementLiftNerveMap : nerve (normalizedTensorElementIndex A X Y) ⟶
    nerve (ULiftHom.{u + 1}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y).Elements)ᵒᵖ)) where
  app _ := ↾fun Γ => Γ ⋙ normalizedTensorElementLiftMap A X Y
  naturality _ _ _ := rfl

def normalizedTensorElementParameterMap : nerve (normalizedTensorElementIndex A X Y) ⟶
    SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y) :=
  normalizedTensorElementLiftNerveMap A X Y ≫
    FrameHom.SimplexTerminalNerve.liftedAugmentation.{u, u + 1}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y)

def normalizedTensorElementPinchedMap : nerve (normalizedTensorElementIndex A X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y :=
  normalizedTensorElementParameterMap A X Y ≫ (normalizedTensorPinchedIso A X Y).hom

def normalizedTensorElementDerivedPinchedMap : nerve (normalizedTensorElementIndex A X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
      ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
      ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) :=
  normalizedTensorElementPinchedMap A X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (complexSemifreeResolutionInfinity A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)

end SerrePositivity.EInfinity.ComplexLimits
