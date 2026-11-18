module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConePrism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：元の全 cone prism を同じ定値先端から元の frame 図式への関手の射にする。
方針：区間因子の順を戻した元の全ホモトピーと、その同じ関手辺の類を使う。
規約：元の全区間族と両端を保持する。使われ方：同じ実屋根との大域三角形の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeHomotopy :
    SSet.Homotopy (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y) where
  h := (β_ (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism A X Y
  h₀ := by
    rw [← Category.assoc]
    have he : SSet.ι₀ (X := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫
        (β_ (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) := by rfl
    rw [he]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism_zero A X Y
  h₁ := by
    rw [← Category.assoc]
    have he : SSet.ι₁ (X := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫
        (β_ (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) := by rfl
    rw [he]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConePrism_one A X Y
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

def normalizedTensorConeFamilyHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y))

end SerrePositivity.ComplexLimits
