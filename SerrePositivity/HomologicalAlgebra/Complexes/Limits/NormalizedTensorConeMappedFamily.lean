module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeFamily

/-!
概要：同じ実 cone の全区間族を任意の関手で送り、既存 D(R) の元の図式へ代入する。
方針：同じホモトピーの後合成と両端の式を使い、元の半自由分解にそのまま適用する。
規約：別の導来圏模型や局所化普遍性を仮定しない。使われ方：元の実屋根との全三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeMappedHomotopy {C : SSet.{u + 1}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) ⟶ C) :
    SSet.Homotopy
      (SSet.const (F.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y ≫ F) where
  h := (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y).h ≫ F
  h₀ := by
    rw [← Category.assoc, SSet.Homotopy.h₀, SSet.const_comp]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.Homotopy.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

def normalizedTensorConeMappedFamilyHom {C : SSet.{u + 1}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (SSet.const (F.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y ≫ F) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeMappedHomotopy A X Y F))

lemma normalizedTensorElementNerveDiagram_derived :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y ≫ _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A =
      nerveMap (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  rfl

def normalizedTensorConeDerivedFamilyHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (SSet.const ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)))
      (nerveMap (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) := by
  rw [← _root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram_derived A X Y]
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeMappedFamilyHom A X Y (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)

end SerrePositivity.ComplexLimits
