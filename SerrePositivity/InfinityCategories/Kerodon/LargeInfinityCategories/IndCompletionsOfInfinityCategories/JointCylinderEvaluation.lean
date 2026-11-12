module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeEquivalenceCylinder

/-!
概要：元の関手円柱を共同評価し、時刻を右因子に保持する。
方針：元の共同評価の変数だけを交換し、全写像として制限と両端を回収する。
規約：新しい辺や比較を選ばず、元の全係数を保つ。
使われ方：指定始点評価を固定した全余錐の相対延長。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：形状と時刻の変数を交換する同じ直積の射。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
def cylinderEvaluationSwitch (A K I : SSet.{u}) : (A ⊗ K) ⊗ I ⟶ (A ⊗ I) ⊗ K :=
  (α_ A K I).hom ≫ (A ◁ (β_ K I).hom) ≫ (α_ A I K).inv
/-- 概要：元の関手円柱を共同評価した同じ実円柱。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
def jointCylinderEvaluation {A K I X : SSet.{u}} (U : A ⊗ I ⟶ (ihom K).obj X) :
    (A ⊗ K) ⊗ I ⟶ X := cylinderEvaluationSwitch A K I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism U
/-- 概要：共同評価円柱の両端を元の射の共同評価へ戻す。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
lemma jointCylinderEvaluation_endpoint
    {A K X : SSet.{u}} (U : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ (ihom K).obj X) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint (A ⊗ K) b ≫ jointCylinderEvaluation U =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ≫ U) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism_restrict]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint (A ⊗ K) b ≫ cylinderEvaluationSwitch A K _ ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism U = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism U
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint (A ⊗ K) b ≫ cylinderEvaluationSwitch A K _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ▷ K) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a, k⟩
    rfl
  rw [← Category.assoc, h]
/-- 概要：係数制限は元の共同評価と厳密に可換。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
lemma jointCylinderEvaluation_restrict
    {A B K I X : SSet.{u}} (U : A ⊗ I ⟶ (ihom K).obj X) (f : B ⟶ A) :
    ((f ▷ K) ▷ I) ≫ jointCylinderEvaluation U =
      jointCylinderEvaluation ((f ▷ I) ≫ U) := by
  have hs : ((f ▷ K) ▷ I) ≫ cylinderEvaluationSwitch A K I =
      cylinderEvaluationSwitch B K I ≫ ((f ▷ I) ▷ K) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, k⟩, i⟩
    rfl
  simp only [jointCylinderEvaluation]
  rw [← Category.assoc, hs, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism_restrict]
/-- 概要：定値の関手族の共同評価も時刻に依存しない。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
lemma jointCylinderEvaluation_constant
    {A K I X : SSet.{u}} (c : A ⟶ (ihom K).obj X) :
    jointCylinderEvaluation (fst A I ≫ c) =
      fst (A ⊗ K) I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism c := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, k⟩, i⟩
  rfl
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
