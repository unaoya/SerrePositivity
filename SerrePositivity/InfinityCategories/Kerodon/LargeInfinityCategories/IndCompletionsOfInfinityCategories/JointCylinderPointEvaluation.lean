module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.JointCylinderEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：共同評価の頂点制限を、元の指定頂点での評価へ戻す。
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
/-- 概要：共同評価円柱の指定頂点制限は元の評価そのもの。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
lemma jointCylinderEvaluation_at_point
    {A K I X : SSet.{u}} (U : A ⊗ I ⟶ (ihom K).obj X) (k : K _⦋0⦌) :
    ((A ◁ SSet.yonedaEquiv.symm k) ▷ I) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.jointCylinderEvaluation U =
      (fst A (Δ[0] : SSet.{u}) ▷ I) ≫ U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k := by
  rw [SSet.yonedaEquiv_symm_zero]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, i⟩
  change (U.app n (a, i)).app n (𝟙 n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n.unop.len) = _
  rfl
/-- 概要：元の関手族の指定頂点制限は元の評価そのもの。
方針：同じ共同評価を計算。規約：全係数と指定値を保持。使われ方：相対境界への移送。 -/
lemma functorFamilyPrism_at_point
    {A K X : SSet.{u}} (c : A ⟶ (ihom K).obj X) (k : K _⦋0⦌) :
    (A ◁ SSet.yonedaEquiv.symm k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism c =
      fst A (Δ[0] : SSet.{u}) ≫ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k := by
  rw [SSet.yonedaEquiv_symm_zero]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  change (c.app n a).app n (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n.unop.len) = _
  rfl
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
