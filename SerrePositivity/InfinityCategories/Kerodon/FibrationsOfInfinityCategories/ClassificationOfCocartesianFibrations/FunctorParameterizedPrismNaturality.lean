module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism

/-!
概要：追加パラメーター付き prism の定義域とパラメーターに関する自然性。
方針：各次数の三成分で内部 Hom の前合成と評価を計算する。
規約：単体集合の充填性は不要。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、普遍的な変換の底変換の計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：図式の定義域への前合成はパラメーター付き prism の制限になる。
方針：各次数の入力で内部 Hom の前合成を評価する。
規約：K と L の二つのパラメーターは固定する。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、coherent な変換の普遍的な族の底変換。 -/
lemma functorParameterizedPrism_pre {K B D L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (H ≫ (pre k).app X) =
      ((K ◁ k) ▷ L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, b⟩, l⟩
  rfl

/-- 概要：追加パラメーターの制限は prism の同じ因子での制限になる。
方針：各次数の入力で三成分を計算する。
規約：prism の因子 K と図式の定義域 B は固定する。
使われ方：Kerodon §5.6.2（Tag 026H）、変換の空間への射による普遍的な族の制限。 -/
lemma functorParameterizedPrism_parameter {K B L M X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (i : M ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism ((K ◁ i) ≫ H) =
      ((K ⊗ B) ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, b⟩, l⟩
  rfl

/-- 概要：prism の端点制限は追加パラメーターの制限と可換。
方針：三成分の積を計算する。
規約：両方の端点を扱う。
使われ方：普遍的な lift の任意の族への制限。 -/
lemma prismEndpoint_parameter_naturality {K L : SSet.{u}} (E : SSet.{u})
    (i : Fin 2) (t : K ⟶ L) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i E ▷ K) ≫ ((Δ[1] ⊗ E) ◁ t) =
      (E ◁ t) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i E ▷ L) := by
  apply SSet.hom_ext
  intro n
  rfl


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
