module

public import SerrePositivity.InfinityCategories.F1.FunctorParameterizedPrism

/-!
概要：追加パラメーター付き prism の定義域とパラメーターに関する自然性。
方針：各次数の三成分で内部 Hom の前合成と評価を計算する。
規約：単体集合の充填性は不要。
使われ方：Kerodon Remark 5.6.2.5、普遍的な変換の底変換の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：図式の定義域への前合成はパラメーター付き prism の制限になる。
方針：各次数の入力で内部 Hom の前合成を評価する。
規約：K と L の二つのパラメーターは固定する。
使われ方：Kerodon Remark 5.6.2.5、coherent な変換の普遍的な族の底変換。 -/
lemma functorParameterizedPrism_pre {K B D L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (k : D ⟶ B) :
    functorParameterizedPrism (H ≫ (pre k).app X) =
      ((K ◁ k) ▷ L) ≫ functorParameterizedPrism H := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, b⟩, l⟩
  rfl

/-- 概要：追加パラメーターの制限は prism の同じ因子での制限になる。
方針：各次数の入力で三成分を計算する。
規約：prism の因子 K と図式の定義域 B は固定する。
使われ方：Kerodon Remark 5.6.2.5、変換の空間への射による普遍的な族の制限。 -/
lemma functorParameterizedPrism_parameter {K B L M X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (i : M ⟶ L) :
    functorParameterizedPrism ((K ◁ i) ≫ H) =
      ((K ⊗ B) ◁ i) ≫ functorParameterizedPrism H := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, b⟩, l⟩
  rfl

end SerrePositivity.InfinityCategories
