module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitIdentityPoint

/-!
# 元の任意の射から hammock への一定の単体写像

概要：元の射の同じ一定単体と標準射を単体写像に束ねる。
方針：元の全単体作用素への自然性を使う。
規約：元の射の恒等性や生成性を仮定しない。
使われ方：元の非指定生成矢の像を指定した自由積の普遍性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C}

def arrowMap (p : X ⟶ Y) : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y where
  app n := ↾fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W p n
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro k
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_simplex W θ p).symm

lemma arrowMap_identity (X : C) : arrowMap W (𝟙 X) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X := by
  ext n p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity W X n

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
