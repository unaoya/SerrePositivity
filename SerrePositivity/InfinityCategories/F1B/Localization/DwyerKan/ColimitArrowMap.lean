module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitIdentityPoint

/-!
# 元の任意の射から hammock への一定の単体写像

概要：元の射の同じ一定単体と標準射を単体写像に束ねる。
方針：元の全単体作用素への自然性を使う。
規約：元の射の恒等性や生成性を仮定しない。
使われ方：元の非指定生成矢の像を指定した自由積の普遍性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C}

def arrowMap (p : X ⟶ Y) : 𝟙_ SSet.{max u v} ⟶ colimitGraph W X Y where
  app n := ↾fun _ => arrowPoint W p n
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro k
    exact (arrowPoint_simplex W θ p).symm

lemma arrowMap_identity (X : C) : arrowMap W (𝟙 X) = colimitUnit W X := by
  ext n p
  exact arrowPoint_identity W X n

end SerrePositivity.EInfinity.Hammock
