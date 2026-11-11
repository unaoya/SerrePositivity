module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSimplexPointedStart
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：任意の元の全単体を定値図式へ移した底を、同じ全単体の係数射影へ戻す。
方針：定値図式の uncurry と直積交換後の射影を任意の実射に対して計算する。
規約：全次元・全係数・元の実射を保持。使われ方：元の二単体上の raw 普遍三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の任意の全単体の定値図式表示の底は、係数射影後の同じ実射そのもの。 -/
lemma functorSimplexDiagram_constant_base {P B X K : SSet.{u}} (p : K ⟶ B) (e : P ⟶ X) :
    (P ◁ p) ≫ functorSimplexDiagram (e ≫ constantDiagram B X) = fst P K ≫ e := by
  unfold functorSimplexDiagram
  rw [uncurry_comp_constantDiagram]
  have hn : (P ◁ p) ≫ (β_ P B).hom ≫ snd B P = fst P K := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  simpa only [Category.assoc] using congrArg (fun f => f ≫ e) hn

end SerrePositivity.InfinityCategories.F2
