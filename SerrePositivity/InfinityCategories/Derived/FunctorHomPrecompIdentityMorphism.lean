module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskering
/-!
概要：元の出力模型比較を、その指定射と可換四角形で照合する。
方針：同じ全関手射の前合成と tensor 評価、元の合成比較の自然性を使う。
規約：指定比較・計算上限を変更しない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPrecomp_identity {X Y Z : SSet.{w}} (f : Y ⟶ Z) (p : X ⟶ Y) :
    functorHomPrecomp f f p (𝟙 (HomotopyCategory.mk (functorVertex f))) =
      𝟙 (HomotopyCategory.mk (functorVertex (p ≫ f))) :=
  (SSet.mapHomotopyCategory ((pre p).app Z)).map_id _
end SerrePositivity.InfinityCategories
