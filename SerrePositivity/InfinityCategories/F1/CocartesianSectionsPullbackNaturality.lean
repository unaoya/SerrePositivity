module

public import SerrePositivity.InfinityCategories.F1.CocartesianSectionsPullbackIso
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSectionsPrecomposition

/-!
概要：底変換の section 同型は、元の始域の前合成と厳密に可換。
方針：全部分複体と相対 fiber の値へ戻し、元の関手の前合成・後合成を照合する。
規約：全高次で同じ相対作用を使う。
使われ方：strict transport の底変換比較を通常の自然変換に束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- section の pullback 同型は、底上の元の始域による制限と厳密に可換。 -/
lemma cocartesianSectionsPullbackIso_pre {P E A B : SSet.{u}} [Quasicategory B]
    {p : E ⟶ B} [CocartesianFibration p] {i : P ⟶ E} {r : P ⟶ A} {f : A ⟶ B}
    (hs : IsPullback i r p f) {a b : Over A} (j : a ⟶ b) :
    kanCocartesianSectionsPre r j ≫
      (cocartesianSectionsPullbackIso hs a.hom (a.hom ≫ f) rfl).hom =
    (cocartesianSectionsPullbackIso hs b.hom (b.hom ≫ f) rfl).hom ≫
      kanCocartesianSectionsPre p ((Over.map f).map j) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
