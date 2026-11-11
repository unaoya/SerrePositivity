module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitPointwise
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitParameterApex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FlipPostcomposition

/-!
概要：選んだ普遍余錐族の像を、像の元の図式族を底とする全余錐として保持する。
方針：元の全余錐へ後合成し、変数交換の自然性で底を揃える。
規約：同じ全余錐の像を保持する。
使われ方：有限余積の指定比較を全パラメータで構成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：選んだ普遍余錐族の像を同じ像の図式族の全余錐とする。
方針：全余錐を後合成し、底の交換の公式を使う。
規約：元の像の全射を保持する。
使われ方：余極限関手の全比較の標的。 -/
def chosenColimitImageCocone {K A X Y : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (U : A ⟶ (ihom K).obj X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K Y (U ≫ (ihom K).map q)) where
  val := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U).val ≫ (ihom A).map q
  property := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U).property]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flip_postcomposition U q).symm

/-- 概要：像の全余錐族の頂点は元の余極限関手の像の全関手頂点。
方針：元の余錐族の頂点評価を後合成で写す。
規約：同じ指定頂点の像を使う。
使われ方：全比較の標的関手の同定。 -/
lemma chosenColimitImageCocone_vertex {K A X Y : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (U : A ⟶ (ihom K).obj X) (q : X ⟶ Y) :
    (chosenColimitImageCocone hX U q).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor K X hX) ≫ q) := by
  change ((ihom A).map q).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_vertex]
  rfl

/-- 概要：像の全余錐族の評価は、元の各余錐の像そのもの。
方針：評価と標的の後合成の交換を使う。
規約：全余錐の射を厳密に比較する。
使われ方：Yoneda 像上の有限余積保存から全比較を判定する。 -/
lemma chosenColimitImageCocone_evaluate_val {K A X Y : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (U : A ⟶ (ihom K).obj X) (q : X ⟶ Y)
    (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone (chosenColimitImageCocone hX U q) a).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U) a)).val := by
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
