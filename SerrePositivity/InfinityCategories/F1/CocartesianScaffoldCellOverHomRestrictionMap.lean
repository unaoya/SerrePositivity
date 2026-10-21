module

public import SerrePositivity.InfinityCategories.F1.CocartesianCellOverHomRestrictionMap
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldLocalComparison

/-!
概要：高次単体の target cospan の両脚を、同じ共有セルの指定制限として表示する。
方針：元の cospan の二射を、任意の通常圏のセルの既存の制限に照合する。
規約：元の辺・尾部・共有頂点を保持する。
使われ方：補正比較の指定像を元の大域自然性へ結ぶ三角等式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の脚は、同じ共有セルの元の制限写像。 -/
lemma cocartesianScaffoldLocalTarget_firstMap :
    (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl =
      cocartesianCellOverHomRestrictionMap
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q := rfl

/-- 尾部への脚も、同じ共有セルの元の制限写像。 -/
lemma cocartesianScaffoldLocalTarget_secondMap :
    (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr =
      cocartesianCellOverHomRestrictionMap (scaffoldFiniteZeroVertex n)
        (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
        (cocartesianScaffoldSharedCell_tail n k) p q := rfl

end SerrePositivity.InfinityCategories
