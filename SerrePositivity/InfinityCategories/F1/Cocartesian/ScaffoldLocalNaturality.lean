module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldLocalComparison

/-!
概要：同じ最初の辺と尾部と共有頂点の cospan の局所比較は、両脚に沿って自然。
方針：同じ共有セルを指定した全局所 Hom の自然性を、そのまま両脚へ渡す。
規約：三成分と源・標的の二本の元の制限写像を保持する。
使われ方：元の高次元 Hom 作用の Segal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ cospan の最初の脚に沿う、元の局所比較の自然性。 -/
def cocartesianScaffoldLocalComparison_firstIso :
    FunctorIso
      ((cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inl ≫
        cocartesianScaffoldLocalComparison n k p q WalkingCospan.one)
      (cocartesianScaffoldLocalComparison n k p q WalkingCospan.left ≫
        (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl) :=
  cocartesianLocalHomComparison_cellOverNaturalityIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q

/-- 同じ共有頂点を使う次の脚でも、元の局所比較は自然。 -/
def cocartesianScaffoldLocalComparison_secondIso :
    FunctorIso
      ((cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inr ≫
        cocartesianScaffoldLocalComparison n k p q WalkingCospan.one)
      (cocartesianScaffoldLocalComparison n k p q WalkingCospan.right ≫
        (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr) :=
  cocartesianLocalHomComparison_cellOverNaturalityIso
    (scaffoldFiniteZeroVertex n)
    (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
    (cocartesianScaffoldSharedCell_tail n k) p q

end SerrePositivity.InfinityCategories
