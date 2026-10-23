module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexLocalComparison

/-!
概要：同じ二辺と共有頂点の cospan の局所比較は、両脚に沿って自然。
方針：同じ共有セルを指定した全局所 Hom の自然性を、そのまま両脚へ渡す。
規約：三成分と源・標的の二本の元の制限写像を保持する。
使われ方：元の二次元 Hom 作用の Segal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ cospan の最初の脚に沿う、元の局所比較の自然性。 -/
def cocartesianTwoSimplexLocalComparison_firstIso :
    FunctorIso
      ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl ≫
        cocartesianTwoSimplexLocalComparison k p q WalkingCospan.one)
      (cocartesianTwoSimplexLocalComparison k p q WalkingCospan.left ≫
        (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl) :=
  cocartesianLocalHomComparison_cellOverNaturalityIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q

/-- 同じ共有頂点を使う次の脚でも、元の局所比較は自然。 -/
def cocartesianTwoSimplexLocalComparison_secondIso :
    FunctorIso
      ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inr ≫
        cocartesianTwoSimplexLocalComparison k p q WalkingCospan.one)
      (cocartesianTwoSimplexLocalComparison k p q WalkingCospan.right ≫
        (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr) :=
  cocartesianLocalHomComparison_cellOverNaturalityIso
    (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
    (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
    (cocartesianTwoSimplexSharedCell_second k) p q

end SerrePositivity.InfinityCategories
