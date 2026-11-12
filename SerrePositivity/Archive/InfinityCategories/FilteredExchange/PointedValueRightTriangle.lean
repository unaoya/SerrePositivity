module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.InverseComparisonCounitSecondTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedValueRightInverse

/-!
概要：元の pointed 値比較の指定単位と指定余単位の三角恒等式を証明する。
方針：既存の余単位を、同じ逆比較と指定単位からの構成へ厳密に戻す。
規約：元の値射・右 Hom・単位・余単位を保持。使われ方：三辺の値比較の指定因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 既存の指定余単位は、元の逆比較と指定単位からの同じ構成そのもの。 -/
lemma pointedValueRightComparison_counitIso_eq_inverseComparisonCounit
    (s : SpaceInfinity.{u} _⦋0⦌) :
    pointedValueRightComparison_counitIso s =
      inverseComparisonCounit (pointedSpaceFiberValueEquivalence s)
        (pointedValueRightComparison s) (pointedValueRightComparison_unitIso s) := rfl

/-- 元の値射への指定単位の像と、元の値射で評価した指定余単位は厳密に一致する。 -/
lemma pointedValueRightComparison_triangle (s : SpaceInfinity.{u} _⦋0⦌) :
    (pointedValueRightComparison_unitIso s).postcomp (pointedSpaceFiberValueEquivalence s).hom =
      (pointedValueRightComparison_counitIso s).precomp
        (pointedSpaceFiberValueEquivalence s).hom := by
  rw [pointedValueRightComparison_counitIso_eq_inverseComparisonCounit]
  exact inverseComparisonCounit_triangle (pointedSpaceFiberValueEquivalence s)
    (pointedValueRightComparison s) (pointedValueRightComparison_unitIso s)

/-- 元の右 Hom の逆射上でも、同じ指定単位と指定余単位の像は厳密に一致する。 -/
lemma pointedValueRightComparison_triangle_inverse (s : SpaceInfinity.{u} _⦋0⦌) :
    (pointedValueRightComparison_unitIso s).precomp (pointedValueRightComparison s) =
      (pointedValueRightComparison_counitIso s).postcomp (pointedValueRightComparison s) := by
  rw [pointedValueRightComparison_counitIso_eq_inverseComparisonCounit]
  exact inverseComparisonCounit_triangle_inverse (pointedSpaceFiberValueEquivalence s)
    (pointedValueRightComparison s) (pointedValueRightComparison_unitIso s)

end SerrePositivity.InfinityCategories.F2
