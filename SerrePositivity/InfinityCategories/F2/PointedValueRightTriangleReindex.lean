module

public import SerrePositivity.InfinityCategories.F2.PointedValueRightTriangle
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTriangleReindex

/-!
概要：同じ元の値比較の二つの三角恒等式を、任意の全係数で厳密に評価する。
方針：指定三角恒等式の前合成と、前後合成の交換・結合を使う。
規約：係数は任意の単体集合。使われ方：全 pointed 族の値と右 Hom の単位因子の照合。
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
variable (s : SpaceInfinity.{u} _⦋0⦌)
local notation "V" => QCatEquivalence.hom (pointedSpaceFiberValueEquivalence s)
local notation "R" => pointedValueRightComparison s

/-- 元の全 fiber 係数での単位の値像は、元の値係数での指定余単位に等しい。 -/
lemma pointedValueRightComparison_triangle_at {P : SSet.{u + 1}}
    (x : P ⟶ vertexFiber pointedSpaceProjection s) :
    ((pointedValueRightComparison_unitIso s).precomp x).postcomp V =
      (pointedValueRightComparison_counitIso s).precomp (x ≫ V) :=
  functorIso_triangle_precomp V R (pointedValueRightComparison_unitIso s)
    (pointedValueRightComparison_counitIso s) (pointedValueRightComparison_triangle s) x

/-- 元の右 Hom の全値係数を戻した単位は、同じ指定余単位の右 Hom への像に等しい。 -/
lemma pointedValueRightComparison_triangle_inverse_at {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj) :
    (pointedValueRightComparison_unitIso s).precomp (x ≫ R) =
      ((pointedValueRightComparison_counitIso s).precomp x).postcomp R :=
  functorIso_triangle_inverse_precomp V R (pointedValueRightComparison_unitIso s)
    (pointedValueRightComparison_counitIso s) (pointedValueRightComparison_triangle_inverse s) x

end SerrePositivity.InfinityCategories.F2
