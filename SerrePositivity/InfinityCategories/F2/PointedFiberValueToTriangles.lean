module

public import SerrePositivity.InfinityCategories.F2.PointedFiberValueToRightInverse
public import SerrePositivity.InfinityCategories.F2.PointedValueRightTriangleReindex

/-!
概要：元の固定値射と同じ右 Hom の逆射の二三角恒等式を、全係数で証明する。
方針：同じ元の頂点等式を消去し、指定単位・余単位の三角恒等式へ戻す。
規約：元の実 fiber・固定値と指定同型を保持。使われ方：四因子境界式の単位因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z')

/-- 元の実 fiber から固定値へ、同じ指定単位と余単位の像は厳密に一致する。 -/
lemma pointedFiberValueTo_triangle :
    (pointedFiberValueToUnitIso hz).postcomp (pointedFiberValueTo hz) =
      (pointedFiberValueToCounitIso hz).precomp (pointedFiberValueTo hz) := by
  cases hz
  exact pointedValueRightComparison_triangle z

/-- 元の固定値から右 Hom で戻すときも、同じ指定単位と余単位の像は一致する。 -/
lemma pointedFiberValueTo_triangle_inverse :
    (pointedFiberValueToUnitIso hz).precomp (pointedFiberValueFrom hz) =
      (pointedFiberValueToCounitIso hz).postcomp (pointedFiberValueFrom hz) := by
  cases hz
  exact pointedValueRightComparison_triangle_inverse z

/-- 任意の全実 fiber 係数で、単位の値像は同じ固定値上の指定余単位となる。 -/
lemma pointedFiberValueTo_triangle_at {P : SSet.{u + 1}}
    (x : P ⟶ vertexFiber pointedSpaceProjection z) :
    ((pointedFiberValueToUnitIso hz).precomp x).postcomp (pointedFiberValueTo hz) =
      (pointedFiberValueToCounitIso hz).precomp (x ≫ pointedFiberValueTo hz) := by
  cases hz
  exact pointedValueRightComparison_triangle_at z x

/-- 任意の全固定値係数で、戻した単位は同じ指定余単位の右 Hom への像となる。 -/
lemma pointedFiberValueTo_triangle_inverse_at {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj) :
    (pointedFiberValueToUnitIso hz).precomp (x ≫ pointedFiberValueFrom hz) =
      ((pointedFiberValueToCounitIso hz).precomp x).postcomp (pointedFiberValueFrom hz) := by
  cases hz
  exact pointedValueRightComparison_triangle_inverse_at z x

end SerrePositivity.InfinityCategories.F2
