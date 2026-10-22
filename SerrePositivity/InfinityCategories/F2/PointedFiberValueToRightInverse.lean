module

public import SerrePositivity.InfinityCategories.F2.PointedValueRightTriangle
public import SerrePositivity.InfinityCategories.F2.CoherentTotalSourceValueTo

/-!
概要：指定した固定値への元の射を、同じ右 Hom の逆射・指定単位・余単位と共に保つ。
方針：元の頂点等式だけを消去し、既存の三つの指定構成を移す。
規約：元の値射を変更しない。使われ方：実三 fiber の四因子境界式の値照合。
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

/-- 指定した同じ固定値から元の実 fiber へ、元の右 Hom の恒等点輸送で戻す。 -/
def pointedFiberValueFrom {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj ⟶
      vertexFiber pointedSpaceProjection z := by
  subst z'
  exact pointedValueRightComparison z

/-- 固定値からの元の逆射は、同じ右 Hom の逆射と実 fiber の表示変更の合成。 -/
lemma pointedFiberValueFrom_eq_cast {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    pointedFiberValueFrom hz = pointedValueRightComparison z' ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) hz.symm) := by
  cases hz
  simp only [pointedFiberValueFrom, eqToHom_refl, Category.comp_id]

/-- 元の固定値射と右 Hom の逆射の合成に対する、元の実 fiber 上の同じ指定単位。 -/
def pointedFiberValueToUnitIso {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    FunctorIso (pointedFiberValueTo hz ≫ pointedFiberValueFrom hz)
      (𝟙 (vertexFiber pointedSpaceProjection z)) := by
  subst z'
  exact pointedValueRightComparison_unitIso z

/-- 同じ逆射と固定値射の合成に対する、同じ元の固定値上の指定余単位。 -/
def pointedFiberValueToCounitIso {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    FunctorIso (pointedFiberValueFrom hz ≫ pointedFiberValueTo hz)
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj)) := by
  subst z'
  exact pointedValueRightComparison_counitIso z

/-- 元の固定値射を、同じ右 Hom の逆射と元の指定単位・余単位を持つ同値に束ねる。 -/
def pointedFiberValueToRightEquivalence {z z' : SpaceInfinity.{u} _⦋0⦌} (hz : z = z') :
    QCatEquivalence (vertexFiber pointedSpaceProjection z)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z').obj) where
  hom := pointedFiberValueTo hz
  inv := pointedFiberValueFrom hz
  homInvIso := pointedFiberValueToUnitIso hz
  invHomIso := pointedFiberValueToCounitIso hz

end SerrePositivity.InfinityCategories.F2
