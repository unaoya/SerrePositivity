module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedRightFamilyEvaluationActionFactor
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueFamilyRightUnit

/-!
概要：元の余単位の全係数成分を全右 Hom の指定正方形へ代入し、元の単位輸送へ戻す。
方針：同じ余単位による動く点同型と、元の第二三角恒等式を使う。
規約：元の単位・余単位と全族比較を保持。使われ方：元の値比較の三因子の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "a" => pointedValueFamilyTargetCounitIso K x
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K))
local notation "q" => x ≫ pointedRightFiberComparison K
local notation "E" => FiberTransportFamily.endpoint (parametrizedFiberTransportFamily
  pointedSpaceProjection (spaceInfinityVertex K) (spaceInfinityVertex L))

/-- 同じ余単位の評価像と全右 Hom 比較の合成は、元の単位輸送因子との合成に等しい。 -/
lemma pointedRightFamilyTransportIso_counit_square :
    (pointedRightFamilyEvaluationValueIso (K := K) (L := L) a y).postcomp
        (pointedRightFiberComparison L) ≪≫ pointedRightFamilyTransportIso (K := K) (L := L) x y =
      pointedRightFamilyTransportIso (K := K) (L := L) (q ≫ V) y ≪≫
        (functorIsoLiftRight
          (pointedValueFamilySourceUnitIso K q)
          (y ≫ coherentKanRightHomInterval K L)).postcomp E := by
  have h := pointedRightFamilyTransportIso_source_square (K := K) (L := L) a y
  rw [← pointedValueFamilySourceUnitIso_at_right K x] at h
  exact h

end SerrePositivity.InfinityCategories.F2
