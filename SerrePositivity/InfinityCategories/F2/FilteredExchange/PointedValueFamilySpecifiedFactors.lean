module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueFamilyTransport

/-!
概要：元の値比較の指定単位・余単位と三つの指定因子を、そのまま明示的に保持する。
方針：既存の定義と同じ実端点の表示変更を名前にし、元の合成を直接回収する。
規約：比較を再選択しない。使われ方：余単位正方形から元の値比較への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (K L : KanObject.{u}) {P : SSet.{u + 1}}
local notation "V₀" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K))
local notation "V₁" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "E" => FiberTransportFamily.endpoint (parametrizedFiberTransportFamily
  pointedSpaceProjection (spaceInfinityVertex K) (spaceInfinityVertex L))

/-- 元の全値比較の始点に使う、同じ指定単位の実端点表示。 -/
def pointedValueFamilySourceUnitIso
    (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    FunctorIso ((x ≫ V₀) ≫ pointedRightFiberComparison K) x := by
  simpa only [pointedValueRightComparison_standard, Category.assoc, Category.comp_id] using
    (pointedValueRightComparison_unitIso (spaceInfinityVertex K)).precomp x

/-- 元の全値比較の終点に使う、同じ指定余単位の実端点表示。 -/
def pointedValueFamilyTargetCounitIso
    (v : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj L.obj) :
    FunctorIso ((v ≫ pointedRightFiberComparison L) ≫ V₁) v := by
  simpa only [pointedValueRightComparison_standard, Category.assoc, Category.comp_id] using
    (pointedValueRightComparison_counitIso (spaceInfinityVertex L)).precomp v

/-- 元の全値比較は、同じ指定余単位・全右 Hom 比較・始点単位輸送の三因子そのもの。 -/
lemma pointedValueFamilyTransportIso_factorization
    (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) :
    pointedValueFamilyTransportIso x y =
      (pointedValueFamilyTargetCounitIso L (pointedRightFamilyEvaluation (x ≫ V₀) y)).symm ≪≫
        (pointedRightFamilyTransportIso (x ≫ V₀) y).postcomp V₁ ≪≫
        ((functorIsoLiftRight (pointedValueFamilySourceUnitIso K x)
          (y ≫ coherentKanRightHomInterval K L)).postcomp E).postcomp V₁ := rfl

end SerrePositivity.InfinityCategories.F2
