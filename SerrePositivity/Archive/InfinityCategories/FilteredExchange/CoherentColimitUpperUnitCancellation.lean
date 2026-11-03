module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperUnitTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoExchangeCancellation

/-!
概要：元の全三角形の値の比較から、既存の上側単位因子を逆との合成で消去する。
方針：同じ指定因子の交換式に同じ二つの逆を合成する。
規約：元の三角形・指定因子を保持。使われ方：値の整合式の上側因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "f₀₁" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 既存の長辺の単位因子を消去すると、同じ全三角形比較と最後の辺の単位因子の逆になる。 -/
lemma coherentColimitUpperUnitFactor_triangle_cancel :
    (coherentColimitUpperUnitFactorIso B c).symm ≪≫
        functorIsoOfEq
          ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
          rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)) =
      functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
          (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
          (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)) ≪≫
        ((coherentColimitUpperUnitFactorIso B b).precomp f₀₁).symm :=
  iso_inverse_exchange_of_square
    (functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
      rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)))
    ((coherentColimitUpperUnitFactorIso B b).precomp f₀₁)
    (coherentColimitUpperUnitFactorIso B c)
    (functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
      (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
      (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)))
    (coherentColimitUpperUnitFactor_triangle_exchange B T)

end SerrePositivity.InfinityCategories.F2
