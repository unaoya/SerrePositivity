module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalModelUnitComparison
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUpperUnitTriangle

/-!
概要：a6 の選択済み模型比較を、元の全三角形に沿う単位比較の交換式へ接続する。
方針：同じ元の三因子への還元式を代入し、既存の長辺・最後辺の単位因子を交換する。
規約：元の全三角形と区間比較を保持。使われ方：五因子の整合式の上側因子の消去。
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

/-- 元の長辺の模型比較と単位後の全三角形比較は、同じ最後辺の単位因子と交換する。 -/
lemma coherentColimitIntervalModelUnitComparison_triangle :
    coherentColimitIntervalModelUnitComparison B c ≪≫
      functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
        (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
        (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)) =
    (coherentColimitLowerTransportFactorIso B c).symm ≪≫
      coherentColimitNativeTriangleActionComparison B c ≪≫
        functorIsoOfEq
          ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
          rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)) ≪≫
        (coherentColimitUpperUnitFactorIso B b).precomp f₀₁ := by
  have h := congrArg (fun e =>
    ((coherentColimitLowerTransportFactorIso B c).symm ≪≫
      coherentColimitNativeTriangleActionComparison B c) ≪≫ e)
    (coherentColimitUpperUnitFactor_triangle_exchange B T).symm
  simpa only [coherentColimitIntervalModelUnitComparison_eq_reduced, Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2
