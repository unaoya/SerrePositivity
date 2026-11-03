module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalTriangleModelUnitValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalModelUnitTriangle

/-!
概要：a6 の元の区間比較の三角形交換式へ、同じ元の模型三角形の指定値を代入する。
方針：模型比較の実両端を元の単位終点に揃え、照合済みの等式を既存の交換式へ代入する。
規約：三辺・全三角形・選択済み区間比較を保持。使われ方：五因子の整合式との直接比較。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "f₀₁" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 元の選択済み区間比較と元の模型三角形は、同じ最後辺の単位因子の交換式を満たす。 -/
lemma coherentColimitIntervalNativeModel_triangle :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    (coherentColimitLowerTransportFactorIso B d).symm ≪≫
      coherentColimitNativeTriangleActionComparison B d ≪≫
        functorIsoOfEq
          ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
          rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)) ≪≫
        (coherentColimitUpperUnitFactorIso B b).precomp f₀₁ := by
  rw [coherentTotalTriangleNativeModelComparison_eq_unit_triangle]
  exact coherentColimitIntervalModelUnitComparison_triangle B T

end SerrePositivity.InfinityCategories.F2
