module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalNativeModelTriangle
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueActionToCoherence

/-!
概要：a6 の選択済み区間比較と元の模型三角形の式へ、元の五因子式を直接代入する。
方針：同じ値空間の左辺二因子を元の右辺三因子へ等式で置き換える。
規約：元の三辺・二面・指定 path を保持。使われ方：下側輸送と上側単位の残りの消去。
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

/-- 元の選択済み比較と模型三角形の合成は、元の五因子式の右辺と元の外側二因子に等しい。 -/
lemma coherentColimitIntervalModel_five_factors :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    (coherentColimitLowerTransportFactorIso B d).symm ≪≫
      vertexIsoOfEq (coherentColimitUnitRightValueTo B T)
        (coherentColimitValueProjection_lower_vertex B d)
        (coherentColimitValueProjection_composite_vertex B a b) ≪≫
      (coherentColimitUpperUnitFactorIso B b).precomp f₀₁ := by
  have h := congrArg (fun k => (coherentColimitLowerTransportFactorIso B d).symm ≪≫ k ≪≫
    (coherentColimitUpperUnitFactorIso B b).precomp f₀₁)
    (coherentColimitUnitNativePair_eq_rightValueTo B T)
  exact (coherentColimitIntervalNativeModel_triangle B T).trans
    (by simpa only [Iso.trans_assoc] using h)

end SerrePositivity.InfinityCategories.F2
