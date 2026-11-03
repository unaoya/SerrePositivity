module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalModelRawLastCancellation

/-!
概要：元の a6 模型三角形式を、新長辺残余と元の raw 二面輸送の同じ三因子へ縮約する。
方針：元の三角形式へ実二因子の消去式をそのまま代入する。
規約：元の三辺・模型比較・指定値を保持。使われ方：同じ全区間族の三角形整合の反映。
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
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 元の a6 模型三角形式は、同じ新長辺残余・二面輸送・最後辺模型単位の三因子になる。 -/
lemma coherentColimitIntervalModel_raw_last_transport :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    coherentColimitIntervalModelRawLastRemainder B T ≪≫
      coherentColimitRawUnitFiberTransportValueTo B a b ≪≫
        (coherentColimitIntervalModelUnitComparison B b).precomp f := by
  rw [coherentColimitIntervalModel_fiber_transport]
  rw [← Iso.trans_assoc (coherentColimitIntervalModelTransportRemainder B T)]
  rw [coherentColimitIntervalModel_raw_last_prefix_cancel]

end SerrePositivity.InfinityCategories.F2
