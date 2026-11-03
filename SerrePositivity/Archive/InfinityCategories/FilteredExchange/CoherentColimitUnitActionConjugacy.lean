module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerTransportFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperTransportFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTriangleAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：a6 への上下作用比較の合成を、元の二面比較と指定外側因子による共役で表す。
方針：元の上下作用の因子分解を代入し、同じ三角形比較の逆と合成を保持する。
規約：元の二面・対角・輸送因子を保持。使われ方：指定 path の比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "z" => coherentDiagramTotalVertex G

/-- 元の native 単位表現を保つ、同じ下面の逆と上面の指定比較合成。 -/
def coherentColimitNativeTriangleActionComparison :
    FunctorIso (coherentColimitLowerCompositeAction B H)
      (coherentColimitUpperCompositeAction B H) :=
  (coherentColimitLowerTriangleActionIso B H).symm ≪≫ coherentColimitUpperTriangleActionIso B H

/-- 既存の a6 への上下作用比較の合成は、同じ二面比較の指定外側因子による共役。 -/
lemma coherentColimitActionComparison_eq_conjugate :
    (coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H =
      (coherentColimitLowerTransportFactorIso B H).symm ≪≫
        coherentColimitNativeTriangleActionComparison B H ≪≫
          coherentColimitUpperTransportFactorIso B H := by
  rw [coherentColimitLowerActionIso_eq_triangle_transport,
    coherentColimitUpperActionIso_eq_triangle_transport]
  simp only [coherentColimitNativeTriangleActionComparison, Iso.trans_symm, Iso.trans_assoc]

/-- 共役の中央の二面比較は、元の全族から値へ戻した二面比較と同じ指定値。 -/
lemma coherentColimitNativeTriangleActionComparison_heq_original :
    HEq (coherentColimitNativeTriangleActionComparison B H)
      (coherentColimitUnitTriangleActionComparison B H) := by
  have hu := (coherentColimitUpperRelativeComparison_map_heq_action B H).symm.trans
    (functorTriangleRelativeComparison_map_constantTarget
      (coherentColimitNativeUnitFunctorTriangle B H))
  have hc := congrArg (fun y => functorVertex
    (((leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val ≫
      (leftUnstraighteningMappingVertexMap G (SSet.const z) y).val) ≫
        (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z ≫
          (pointedSpaceFiberValueEquivalence z).hom)))
    (coherentVertexOfHomotopy_of_vertex (coherentNativeUnitRepresentation G).1).symm
  unfold coherentColimitNativeTriangleActionComparison coherentColimitUnitTriangleActionComparison
  exact vertexIso_trans_heq_of_heq _ _ _ _ rfl rfl hc HEq.rfl hu

end SerrePositivity.InfinityCategories.F2
