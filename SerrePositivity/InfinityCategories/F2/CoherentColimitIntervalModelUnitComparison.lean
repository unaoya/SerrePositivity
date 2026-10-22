module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalModelReduction
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransportCancellation

/-!
概要：a6 の元の模型正方形を、同じ単位終点での指定比較として保持する。
方針：元の三因子の左辺の終点だけを、同じ単位自然性で表示変更する。
規約：既存の区間比較を再選択しない。使われ方：元の全三角形の単位因子の消去。
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
local notation "a" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)
local notation "n" => Sigma.fst (coherentTotalMapNativeRepresentation F G a)
local notation "S" => coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z
local notation "C" => coherentCoconeIntervalTransportAction F (coherentDiagramTotalCocone F) z
local notation "L" => coherentCoconeIntervalTransportActionIso F (coherentDiagramTotalCocone F) z
local notation "s" => Iso.inv (smallUnstraighteningHomIso F (KanObject.obj (spaceInfinityObject z)))
local notation "u₀" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G a) s)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))

/-- 元の模型正方形の三因子を、同じ元の単位終点で読む指定比較。 -/
def coherentColimitIntervalModelUnitComparison :
    FunctorIso (coconeFiberMap (coherentDiagramTotalCocone F) ≫
      coherentColimitFiberTransport B H ≫ (pointedSpaceFiberValueEquivalence z).hom)
      ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (a ≫ coherentDiagramTotalUnit G)) :=
  vertexIsoOfEq
    (VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S ≪≫
      VertexIso.map (coherentColimitIntervalNativeIso B H) C ≪≫
        ((FunctorIso.app L n).symm ≪≫ u₀)) rfl
    (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B H))

/-- 元の三因子の指定比較は、上側 native 因子を消去した同じ元の三因子に等しい。 -/
lemma coherentColimitIntervalModelUnitComparison_eq_reduced :
    coherentColimitIntervalModelUnitComparison B H =
      (coherentColimitLowerTransportFactorIso B H).symm ≪≫
        coherentColimitNativeTriangleActionComparison B H ≪≫
          coherentColimitUpperUnitFactorIso B H := by
  unfold coherentColimitIntervalModelUnitComparison
  rw [coherentColimitIntervalModel_square_reduced]
  exact functorIsoOfEq_vertex_target_cancel _ (coherentColimitNativeModelTarget_eq_unit B H)

end SerrePositivity.InfinityCategories.F2
