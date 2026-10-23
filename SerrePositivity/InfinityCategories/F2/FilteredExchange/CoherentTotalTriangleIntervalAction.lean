module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCoconeIntervalTransportAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalTriangleNativeComparison

/-!
概要：元の全三角形の模型比較を、同じ区間写像空間の普遍作用へ移す。
方針：元の正方形 hu と全 Hom の指定比較の自然性を合成する。
規約：元の模型比較・native 表現を保持。使われ方：完成済み三角形の像との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u}} [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "d₀" => coherentTransformationTotalMap F J (coherentVertexOfHomotopy d)
local notation "c₀" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a) ≫
  coherentTransformationTotalMap G J (coherentVertexOfHomotopy b)
local notation "z" => coherentDiagramTotalVertex J
local notation "S" => Iso.inv (smallUnstraighteningHomIso F (KanObject.obj (spaceInfinityObject z)))
local notation "u₀" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F J d₀) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F J d₀))
local notation "u₁" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F J c₀) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F J c₀))
local notation "e" => coherentCoconeIntervalTransportActionIso F (coherentDiagramTotalCocone F) z
local notation "x" => Sigma.fst (coherentTotalMapNativeRepresentation F J d₀)
local notation "y" => Sigma.fst (coherentTotalMapNativeRepresentation F J c₀)
local notation "A" => pinchedHomLeftToIntervalMappingSpace
  (JoinCocone.vertex (coherentDiagramTotalCocone F)) z ≫
    coherentCoconeIntervalTransportAction F (coherentDiagramTotalCocone F) z

/-- 同じ元の模型三角形比較は、普遍作用の同じ二成分の正方形を満たす。 -/
lemma coherentTotalTriangleIntervalAction_square :
    ((FunctorIso.app e x).symm ≪≫ u₀) ≪≫ coherentTotalTriangleNativeModelComparison T =
      VertexIso.map (coherentTotalTriangleNativeComparison T) A ≪≫
        ((FunctorIso.app e y).symm ≪≫ u₁) := by
  exact functorIso_app_vertexIso_comparison_naturality e
    (coherentTotalTriangleNativeComparison T) u₀ u₁
    (coherentTotalTriangleNativeModelComparison T) (coherentTotalTriangleNativeComparison_square T)

/-- 同じ模型比較と元の二成分の逆も、同じ普遍作用の像により整合する。 -/
lemma coherentTotalTriangleIntervalAction_inverse_square :
    coherentTotalTriangleNativeModelComparison T ≪≫ ((FunctorIso.app e y).symm ≪≫ u₁).symm =
      ((FunctorIso.app e x).symm ≪≫ u₀).symm ≪≫
        VertexIso.map (coherentTotalTriangleNativeComparison T) A := by
  exact functorIso_app_vertexIso_comparison_inverse_naturality e
    (coherentTotalTriangleNativeComparison T) u₀ u₁
    (coherentTotalTriangleNativeModelComparison T) (coherentTotalTriangleNativeComparison_square T)

end SerrePositivity.InfinityCategories.F2
