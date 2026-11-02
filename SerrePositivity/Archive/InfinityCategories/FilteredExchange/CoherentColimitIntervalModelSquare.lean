module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalNativeActionSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeIntervalComponents
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoSquareRightPasting
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFiberTransportImage

/-!
概要：a6 の元の区間比較を、全 Hom の元の模型比較と同じ成分の正方形へ接続する。
方針：共有する普遍輸送成分を同じ native 成分の回収式で消去する。
規約：a6 の選択済み比較を保持。使われ方：完成済み三角形と模型三角形の像の照合。
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

/-- 元の a6 比較の同じ像と既存 native 因子は、同じ模型比較の正方形で結ばれる。 -/
lemma coherentColimitIntervalModel_square :
    VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S ≪≫
      VertexIso.map (coherentColimitIntervalNativeIso B H) C ≪≫
        ((FunctorIso.app L n).symm ≪≫ u₀) =
    vertexIsoOfEq (VertexIso.map (coherentColimitFiberTransportIso B H) S) rfl
      (coherentColimitIntervalNativeActionSource_eq B H) ≪≫
        coherentTotalMapNativeActionComponentsIso F G a := by
  exact iso_square_finish_right _ _ _ _ _ _
    (coherentColimitIntervalNativeAction_universal_square B H)
    (coherentTotalMapNativeIntervalComponents_cancel F G a)

/-- 正方形の同じ fiber 因子は、元の上下二面の指定共役そのものへ戻る。 -/
lemma coherentColimitIntervalModelFiber_heq_conjugate :
    HEq (vertexIsoOfEq (VertexIso.map (coherentColimitFiberTransportIso B H) S) rfl
      (coherentColimitIntervalNativeActionSource_eq B H))
      ((coherentColimitLowerTransportFactorIso B H).symm ≪≫
        coherentColimitNativeTriangleActionComparison B H ≪≫
          coherentColimitUpperTransportFactorIso B H) := by
  exact (vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitFiberTransportIso_action_heq_conjugate B H)

end SerrePositivity.InfinityCategories.F2
