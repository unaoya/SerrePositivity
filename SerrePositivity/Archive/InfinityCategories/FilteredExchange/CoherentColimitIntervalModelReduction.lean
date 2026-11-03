module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalModelSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitNativeModelEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperNativeCancellation

/-!
概要：a6 の選択済み模型正方形から、同じ上側 native 因子を厳密に消去する。
方針：元の実両端を揃え、指定共役式の native 因子と同じ模型成分を相殺する。
規約：元の選択済み比較を保持。使われ方：五因子の三角形整合式への代入。
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
local notation "E" => vertexIsoOfEq (VertexIso.map (coherentColimitFiberTransportIso B H) S) rfl
  (coherentColimitIntervalNativeActionSource_eq B H)
local notation "R" => functorIsoOfEq
  (Iso.symm (coherentColimitLowerTransportFactorIso B H) ≪≫
    coherentColimitNativeTriangleActionComparison B H ≪≫ coherentColimitUpperUnitFactorIso B H)
  rfl (Eq.symm (coherentColimitNativeModelTarget_eq_unit B H))

/-- 元の模型正方形の右辺では、同じ native 成分が上側 native 因子を値まで相殺する。 -/
lemma coherentColimitIntervalModel_cancel_upperNative :
    E ≪≫ coherentTotalMapNativeActionComponentsIso F G a = R := by
  have he := (coherentColimitIntervalModelFiber_heq_conjugate B H).trans
    (heq_of_eq (coherentColimitActionComparison_eq_conjugate B H).symm)
  have h := vertexIso_trans_heq_of_heq E (coherentTotalMapNativeActionComponentsIso F G a)
    ((coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H)
    (coherentColimitUpperNativeFactorIso B H).symm rfl
    (coherentColimitNativeModelSource_eq_action B H)
    (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B H)) he
    (coherentColimitUpperNativeFactorIso_symm_heq_components B H).symm
  exact eq_of_heq ((h.trans
    (heq_of_eq (coherentColimitActionComparison_cancel_upperNative B H))).trans
      (functorIsoOfEq_heq _ _ _).symm)

/-- a6 の元の区間比較の模型正方形は、上側 native 因子を消した同じ指定値に等しい。 -/
lemma coherentColimitIntervalModel_square_reduced :
    VertexIso.map (coherentColimitIntervalCompletedTransportIso B H) S ≪≫
      VertexIso.map (coherentColimitIntervalNativeIso B H) C ≪≫
        ((FunctorIso.app L n).symm ≪≫ u₀) = R := by
  exact (coherentColimitIntervalModel_square B H).trans
    (coherentColimitIntervalModel_cancel_upperNative B H)

end SerrePositivity.InfinityCategories.F2
