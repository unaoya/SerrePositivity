module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawTransportModelUnitRecovery

/-!
概要：元の具体的 Kan 射への模型比較から、第一辺合成比較の固定値での指定像を構成する。
方針：同じ上側単位逆因子を続け、元の二実端点へ戻す。
規約：模型比較と単位を保持。使われ方：元の第一辺合成比較の fiber 側への反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 同じ元の模型比較へ上側単位逆因子を続けると、元の第一辺合成比較の指定値。 -/
lemma coherentColimitRawTransportModelUnitComparison_cancel_upper :
    coherentColimitRawTransportModelUnitComparison B a ≪≫
      (coherentColimitUpperUnitFactorIso B a).symm =
    coherentColimitRawFirstUnitValueComparison B a := by
  rw [coherentColimitRawTransportModelUnitComparison_eq_model,
    ← coherentColimitRawFirstUnitValueComparison_model]
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- 元の具体的 Kan 射への模型比較から構成した、同じ実両端間の第一辺指定値。 -/
def coherentColimitModelFirstUnitValueIso :
    FunctorIso ((u₀ ≫ (P ≫ coherentColimitRawFiberTransport B a)) ≫ V)
      ((coherentColimitRawUpperCompositeAction B a ≫ PG) ≫ V) :=
  vertexIsoOfEq (coherentColimitRawTransportModelUnitComparison B a ≪≫
    (coherentColimitUpperUnitFactorIso B a).symm)
    (coherentColimitRawFirstUnit_source_value_vertex B a).symm
    (congrArg functorVertex (coherentColimitRawUnitFiberValue_target_map B a)).symm

/-- 同じ元の模型比較から構成した値は、元の raw 第一辺合成比較の指定像そのもの。 -/
lemma coherentColimitModelFirstUnitValueIso_eq_raw :
    coherentColimitModelFirstUnitValueIso B a =
      (coherentColimitRawFirstUnitComparison B a).postcomp V := by
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    ((heq_of_eq (coherentColimitRawTransportModelUnitComparison_cancel_upper B a)).trans
      (vertexIsoOfEq_heq _ _ _)))

end SerrePositivity.InfinityCategories.F2
