module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstUnitComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUnitFiberTransportValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawLastLongValueEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoInversePrePostValue

/-!
概要：元の逆第一辺因子と二面輸送を、同じ raw 第一辺合成比較の最後辺輸送へ束ねる。
方針：実三頂点と元の指定値を揃え、前後合成の交換と合成の保存を使う。
規約：元の模型式の二因子を保持。使われ方：普遍三角形の残余だけを残す模型三角形式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "t" => coherentColimitRawFiberTransport B b
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)

/-- 元の逆第一辺因子の最後辺輸送を、元の二面輸送の同じ実始点まで保持する。 -/
def coherentColimitRawFirstUnitInverseTransportValue :=
  vertexIsoOfEq (FunctorIso.postcomp
    (((coherentColimitConstantTransportRawPointIso B a).postcomp t).precomp u₀) V).symm rfl
    (coherentColimitRawLastLongValue_target_vertex B a b)

/-- 同じ元の逆因子は、元の raw 逆第一辺比較の最後辺輸送の指定値に一致する。 -/
lemma coherentColimitRawFirstUnitInverseTransportValue_heq_raw :
    HEq (coherentColimitRawFirstUnitInverseTransportValue B a b)
      (((coherentColimitRawFirstUnitInversePoint B a).postcomp t).postcomp V) := by
  exact (vertexIsoOfEq_heq _ _ _).trans
    (functorIsoOfEq_inverse_pre_post_value_heq
      (coherentColimitConstantTransportRawPointIso B a) u₀
      (coherentColimitRawFirstUnit_middle_map B a) t V).symm

/-- 元の逆第一辺因子と元の二面輸送を、同じ実中間点で合成した指定比較。 -/
def coherentColimitRawFirstUnitTransportValue :=
  coherentColimitRawFirstUnitInverseTransportValue B a b ≪≫
    coherentColimitRawUnitFiberTransportValueTo B a b

/-- 元の二因子の合成は、同じ raw 第一辺合成比較の最後辺輸送と同じ値射の像。 -/
lemma coherentColimitRawFirstUnitTransportValue_heq_raw :
    HEq (coherentColimitRawFirstUnitTransportValue B a b)
      (((coherentColimitRawFirstUnitComparison B a).postcomp t).postcomp V) := by
  have h := vertexIso_trans_heq_of_heq
    (coherentColimitRawFirstUnitInverseTransportValue B a b)
    (coherentColimitRawUnitFiberTransportValueTo B a b)
    (((coherentColimitRawFirstUnitInversePoint B a).postcomp t).postcomp V)
    (((coherentColimitRawUnitFiberComparison B a).postcomp t).postcomp V)
    (congrArg (fun r => functorVertex (r ≫ V))
      (Category.assoc u₀ (coherentColimitRawConstantFiberProjection B F ≫
        coherentColimitRawFiberTransport B a) t)).symm
    (congrArg functorVertex (coherentColimitRawUnitFiberTransport_raw_source_map B a b)).symm
    (congrArg functorVertex (coherentColimitRawUnitFiberTransport_raw_target_map B a b)).symm
    (coherentColimitRawFirstUnitInverseTransportValue_heq_raw B a b)
    (coherentColimitRawUnitFiberTransportValueTo_heq_raw B a b)
  exact h.trans (heq_of_eq (functorIso_postcomp_trans_twice
    (coherentColimitRawFirstUnitInversePoint B a)
    (coherentColimitRawUnitFiberComparison B a) t V)).symm

end SerrePositivity.InfinityCategories.F2
