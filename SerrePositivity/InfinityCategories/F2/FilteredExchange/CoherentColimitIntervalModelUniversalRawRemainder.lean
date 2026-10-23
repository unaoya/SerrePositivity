module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstUnitTransportValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstUnitModel
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalModelRawLastFactorization
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalModelRawLastTransport

/-!
概要：元の模型三角形式を、普遍二辺三角形の残余と第一辺合成輸送へ厳密に縮約する。
方針：同じ三実頂点で新長辺残余の分解を戻し、元の二面輸送と合成する。
規約：元の三角形・模型単位比較を保持。使われ方：全区間族の指定三角形との最終照合。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "P" => coherentColimitRawConstantFiberProjection B F

/-- 同じ raw 普遍三角形の逆比較の像を、元の長辺模型単位比較の始点から保持する。 -/
def coherentColimitIntervalModelUniversalRawRemainder :=
  vertexIsoOfEq (FunctorIso.postcomp
    ((coherentColimitRawUniversalTriangleComparison B T P).precomp u₀) V).symm
    (coherentColimitRawFirstUnit_source_value_vertex B d) rfl

/-- 元の模型残余は、同じ普遍三角形残余と逆第一辺指定因子の合成そのもの。 -/
lemma coherentColimitIntervalModelRawLastRemainder_eq_universal_first :
    coherentColimitIntervalModelRawLastRemainder B T =
      coherentColimitIntervalModelUniversalRawRemainder B T ≪≫
        coherentColimitRawFirstUnitInverseTransportValue B a b := by
  have h := vertexIso_trans_heq_of_heq
    (coherentColimitIntervalModelUniversalRawRemainder B T)
    (coherentColimitRawFirstUnitInverseTransportValue B a b) _ _
    (coherentColimitRawFirstUnit_source_value_vertex B d).symm rfl
    (coherentColimitRawLastLongValue_target_vertex B a b).symm
    (vertexIsoOfEq_heq _ _ _) (vertexIsoOfEq_heq _ _ _)
  exact eq_of_heq
    ((coherentColimitIntervalModelRawLastRemainder_heq_factorization B T).trans h.symm)

/-- 元の模型三角形式は、普遍三角形残余・第一辺合成輸送・最後辺模型単位の三因子。 -/
lemma coherentColimitIntervalModel_universal_raw_transport [Quasicategory B] :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    coherentColimitIntervalModelUniversalRawRemainder B T ≪≫
      coherentColimitRawFirstUnitTransportValue B a b ≪≫
        (coherentColimitIntervalModelUnitComparison B b).precomp
          (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val := by
  rw [coherentColimitIntervalModel_raw_last_transport,
    coherentColimitIntervalModelRawLastRemainder_eq_universal_first]
  simp only [coherentColimitRawFirstUnitTransportValue, Iso.trans_assoc]

end SerrePositivity.InfinityCategories.F2
