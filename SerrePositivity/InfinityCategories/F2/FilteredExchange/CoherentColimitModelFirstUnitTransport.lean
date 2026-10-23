module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitModelFirstUnitComparison
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalModelUniversalRawRemainder

/-!
概要：元の第一辺合成輸送を、a6 の元の模型第一辺比較の同じ最後辺輸送へ値まで同定する。
方針：同じ raw fiber での指定値の一致を輸送し、実始点・終点だけを戻す。
規約：元の模型比較と三角形の全因子を保持。使われ方：普遍三角形残余との最終照合。
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

/-- 元の模型第一辺比較を同じ最後辺と値へ写し、元の模型三角形式の実両端で読む。 -/
def coherentColimitModelFirstUnitTransportValue :=
  vertexIsoOfEq (((coherentColimitModelFirstUnitComparison B a).postcomp t).postcomp V)
    (congrArg (fun r => functorVertex (r ≫ V))
      (Category.assoc u₀ (coherentColimitRawConstantFiberProjection B F ≫
        coherentColimitRawFiberTransport B a) t))
    (congrArg functorVertex (coherentColimitRawUnitFiberTransport_raw_target_map B a b))

/-- 元の模型第一辺比較の同じ輸送は、元の二因子を合成した指定輸送比較そのもの。 -/
lemma coherentColimitModelFirstUnitTransportValue_eq_raw :
    coherentColimitModelFirstUnitTransportValue B a b =
      coherentColimitRawFirstUnitTransportValue B a b := by
  have hm := congrArg (fun e => (FunctorIso.postcomp e t).postcomp V)
    (coherentColimitModelFirstUnitComparison_eq_raw B a)
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    ((heq_of_eq hm).trans (coherentColimitRawFirstUnitTransportValue_heq_raw B a b).symm))

/-- 元の模型三角形式を、元の模型第一辺比較の同じ最後辺輸送で厳密に表示する。 -/
lemma coherentColimitIntervalModel_model_first_transport [Quasicategory B]
    {d : SSet.Homotopy F J} (T : FunctorCompositionTriangle a b d) :
    coherentColimitIntervalModelUnitComparison B d ≪≫
      vertexIsoOfEq (coherentTotalTriangleNativeModelComparison T)
        (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B d))
        (congrArg functorVertex (coherentTotalTriangleNativeModelTarget_eq_unit a b)) =
    coherentColimitIntervalModelUniversalRawRemainder B T ≪≫
      coherentColimitModelFirstUnitTransportValue B a b ≪≫
        (coherentColimitIntervalModelUnitComparison B b).precomp
          (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val := by
  rw [coherentColimitModelFirstUnitTransportValue_eq_raw]
  exact coherentColimitIntervalModel_universal_raw_transport B T

end SerrePositivity.InfinityCategories.F2
